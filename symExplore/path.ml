open Language
open Zzdatatype.Datatype

module type CH = sig
  type ch

  val layout : ch -> string
  val layout_op : ch -> string
end

module type STATE = sig
  type state

  val layout : state -> string
end

module MakePath (S : STATE) (Ch : CH) = struct
  open S
  open Ch

  type path =
    | PathEmpty of state
    | PathCons of { prefix : path; ch : ch; dest : state }

  let append prefix (ch, dest) = PathCons { prefix; ch; dest }

  let to_ch_list =
    let rec aux rev = function
      | PathEmpty _ -> List.rev rev
      | PathCons { prefix; ch; _ } -> aux (ch :: rev) prefix
    in
    aux []

  let to_ch_op_list p = List.map layout_op @@ to_ch_list p
  let length l = List.length @@ to_ch_list l
  let end_point = function PathEmpty s -> s | PathCons { dest; _ } -> dest

  let rec start_point = function
    | PathEmpty s -> s
    | PathCons { prefix; _ } -> start_point prefix

  let layout_ layout_ch layout_state =
    let rec aux = function
      | PathEmpty s -> layout_state s
      | PathCons { prefix; ch; dest } ->
          spf "%s =>> %s =>> %s" (aux prefix) (layout_ch ch) (layout_state dest)
    in
    aux

  let layout = layout_ Ch.layout S.layout
  let layout_paths = List.split_by "\n" layout
  let layout_op = (List.split_by " =>> " layout_op)#.List.rev#.to_ch_list

  (* let layout_op = layout_ (_get_sevent_name __FILE__ __LINE__) string_of_int *)
  let layout_paths_op = List.split_by "\n" layout_op

  let rec front_destruct_opt = function
    | PathEmpty _ -> None
    | PathCons { prefix = PathEmpty start; ch; dest } ->
        Some ((start, ch, dest), PathEmpty dest)
    | PathCons { prefix; ch; dest } -> (
        match front_destruct_opt prefix with
        | None -> _die [%here]
        | Some (tran, prefix) -> Some (tran, PathCons { prefix; ch; dest }))
end

module EventOp = struct
  type ch = string

  let layout op = op
  let layout_op ch = ch
end

module Event = struct
  type ch = Nt.t sevent

  let layout = layout_se
  let layout_op ch = _get_sevent_name __FILE__ __LINE__ ch
end

module MultiEvent = struct
  type ch = {
    op : string;
    vs : (Nt.t, string) typed list;
    phis : Nt.t prop list;
  }

  let layout (_ : ch) = _die [%here]
  let layout_op ch = ch.op

  let ch_to_chs { op; vs; phis } =
    List.map (fun phi -> EffEvent { op; vs; phi }) phis

  let check (sat_solver : Nt.t prop -> bool) world
      (world_props : Nt.t prop list) (ch : ch) =
    let body =
      smart_and
      @@ List.map (fun (p1, p2) -> Implies (p1, p2))
      @@ List.combine world_props ch.phis
    in
    let rec aux world =
      match world with
      | WState -> body
      | WMap { qv; world; _ } -> Forall { qv; body = aux world }
      | WSingle { qv; world; _ } -> Exists { qv; body = aux world }
    in
    let query = aux world in
    sat_solver query
end

module State = struct
  type state = int

  let layout = string_of_int
end

module MultiState = struct
  type state = int list

  let layout = IntList.to_string
end

module Path = MakePath (State) (Event)
module MPath = MakePath (MultiState) (MultiEvent)
module MOpPath = MakePath (MultiState) (EventOp)

let to_paths =
  let open MPath in
  let rec aux = function
    | PathEmpty s -> List.map (fun s -> Path.PathEmpty s) s
    | PathCons { prefix; ch; dest } ->
        let prefix = aux prefix in
        let ch = MultiEvent.ch_to_chs ch in
        List.map (fun (prefix, (ch, dest)) ->
            Path.PathCons { prefix; ch; dest })
        @@ List.combine prefix (List.combine ch dest)
  in
  aux
