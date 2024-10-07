include Common

(* include Constructor_declaration *)
(* include Item *)
(* include Inst *)
include Zutils
include Typectx

(* include Pmachine *)
(* include Wrapper *)
include Myconfig
open AutomataLibrary

type srl = (Nt.nt, Nt.nt sevent) regex [@@deriving show, eq, ord]

let default_v = "v"

type cty = { nt : Nt.nt; phi : Nt.nt prop } [@@deriving show, eq, ord]

type 'r haft =
  | RtyBase of cty
  | RtyHAF of { history : 'r; adding : 'r; future : 'r }
  | RtyHAParallel of {
      history : 'r;
      adding_se : Nt.nt sevent;
      parallel : Nt.nt sevent list;
    }
  | RtyArr of { arg : string; argcty : cty; retrty : 'r haft }
  | RtyInter of 'r haft * 'r haft
[@@deriving show, eq, ord]

type value = VVar of (Nt.nt, string) typed | VConst of constant
[@@deriving show, eq, ord]

type term =
  | CVal of (Nt.nt, value) typed
  | CLetE of {
      rhs : (Nt.nt, term) typed;
      lhs : (Nt.nt, string) typed list;
      body : (Nt.nt, term) typed;
    }
  | CAppOp of { op : (Nt.nt, op) typed; args : (Nt.nt, value) typed list }
  | CObs of { op : (Nt.nt, string) typed }
  | CGen of { op : (Nt.nt, string) typed; args : (Nt.nt, value) typed list }
  | CUnion of term list
  | CAssume of value
[@@deriving show, eq, ord]

type syn_goal = { qvs : (Nt.nt, string) typed list; prop : srl }
[@@deriving show, eq, ord]

type 'r item =
  | PrimDecl of { name : string; nt : Nt.nt }
  | MsgNtDecl of { generative : bool; name : string; nt : Nt.nt }
  | MsgDecl of { name : string; haft : 'r haft }
  | SynGoal of syn_goal
[@@deriving show, eq, ord]

type syn_env = {
  event_rtyctx : SFA.raw_regex haft ctx;
  gen_ctx : bool ctx;
  event_tyctx : (Nt.nt, string) typed list ctx;
  tyctx : Nt.t ctx;
  goal : syn_goal option;
}

let mk_inter_type l =
  match l with
  | [] -> _die [%here]
  | h :: t -> List.fold_left (fun x y -> RtyInter (x, y)) h t

let erase_cty { nt; _ } = nt

let rec erase_rty = function
  | RtyBase cty -> erase_cty cty
  | RtyHAF _ | RtyHAParallel _ -> Nt.Ty_unit
  | RtyArr { argcty; retrty; _ } ->
      Nt.mk_arr (erase_cty argcty) (erase_rty retrty)
  | RtyInter (t1, t2) ->
      let t1, t2 = map2 erase_rty (t1, t2) in
      let t = Nt._type_unify [%here] t1 t2 in
      t

let mk_haf (history, adding, future) = RtyHAF { history; adding; future }

let rec is_singleton_haft = function
  | RtyBase _ | RtyHAF _ | RtyHAParallel _ -> true
  | RtyArr { retrty; _ } -> is_singleton_haft retrty
  | RtyInter _ -> false

let rec haft_to_triple = function
  | RtyInter (t1, t2) -> haft_to_triple t1 @ haft_to_triple t2
  | _ as r ->
      if is_singleton_haft r then [ r ]
      else _die_with [%here] "not a well-formed HAF type"

let qv_to_cqv { x; ty } = { x; ty = { nt = ty; phi = mk_true } }

let rctx_to_prefix rctx =
  List.fold_right
    (fun x (qvs, prop) ->
      let x' = x.x #: x.ty.nt in
      let phi = subst_prop_instance default_v (AVar x') x.ty.phi in
      (x' :: qvs, smart_add_to phi prop))
    (ctx_to_list rctx) ([], mk_true)

let destruct_haft loc r =
  let rec aux r =
    match r with
    | RtyInter _ -> _die loc
    | RtyBase _ | RtyHAF _ | RtyHAParallel _ -> ([], r)
    | RtyArr { argcty; retrty; arg } ->
        let args, t = aux retrty in
        ((arg #: argcty) :: args, t)
  in
  aux r

let destruct_hap loc = function
  | RtyHAParallel { history; adding_se; parallel } ->
      (history, adding_se, parallel)
  | _ -> _die loc

(* module type AST = sig *)
(*   type 'a ast [@@deriving sexp, show, eq, ord] *)

(*   val fv : 'a ast -> string *)
(*   val subst : 'a ast -> string -> 'a ast -> 'a ast *)
(*   val subst_id : 'a ast -> string -> string -> 'a ast *)
(* end *)
