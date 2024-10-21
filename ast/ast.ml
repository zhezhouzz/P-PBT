include Common
open Sexplib.Std

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
  | RtyGArr of { arg : string; argnt : Nt.nt; retrty : 'r haft }
  | RtyArr of { arg : string; argcty : cty; retrty : 'r haft }
  | RtyInter of 'r haft * 'r haft
[@@deriving show, eq, ord]

type value = VVar of (Nt.nt, string) typed | VConst of constant
[@@deriving sexp, show, eq, ord]

type trace_elem = string * constant list [@@deriving show, eq, ord]
type trace = trace_elem list [@@deriving show, eq, ord]

type term =
  | CVal of (Nt.nt, value) typed
  | CLetE of {
      rhs : (Nt.nt, term) typed;
      lhs : (Nt.nt, string) typed list;
      body : (Nt.nt, term) typed;
    }
  | CAppOp of { op : (Nt.nt, string) typed; args : (Nt.nt, value) typed list }
  | CObs of { op : (Nt.nt, string) typed; prop : Nt.nt prop }
  | CGen of { op : (Nt.nt, string) typed; args : (Nt.nt, value) typed list }
  | CUnion of term list
  | CAssert of value
  | CAssume of (Nt.nt list * Nt.nt prop)
  | CAssertP of Nt.nt prop
[@@deriving sexp, show, eq, ord]

type syn_goal = { qvs : (Nt.nt, string) typed list; prop : srl }
[@@deriving show, eq, ord]

type 'r item =
  | PrimDecl of { name : string; nt : Nt.nt }
  | MsgNtDecl of {
      generative : bool;
      name : string;
      nt : Nt.nt;
      recvable : bool;
    }
  | MsgDecl of { name : string; haft : 'r haft }
  | SynGoal of syn_goal
[@@deriving show, eq, ord]

type plan_elem =
  | PlanAct of { op : string; args : (Nt.nt, string) typed list }
  | PlanActBuffer of {
      op : string;
      args : (Nt.nt, string) typed list;
      phi : Nt.nt prop;
    }
  | PlanSe of Nt.nt sevent
  | PlanStarInv of SFA.CharSet.t
  | PlanStar of SFA.CharSet.t raw_regex
[@@deriving eq, ord]

type plan = plan_elem list

type syn_env = {
  event_rtyctx : SFA.raw_regex haft ctx;
  gen_ctx : bool ctx;
  recvable_ctx : bool ctx;
  event_tyctx : (Nt.nt, string) typed list ctx;
  tyctx : Nt.t ctx;
  goal : syn_goal option;
}

let mk_value_tt = (VConst U) #: Nt.Ty_unit
let mk_term_tt = CVal mk_value_tt

let term_to_nt = function
  | CVal v -> v.ty
  | CLetE { body; _ } -> body.ty
  | CAppOp { op; _ } -> snd @@ Nt.destruct_arr_tp op.ty
  | CObs { op; _ } -> snd @@ Nt.destruct_arr_tp op.ty
  | CGen _ | CUnion _ | CAssert _ | CAssertP _ -> Ty_unit
  (* | CRandom nt -> nt *)
  | CAssume (nts, _) -> Nt.Ty_tuple nts

let mk_let lhs rhs body =
  let ty =
    match lhs with
    | [] -> Nt.Ty_unit
    | [ x ] -> x.ty
    | _ -> Nt.Ty_tuple (List.map _get_ty lhs)
  in
  CLetE { lhs; rhs = rhs #: ty; body = body #: (term_to_nt body) }

let term_concat term body =
  CLetE { lhs = []; rhs = term #: Nt.Ty_unit; body = body #: Nt.Ty_unit }

let mk_inter_type l =
  match l with
  | [] -> _die [%here]
  | h :: t -> List.fold_left (fun x y -> RtyInter (x, y)) h t

let erase_cty { nt; _ } = nt

let rec erase_rty = function
  | RtyBase cty -> erase_cty cty
  | RtyHAF _ | RtyHAParallel _ -> Nt.Ty_unit
  | RtyGArr { retrty; _ } -> erase_rty retrty
  | RtyArr { argcty; retrty; _ } ->
      Nt.mk_arr (erase_cty argcty) (erase_rty retrty)
  | RtyInter (t1, t2) ->
      let t1, t2 = map2 erase_rty (t1, t2) in
      let t = Nt._type_unify [%here] t1 t2 in
      t

let mk_haf (history, adding, future) = RtyHAF { history; adding; future }

let rec is_singleton_haft = function
  | RtyBase _ | RtyHAF _ | RtyHAParallel _ -> true
  | RtyGArr { retrty; _ } | RtyArr { retrty; _ } -> is_singleton_haft retrty
  | RtyInter _ -> false

let rec haft_to_triple = function
  | RtyInter (t1, t2) -> haft_to_triple t1 @ haft_to_triple t2
  | _ as r ->
      if is_singleton_haft r then [ r ]
      else _die_with [%here] "not a well-formed HAF type"

let qv_to_cqv { x; ty } = { x; ty = { nt = ty; phi = mk_true } }
let value_to_nt = function VVar x -> x.ty | VConst c -> constant_to_nt c
let value_to_tvalue v = v #: (value_to_nt v)
let value_to_lit = function VVar x -> AVar x | VConst c -> AC c

let mk_term_gen env op args e =
  let ty = _get_force [%here] env.event_tyctx op in
  term_concat
    (CGen { op = op #: (Nt.Ty_record ty); args = List.map value_to_tvalue args })
    e

let mk_term_assertP prop e =
  if is_true prop then e else term_concat (CAssertP prop) e

let mk_term_assume args prop e =
  match args with
  | [] -> if is_true prop then e else _die_with [%here] "not true"
  | _ -> mk_let args (CAssume (List.map _get_ty args, prop)) e

let mk_term_obs env op args prop e =
  let ty = _get_force [%here] env.event_tyctx op in
  mk_let args (CObs { op = op #: (Nt.Ty_record ty); prop }) e

let rctx_to_prefix rctx =
  List.fold_right
    (fun x (qvs, prop) ->
      let x' = x.x #: x.ty.nt in
      let phi = subst_prop_instance default_v (AVar x') x.ty.phi in
      (x' :: qvs, smart_add_to phi prop))
    (ctx_to_list rctx) ([], mk_true)

let destruct_haft_inner loc r =
  let rec aux r =
    match r with
    | RtyInter _ -> _die loc
    | RtyGArr _ -> _die_with loc "never"
    | RtyBase _ | RtyHAF _ | RtyHAParallel _ -> ([], r)
    | RtyArr { argcty; retrty; arg } ->
        let args, t = aux retrty in
        ((arg #: argcty) :: args, t)
  in
  aux r

let destruct_haft loc r =
  let rec aux r =
    match r with
    | RtyInter _ -> _die loc
    | RtyBase _ | RtyHAF _ | RtyHAParallel _ | RtyArr _ ->
        ([], destruct_haft_inner loc r)
    | RtyGArr { argnt; retrty; arg } ->
        let args, t = aux retrty in
        ((arg #: argnt) :: args, t)
  in
  aux r

let destruct_hap loc = function
  | RtyHAParallel { history; adding_se; parallel } ->
      (history, adding_se, parallel)
  | _ -> _die loc

let subst_cty name lit { nt; phi } =
  { nt; phi = subst_prop_instance name lit phi }

let subst_raw_sregex name lit r =
  SFA.raw_reg_map (SFA.CharSet.map (subst_sevent_instance name lit)) r

let subst_haft name lit t =
  let rec aux = function
    | RtyBase cty -> RtyBase (subst_cty name lit cty)
    | RtyHAF { history; adding; future } ->
        let history, adding, future =
          map3 (subst_raw_sregex name lit) (history, adding, future)
        in
        RtyHAF { history; adding; future }
    | RtyHAParallel { history; adding_se; parallel } ->
        let history = subst_raw_sregex name lit history in
        let adding_se = subst_sevent_instance name lit adding_se in
        let parallel = List.map (subst_sevent_instance name lit) parallel in
        RtyHAParallel { history; adding_se; parallel }
    | RtyArr { arg; argcty; retrty } ->
        if String.equal arg name then RtyArr { arg; argcty; retrty }
        else
          RtyArr
            { arg; argcty = subst_cty name lit argcty; retrty = aux retrty }
    | RtyGArr { arg; argnt; retrty } ->
        if String.equal arg name then RtyGArr { arg; argnt; retrty }
        else RtyGArr { arg; argnt; retrty = aux retrty }
    | RtyInter (t1, t2) -> RtyInter (aux t1, aux t2)
  in
  aux t

let rec fresh_haft t =
  match t with
  | RtyBase _ | RtyHAF _ | RtyHAParallel _ -> t
  | RtyArr { arg; argcty; retrty } ->
      let arg' = Rename.unique arg in
      let retrty = subst_haft arg (AVar arg' #: argcty.nt) retrty in
      RtyArr { arg = arg'; argcty; retrty = fresh_haft retrty }
  | RtyGArr { arg; argnt; retrty } ->
      let arg' = Rename.unique arg in
      let retrty = subst_haft arg (AVar arg' #: argnt) retrty in
      RtyGArr { arg = arg'; argnt; retrty = fresh_haft retrty }
  | RtyInter (t1, t2) -> RtyInter (fresh_haft t1, fresh_haft t2)

open Zdatatype

let layout_trace_elem (op, args) =
  spf "%s(%s)" op (List.split_by_comma layout_constant args)

let layout_trace = List.split_by "; " layout_trace_elem
