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

type haft =
  | RtyBase of cty
  | RtyHAF of { history : srl; adding : srl; future : srl }
  | RtyArr of { arg : string; argcty : cty; retrty : haft }
  | RtyInter of haft * haft
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

type item =
  | PrimDecl of { name : string; nt : Nt.nt }
  | MsgNtDecl of { generative : bool; name : string; nt : Nt.nt }
  | MsgDecl of { name : string; haft : haft }
  | SynGoal of srl
[@@deriving show, eq, ord]

type syn_env = {
  event_rtyctx : haft ctx;
  gen_ctx : bool ctx;
  event_tyctx : (Nt.nt, string) typed list ctx;
  tyctx : Nt.t ctx;
  goal : srl option;
}

let mk_inter_type l =
  match l with
  | [] -> _die [%here]
  | h :: t -> List.fold_left (fun x y -> RtyInter (x, y)) h t

let erase_cty { nt; _ } = nt

let rec erase_rty = function
  | RtyBase cty -> erase_cty cty
  | RtyHAF _ -> Nt.Ty_unit
  | RtyArr { argcty; retrty; _ } ->
      Nt.mk_arr (erase_cty argcty) (erase_rty retrty)
  | RtyInter (t1, t2) ->
      let t1, t2 = map2 erase_rty (t1, t2) in
      let t = Nt._type_unify [%here] t1 t2 in
      t

(* module type AST = sig *)
(*   type 'a ast [@@deriving sexp, show, eq, ord] *)

(*   val fv : 'a ast -> string *)
(*   val subst : 'a ast -> string -> 'a ast -> 'a ast *)
(*   val subst_id : 'a ast -> string -> string -> 'a ast *)
(* end *)
