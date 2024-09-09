open Ast
open Common

module MakeAutomata (C : CHARACTER) = struct
  module C = C
  module CharMap = Map.Make (C)

  type transitions = StateSet.t CharMap.t
  type d_transition = state CharMap.t

  type nfa = {
    start : StateSet.t;
    finals : StateSet.t;
    next : state -> transitions;
  }

  let find_states sym nfa m =
    try CharMap.find sym (nfa.next m) with Not_found -> StateSet.empty

  let fold_states_nfa : 'a. (state -> 'a -> 'a) -> nfa -> 'a -> 'a =
   fun f nfa init ->
    let v = ref init in
    let seen = Hashtbl.create 10 in
    let rec apply state =
      if not (Hashtbl.mem seen state) then (
        v := f state !v;
        Hashtbl.add seen state ();
        CharMap.iter (fun _ -> visit) (nfa.next state))
    and visit states = StateSet.iter apply states in
    visit nfa.start;
    !v

  let fold_transitions_nfa :
        'a. (state * C.t * state -> 'a -> 'a) -> nfa -> 'a -> 'a =
   fun f nfa init ->
    fold_states_nfa
      (fun src v ->
        CharMap.fold
          (fun (c : C.t) dsts ->
            StateSet.fold (fun dst -> f (src, c, dst)) dsts)
          (nfa.next src) v)
      nfa init

  let layout_nfa nfa =
    (* let open Zdatatype in *)
    let () =
      Printf.printf "starts: %s\n" (layout_states Int.to_string nfa.start)
    in
    let () =
      Printf.printf "finals: %s\n" (layout_states Int.to_string nfa.finals)
    in
    let () =
      fold_transitions_nfa
        (fun (s, c, d) _ ->
          Printf.printf "\t%s--[%s]-->%s\n" (Int.to_string s) (C.layout c)
            (Int.to_string d))
        nfa ()
    in
    let () = print_newline () in
    ()

  let flat_map f ss =
    StateSet.fold (fun s -> StateSet.union (f s)) ss StateSet.empty

  let nextss curs sym nfa = flat_map (find_states sym nfa) curs

  (** Complement *)

  let union_charmap c1 c2 =
    CharMap.merge
      (fun _ s1 s2 ->
        match (s1, s2) with
        | None, None -> None
        | Some s1, None -> Some s1
        | None, Some s2 -> Some s2
        | Some s1, Some s2 -> Some (StateSet.union s1 s2))
      c1 c2

  let complete_nfa (ctx : C.t list) (nfa : nfa) =
    (* Add a dummy node to complete the nfa, where we just record the transitions to this node. *)
    let max_state = ref None in
    let update_max s =
      match !max_state with
      | None -> max_state := Some (Int.add s 1)
      | Some n -> if s >= n then max_state := Some (Int.add s 1) else ()
    in
    let dummy_transitions = Hashtbl.create 1000 in
    let point_to_dummy_node (s, c) =
      (* let () = *)
      (*   Printf.printf "### --%s-->%s\n" (C.layout c) (Int.to_string s) *)
      (* in *)
      match Hashtbl.find_opt dummy_transitions c with
      | None -> Hashtbl.add dummy_transitions c (StateSet.singleton s)
      | Some ss -> Hashtbl.replace dummy_transitions c (StateSet.add s ss)
    in
    let () =
      fold_states_nfa
        (fun state () ->
          let () = update_max state in
          let m = nfa.next state in
          List.iter
            (fun c ->
              match CharMap.find_opt c m with
              | None -> point_to_dummy_node (state, c)
              | Some _ -> ())
            ctx)
        nfa ()
    in
    (* reverse the nfa *)
    if Hashtbl.length dummy_transitions == 0 then (* already complete *)
      nfa
    else
      match !max_state with
      | None -> _die [%here]
      | Some s' ->
          let char_map =
            List.fold_right
              (fun c ->
                CharMap.update c (function
                  | None -> Some (StateSet.singleton s')
                  | Some ss -> Some (StateSet.add s' ss)))
              ctx CharMap.empty
          in
          let map = StateMap.add s' char_map StateMap.empty in
          let next' =
            Hashtbl.fold
              (fun c ss map ->
                StateSet.fold
                  (fun s (map : StateSet.t CharMap.t StateMap.t) ->
                    StateMap.update s
                      (function
                        | None ->
                            Some (CharMap.singleton c (StateSet.singleton s'))
                        | Some (char_map : StateSet.t CharMap.t) ->
                            Some
                              (CharMap.update c
                                 (function
                                   | None -> Some (StateSet.singleton s')
                                   | Some state_set ->
                                       Some (StateSet.add s' state_set))
                                 char_map))
                      map)
                  ss map)
              dummy_transitions map
          in
          {
            start = nfa.start;
            finals = nfa.finals;
            next =
              (fun s ->
                let res' = try nfa.next s with Not_found -> CharMap.empty in
                match StateMap.find_opt s next' with
                | Some res -> union_charmap res res'
                | None -> res');
          }

  (** A simple NFA interpreter.
      cur is the set of all the current states -- i.e. those states at
      which we have arrived by examining the input up to this point.
      Since the automaton is non-deterministic, encountering a character
      in a given state can cause transitions to multiple different
      states *)
  let nfa_accept (nfa : nfa) inp =
    let rec step cur = function
      | [] -> StateSet.(not (is_empty (inter cur nfa.finals)))
      | c :: cs -> step (nextss cur c nfa) cs
    in
    step nfa.start inp

  type dfa = {
    start : state;
    finals : StateSet.t;
    next : state -> d_transition;
  }

  let charmap_union (type a) (f : C.t -> a -> a -> a option) =
    let f k x y =
      match (x, y) with
      | None, None -> None
      | Some v, None -> Some v
      | None, Some v -> Some v
      | Some v1, Some v2 -> f k v1 v2
    in
    CharMap.merge f

  let fold_states : 'a. (state -> 'a -> 'a) -> dfa -> 'a -> 'a =
   fun f dfa init ->
    let v = ref init in
    let seen = Hashtbl.create 10 in
    let rec visit state =
      if not (Hashtbl.mem seen state) then (
        v := f state !v;
        Hashtbl.add seen state ();
        CharMap.iter (fun _ -> visit) (dfa.next state))
    in
    visit dfa.start;
    !v

  let fold_transitions :
        'a. (state * C.t * state -> 'a -> 'a) -> dfa -> 'a -> 'a =
   fun f dfa init ->
    fold_states
      (fun src v ->
        CharMap.fold (fun c dst -> f (src, c, dst)) (dfa.next src) v)
      dfa init

  (** Add src--c-->dst to the transition set, replacing any existing src--c-->dst' *)
  let add_transition (src, c, dst) trans =
    match StateMap.find src trans with
    | exception Not_found -> StateMap.add src (CharMap.singleton c dst) trans
    | cm -> StateMap.add src (CharMap.add c dst cm) trans

  (** Add src--c-->dst to the transition set, augmenting any existing src--c-->dst' *)
  let add_transition' (src, c, dst) trans =
    match StateMap.find src trans with
    | exception Not_found ->
        StateMap.add src (CharMap.singleton c (StateSet.singleton dst)) trans
    | cm ->
        let dstset =
          match CharMap.find c cm with
          | exception Not_found -> StateSet.singleton dst
          | dstset -> StateSet.add dst dstset
        in
        StateMap.add src (CharMap.add c dstset cm) trans

  (** Build an NFA by reversing a DFA, inverting transition arrows,
   turning finals states into start states, and the start state into
   the final state *)
  let reverse (dfa : dfa) : nfa =
    let map =
      fold_transitions
        (fun (s, c, t) -> add_transition' (t, c, s))
        dfa StateMap.empty
    in
    {
      start = dfa.finals;
      finals = StateSet.singleton dfa.start;
      next =
        (fun s -> try StateMap.find s map with Not_found -> CharMap.empty);
    }

  (** Available transitions from a set of states *)
  let transitions states (nfa : nfa) =
    StateSet.fold
      (fun s m ->
        let m' = nfa.next s in
        charmap_union (fun _ s s' -> Some (StateSet.union s s')) m m')
      states CharMap.empty

  (** Conversion to DFA via the powerset construction *)
  let determinize : nfa -> dfa =
    let module M = Map.Make (StateSet) in
    fun nfa ->
      let fresh =
        let r = ref (_default_init_state : int) in
        fun () ->
          r := Int.succ !r;
          !r
      in
      let rec build states (map, ts, finals) =
        match M.find states map with
        | state -> (state, map, ts, finals)
        | exception Not_found ->
            let state = fresh () in
            let finals =
              if not (StateSet.is_empty (StateSet.inter states nfa.finals)) then
                StateSet.add state finals
              else finals
            in
            let map = M.add states state map in
            let tsn = transitions states nfa in
            let map, ts, finals =
              CharMap.fold
                (fun c ss (map, ts, finals) ->
                  let dst, map, ts, finals = build ss (map, ts, finals) in
                  let ts = add_transition (state, c, dst) ts in
                  (map, ts, finals))
                tsn (map, ts, finals)
            in
            (state, map, ts, finals)
      in

      let start, _, trans, finals =
        build nfa.start (M.empty, StateMap.empty, StateSet.empty)
      in
      let next s =
        try StateMap.find s trans with Not_found -> CharMap.empty
      in
      { start; finals; next }

  (** Brzozowski's DFA minimization algorithm:
    reverse DFA to build an NFA and determinize, then do the same again *)
  let minimize g = determinize (reverse (determinize (reverse g)))

  let inject ({ start; finals; next } : dfa) : nfa =
    {
      start = StateSet.singleton start;
      finals;
      next = (fun s -> CharMap.map StateSet.singleton (next s));
    }

  (** A simple DFA interpreter. *)
  let dfa_accept dfa inp =
    let rec step cur = function
      | [] -> StateSet.mem cur dfa.finals
      | c :: cs -> (
          match CharMap.find c (dfa.next cur) with
          | exception Not_found -> false
          | s -> step s cs)
    in
    step dfa.start inp

  (** Regex to NFA *)

  module CharSet = Set.Make (C)
  (** Convert a raw_regex to an ε-free NFA using a slight modification of
    Glushkov's algorithm.

    (The modification: we label character sets rather than characters
     to prevent a state explosion.)
 *)

  (** A 'letter' is a character set paired with an identifier that
    uniquely identifies the character set within the raw_regex *)
  module Letter = struct
    type t = CharSet.t * state

    let compare (_, x) (_, y) = Int.compare x y
  end

  (** Sets of single letters *)
  module LetterSet = struct
    module S = Set.Make (Letter)

    let ( <+> ) = S.union
  end

  (** Sets of letter pairs *)
  module Letter2Set = struct
    module Pair = struct
      type t = Letter.t * Letter.t

      let compare ((_, w), (_, x)) ((_, y), (_, z)) =
        Stdlib.compare (w, x) (y, z)
    end

    module S = Set.Make (Pair)

    let ( <+> ) = S.union
    let ( >>= ) m k = LetterSet.S.fold (fun x s -> k x <+> s) m S.empty

    let ( <*> ) : LetterSet.S.t -> LetterSet.S.t -> S.t =
     fun l r ->
      l >>= fun x ->
      r >>= fun y -> S.singleton (x, y)
  end

  type 'c raw_regex =
    | Empty : 'c raw_regex (* L = { } *)
    | Eps : 'c raw_regex (* L = {ε} *)
    | Char : 'c -> 'c raw_regex
    | Alt : 'c raw_regex * 'c raw_regex -> 'c raw_regex
    | Seq : 'c raw_regex * 'c raw_regex -> 'c raw_regex
    | Star : 'c raw_regex -> 'c raw_regex

  (** Λ(r) is {ε} ∩ L(r); we represent it as a bool *)
  let rec l = function
    | Empty -> false
    | Eps -> true
    | Char _ -> false
    | Alt (e, f) -> l e || l f
    | Seq (e, f) -> l e && l f
    | Star _ -> true

  (** firsts: P(r) = {c | ∃s.cs ∈ L(r) } *)
  let rec p =
    let open LetterSet in
    function
    | Empty | Eps -> S.empty
    | Char c -> S.singleton c
    | Alt (e, f) -> p e <+> p f
    | Seq (e, f) -> p e <+> if l e then p f else S.empty
    | Star e -> p e

  (** lasts: D(r) = {c | ∃s.sc ∈ L(r) } *)
  let rec d =
    let open LetterSet in
    function
    | Empty | Eps -> S.empty
    | Char c -> S.singleton c
    | Alt (f, e) -> d f <+> d e
    | Seq (f, e) -> (if l e then d f else S.empty) <+> d e
    | Star e -> d e

  (** factors of length 2: F(r) = {c₁c₂ | ∃s₁s₂.s₁c₁c₂s₂ ∈ L(R)} *)
  let rec f_ =
    let open Letter2Set in
    function
    | Empty | Eps | Char _ -> S.empty
    | Alt (e, f) -> f_ e <+> f_ f
    | Seq (e, f) -> f_ e <+> f_ f <+> (d e <*> p f)
    | Star e -> f_ e <+> (d e <*> p e)

  module CharSetMap = Map.Make (CharSet)

  let add_transition2 c i tm =
    let ss =
      match CharSetMap.find c tm with
      | exception Not_found -> StateSet.empty
      | ss -> ss
    in
    CharSetMap.add c (StateSet.add i ss) tm

  let add_transition i1 c2 i2 sm =
    let tm =
      match StateMap.find i1 sm with
      | exception Not_found -> CharSetMap.empty
      | ss -> ss
    in
    StateMap.add i1 (add_transition2 c2 i2 tm) sm

  let transition_map_of_factor_set fs =
    Letter2Set.S.fold
      (fun ((_, i1), (c2, i2)) sm -> add_transition i1 c2 i2 sm)
      fs StateMap.empty

  let positions : LetterSet.S.t -> StateSet.t =
   fun s -> StateSet.of_list (List.map snd (LetterSet.S.elements s))

  let transition_map_of_letter_set : LetterSet.S.t -> StateSet.t CharSetMap.t =
   fun s ->
    LetterSet.S.fold
      (fun (c, i) tm ->
        let entry =
          match CharSetMap.find c tm with
          | exception Not_found -> StateSet.singleton i
          | s -> StateSet.add i s
        in
        CharSetMap.add c entry tm)
      s CharSetMap.empty

  type t = CharSet.t raw_regex

  let fresh_state =
    let counter = ref _default_init_state in
    let incr64 r = r := Int.succ !r in
    fun () ->
      let c = !counter in
      incr64 counter;
      c

  let start_state = fresh_state ()

  let rec annotate : 'a. 'a raw_regex -> ('a * int) raw_regex = function
    | Empty -> Empty
    | Eps -> Eps
    | Char c ->
        let p = (c, fresh_state ()) in
        Char p
    | Alt (e, f) -> Alt (annotate e, annotate f)
    | Seq (e, f) -> Seq (annotate e, annotate f)
    | Star e -> Star (annotate e)

  let flatten_transitions : StateSet.t CharSetMap.t -> StateSet.t CharMap.t =
   fun cm ->
    CharSetMap.fold
      (fun cs ss cm ->
        CharSet.fold
          (fun c cm ->
            let entry =
              match CharMap.find c cm with
              | exception Not_found -> StateSet.empty
              | ss -> ss
            in
            CharMap.add c (StateSet.union ss entry) cm)
          cs cm)
      cm CharMap.empty

  let compile_from_raw_regex r : nfa =
    (* Give every character set in 'r' a unique identifier *)
    let r = annotate r in

    (* The final states are the set of 'last' characters in r,
        (+ the start state if r accepts the empty string) *)
    let finals =
      if l r then StateSet.add start_state (positions (d r))
      else positions (d r)
    in

    (* Transitions arise from factor (pairs of character sets with a
        transition between them) ... *)
    let transitions = transition_map_of_factor_set (f_ r) in

    (* ... and from the start state to the initial character sets. *)
    let initial_transitions = transition_map_of_letter_set (p r) in
    let joint_transitions =
      StateMap.add start_state initial_transitions transitions
    in

    (* The 'next' function is built from the transition sets. *)
    let next s =
      try flatten_transitions (StateMap.find s joint_transitions)
      with Not_found -> CharMap.empty
    in
    { start = StateSet.singleton start_state; finals; next }

  (** Various basic and derived raw_regex combinators *)
  let seq l r = match (l, r) with Eps, s | s, Eps -> s | l, r -> Seq (l, r)

  let alt l r =
    match (l, r) with
    | Char c1, Char c2 -> Char (CharSet.union c1 c2)
    | l, r -> Alt (l, r)

  let star r = Star r
  let plus t = seq t (star t)
  let eps = Eps
  let chr c = Char (CharSet.singleton c)
  let opt t = alt t eps
  let empty = Empty
  let oneof cs = match CharSet.cardinal cs with 0 -> Empty | _ -> Char cs

  let mk_repeat (n, r) =
    let rec aux (n, r) =
      match n with
      | 0 -> Eps
      | 1 -> r
      | _ when n > 1 -> seq r (aux (n - 1, r))
      | _ -> _die_with [%here] "invalid repeat"
    in
    aux (n, r)

  let regex_to_raw (regex : ('t, C.t) regex) : CharSet.t raw_regex option =
    (* let regex = Regex.to_nnf regex in *)
    (* let () = *)
    (*   Printf.printf "regex_to_raw: %s\n" *)
    (*     (Sexplib.Sexp.to_string *)
    (*     @@ sexp_of_regex *)
    (*          (fun c -> Sexplib.Std.sexp_of_string @@ C.layout c) *)
    (*          regex) *)
    (* in *)
    let rec aux (regex : ('t, C.t) regex) : CharSet.t raw_regex option =
      match regex with
      | Extension _ | SyntaxSugar _ | RExpr _ -> failwith "die"
      | LandA _ | DComplementA _ -> None
      | RepeatN (n, r) ->
          let* r = aux r in
          Some (mk_repeat (n, r))
      | MultiAtomic l -> Some (Char (CharSet.of_list l))
      | EmptyA -> Some Empty
      | EpsilonA -> Some Eps
      | Atomic c -> Some (Char (CharSet.singleton c))
      | LorA (r1, r2) ->
          let* r1 = aux r1 in
          let* r2 = aux r2 in
          Some (alt r1 r2)
      | SeqA (r1, r2) ->
          let* r1 = aux r1 in
          let* r2 = aux r2 in
          Some (seq r1 r2)
      | StarA r ->
          let* r = aux r in
          Some (star r)
    in
    aux regex

  let compile (r : ('t, C.t) regex) : nfa =
    match regex_to_raw r with
    | Some r -> compile_from_raw_regex r
    | None -> _die [%here]

  let layout_dfa (dfa : dfa) =
    (* let open Zdatatype in *)
    let res = Printf.sprintf "start: %s\n" (Int.to_string dfa.start) in
    let res =
      Printf.sprintf "%sfinals: %s\n" res
        (layout_states Int.to_string dfa.finals)
    in
    let res =
      fold_transitions
        (fun (s, c, d) res ->
          Printf.sprintf "%s\t%s--[%s]-->%s\n" res (Int.to_string s)
            (C.layout c) (Int.to_string d))
        dfa res
    in
    spf "%s\n" res

  let complete_dfa (ctx : C.t list) (dfa : dfa) =
    determinize @@ complete_nfa ctx @@ inject dfa

  let swap_dfa (dfa : dfa) : dfa =
    let finals =
      fold_states
        (fun s res ->
          if StateSet.mem s dfa.finals then res else StateSet.add s res)
        dfa StateSet.empty
    in
    { start = dfa.start; finals; next = dfa.next }

  let complement_dfa (ctx : C.t list) (dfa : dfa) =
    swap_dfa @@ complete_dfa ctx dfa

  let complement_nfa (ctx : C.t list) (nfa : nfa) =
    inject @@ swap_dfa @@ determinize @@ complete_nfa ctx nfa

  (** binary operations *)

  let concretelize_nfa_aux renaming (nfa : nfa) =
    let next =
      fold_transitions_nfa
        (fun (s, c, d) ->
          let s = renaming s in
          let d = renaming d in
          StateMap.update s (function
            | None -> Some (CharMap.singleton c (StateSet.singleton d))
            | Some charmap ->
                Some
                  (CharMap.update c
                     (function
                       | None -> Some (StateSet.singleton d)
                       | Some ss -> Some (StateSet.add d ss))
                     charmap)))
        nfa StateMap.empty
    in
    next

  let concretelize_dfa_aux renaming (dfa : dfa) =
    let next =
      fold_transitions
        (fun (s, c, d) ->
          let s = renaming s in
          let d = renaming d in
          StateMap.update s (function
            | None -> Some (CharMap.singleton c d)
            | Some charmap -> Some (CharMap.add c d charmap)))
        dfa StateMap.empty
    in
    next

  let construct_next next s =
    match StateMap.find_opt s next with
    | None -> CharMap.empty
    | Some res -> res

  let concretelize_nfa (nfa : nfa) : nfa =
    let next = concretelize_nfa_aux (fun x -> x) nfa in
    { start = nfa.start; finals = nfa.finals; next = construct_next next }

  let concretelize_dfa (dfa : dfa) : dfa =
    let next = concretelize_dfa_aux (fun x -> x) dfa in
    { start = dfa.start; finals = dfa.finals; next = construct_next next }

  let rename_nfa rename (nfa : nfa) : nfa =
    let start = StateSet.map rename nfa.start in
    let finals = StateSet.map rename nfa.finals in
    let next = concretelize_nfa_aux rename nfa in
    { start; finals; next = construct_next next }

  let rename_dfa rename (dfa : dfa) : dfa =
    let start = rename dfa.start in
    let finals = StateSet.map rename dfa.finals in
    let next = concretelize_dfa_aux rename dfa in
    { start; finals; next = construct_next next }

  let normalize_nfa (nfa : nfa) : nfa =
    let state_naming = ref StateMap.empty in
    let next_state = ref _default_init_state in
    let incr () =
      let res = !next_state in
      next_state := Int.add 1 !next_state;
      res
    in
    let do_state_renaming s =
      match StateMap.find_opt s !state_naming with
      | Some _ -> ()
      | None -> state_naming := StateMap.add s (incr ()) !state_naming
    in
    let () = fold_states_nfa (fun s () -> do_state_renaming s) nfa () in
    rename_nfa (fun s -> StateMap.find s !state_naming) nfa

  let normalize_dfa (dfa : dfa) : dfa =
    let state_naming = ref StateMap.empty in
    let next_state = ref _default_init_state in
    let incr () =
      let res = !next_state in
      next_state := Int.add 1 !next_state;
      res
    in
    let do_state_renaming s =
      match StateMap.find_opt s !state_naming with
      | Some _ -> ()
      | None -> state_naming := StateMap.add s (incr ()) !state_naming
    in
    let () = fold_states (fun s () -> do_state_renaming s) dfa () in
    rename_dfa (fun s -> StateMap.find s !state_naming) dfa

  let num_states_nfa (nfa : nfa) = fold_states_nfa (fun _ x -> x + 1) nfa 0
  let num_states_dfa (dfa : dfa) = fold_states (fun _ x -> x + 1) dfa 0

  let mk_disjoint_nfa (nfa1 : nfa) (nfa2 : nfa) =
    let nfa1 = normalize_nfa nfa1 in
    let nfa2 = normalize_nfa nfa2 in
    let n1 = num_states_nfa nfa1 in
    let nfa2 = rename_nfa (fun x -> Int.add x n1) nfa2 in
    (nfa1, nfa2)

  let mk_disjoint_dfa (dfa1 : dfa) (dfa2 : dfa) =
    let dfa1 = normalize_dfa dfa1 in
    let dfa2 = normalize_dfa dfa2 in
    let n1 = num_states_dfa dfa1 in
    let dfa2 = rename_dfa (fun x -> Int.add x n1) dfa2 in
    (dfa1, dfa2)

  let union_nfa (nfa1 : nfa) (nfa2 : nfa) : nfa =
    let nfa1, nfa2 = mk_disjoint_nfa nfa1 nfa2 in
    {
      start = StateSet.union nfa1.start nfa2.start;
      finals = StateSet.union nfa1.finals nfa2.finals;
      next = (fun s -> union_charmap (nfa1.next s) (nfa2.next s));
    }

  let union_dfa (dfa1 : dfa) (dfa2 : dfa) : dfa =
    minimize @@ determinize @@ union_nfa (inject dfa1) (inject dfa2)

  let intersect_dfa (dfa1 : dfa) (dfa2 : dfa) : dfa =
    let dfa1 = normalize_dfa dfa1 in
    let dfa2 = normalize_dfa dfa2 in
    (* let () = Printf.printf "num = %i\n" (num_states_dfa dfa1) in *)
    (* let () = layout_dfa dfa1 in *)
    (* let () = layout_dfa dfa2 in *)
    let num2 = num_states_dfa dfa2 in
    let mk_p (n1 : state) (n2 : state) =
      let res = Int.add n2 @@ Int.mul num2 n1 in
      (* let () = *)
      (*   Printf.printf "%s + %s*%s = %s\n" (Int.to_string n2) *)
      (*     (Int.to_string num2) (Int.to_string n1) (Int.to_string res) *)
      (* in *)
      res
    in
    let fst_p p = Int.div p num2 in
    let snd_p p = Int.rem p num2 in
    let seen = Hashtbl.create 1000 in
    let tbl = ref StateMap.empty in
    let update_tbl (s, c, d) =
      tbl :=
        StateMap.update s
          (function
            | None -> Some (CharMap.singleton c d)
            | Some charmap -> Some (CharMap.add c d charmap))
          !tbl
    in
    let rec visit state =
      if not (Hashtbl.mem seen state) then
        (* let () = *)
        (*   Printf.printf "state: (%s, %s)\n" *)
        (*     (Int.to_string (fst_p state)) *)
        (*     (Int.to_string (snd_p state)) *)
        (* in *)
        let () = Hashtbl.add seen state () in
        let charmap1 = dfa1.next (fst_p state) in
        let charmap2 = dfa2.next (snd_p state) in
        CharMap.iter
          (fun c d1 ->
            match CharMap.find_opt c charmap2 with
            | None -> ()
            | Some d2 ->
                (* let () = *)
                (*   Printf.printf "\t--[%s]-->(%s, %s)\n" (C.layout c) *)
                (*     (Int.to_string d1) (Int.to_string d2) *)
                (* in *)
                let d = mk_p d1 d2 in
                update_tbl (state, c, d);
                visit d)
          charmap1
    in
    let start = mk_p dfa1.start dfa2.start in
    let () = visit start in
    let finals =
      StateSet.fold
        (fun s1 ->
          StateSet.fold (fun s2 -> StateSet.add (mk_p s1 s2)) dfa2.finals)
        dfa1.finals StateSet.empty
    in
    let res = { start; finals; next = construct_next !tbl } in
    (* let () = layout_dfa res in *)
    minimize res

  let intersect_nfa (nfa1 : nfa) (nfa2 : nfa) : nfa =
    inject @@ intersect_dfa (determinize nfa1) (determinize nfa2)

  let concat_dfa (dfa1 : dfa) (dfa2 : dfa) : dfa =
    let dfa1 = normalize_dfa dfa1 in
    let dfa2 = normalize_dfa dfa2 in
    let finals = List.of_seq @@ StateSet.to_seq @@ dfa1.finals in
    let _, dfa2s =
      List.fold_left
        (fun (total_num, res) final ->
          let dfa2 =
            rename_dfa
              (fun x ->
                if Int.equal Int.zero x then final else Int.add x total_num)
              dfa2
          in
          let dfa2 = { dfa2 with start = final } in
          let total_num = total_num + num_states_dfa dfa2 in
          (total_num, res @ [ dfa2 ]))
        (num_states_dfa dfa1, [])
        finals
    in
    let new_finals =
      List.fold_left
        (fun s dfa2 -> StateSet.union s dfa2.finals)
        StateSet.empty dfa2s
    in
    let new_transitoins s =
      List.fold_left
        (fun m dfa2 ->
          union_charmap m
            (CharMap.map (fun s -> StateSet.singleton s) @@ dfa2.next s))
        CharMap.empty dfa2s
    in
    let nfa : nfa =
      {
        start = StateSet.singleton dfa1.start;
        finals = new_finals;
        next = new_transitoins;
      }
    in
    minimize (determinize nfa)

  let desugar_and_delimit_regex r =
    let r = Regex.desugar r in
    let r = Regex.delimit_context C.delimit_cotexnt_char r in
    let r = Regex.simp_regex (fun a b -> 0 == C.compare a b) r in
    r

  let compile2dfa (r : ('t, C.t) regex) : dfa =
    let r = desugar_and_delimit_regex r in
    let rec aux r =
      let res =
        match regex_to_raw r with
        | Some r -> minimize @@ determinize @@ compile_from_raw_regex r
        | None -> (
            match r with
            | DComplementA { atoms; body } -> complement_dfa atoms @@ aux body
            | LandA (r1, r2) ->
                (* complement_dfa ctx *)
                (* @@ union_dfa *)
                (*      (complement_dfa ctx @@ aux r1) *)
                (*      (complement_dfa ctx @@ aux r2) *)
                intersect_dfa (aux r1) (aux r2)
            | SeqA (r1, r2) -> concat_dfa (aux r1) (aux r2)
            | _ ->
                let () =
                  Printf.printf "\n?? %s\n" @@ Regex.layout_sexp_regex r
                in
                _die [%here])
      in
      (* let () = *)
      (*   Printf.printf "compile2dfa: %s\n" *)
      (*     (Sexplib.Sexp.to_string *)
      (*     @@ sexp_of_regex (fun c -> Sexplib.Std.sexp_of_string @@ C.layout c) r *)
      (*     ) *)
      (* in *)
      (* let () = layout_dfa res in *)
      res
    in
    aux r

  let map_on_char_dfa (dfa : dfa) (f : C.t -> C.t) : dfa =
    let next = concretelize_dfa_aux (fun x -> x) dfa in
    let next =
      StateMap.map
        (fun m ->
          CharMap.of_seq
          @@ Seq.map (fun (char, s) -> (f char, s))
          @@ CharMap.to_seq m)
        next
    in
    { start = dfa.start; finals = dfa.finals; next = construct_next next }
end
