open Common
open Zzdatatype.Datatype

module type AUTOMATA = sig
  module C : CHARACTER
  module CharMap : Map.S with type key = C.t

  type transitions = StateSet.t CharMap.t
  type d_transition = state CharMap.t

  type nfa = {
    start : StateSet.t;
    finals : StateSet.t;
    next : state -> transitions;
  }

  type dfa = {
    start : state;
    finals : StateSet.t;
    next : state -> d_transition;
  }
end
