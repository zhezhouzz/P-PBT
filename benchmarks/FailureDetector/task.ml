(* type tNode = (node1 * node2[@tNode]) *)
(* type tTrial = (trial1 * trial2[@tTrial]) *)

val ( == ) : 'a -> 'a -> bool

(** handled by env *)

val eNotifyNodesDown : < node : (node1 * node2[@tNode]) > [@@obsRecv]

let eNotifyNodesDown ?l:(n = (true : [%v: (node1 * node2[@tNode])])) =
  ( starA (anyA - ENotifyNodesDown (node == n)),
    ENotifyNodesDown (node == n),
    [||] )

(** Node Machine *)

val ePing :
  < node : (node1 * node2[@tNode]) ; trial : (trial1 * trial2[@tTrial]) >
[@@obs]

val eShutDown : < node : (node1 * node2[@tNode]) > [@@obs]

let ePing =
  [|
    (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])]))
         ?l:(tl = (true : [%v: (trial1 * trial2[@tTrial])])) ->
      ( starA (anyA - EShutDown (node == n)),
        EPing (node == n && trial == tl),
        [| EPong (node == n && trial == tl) |] ));
    (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])]))
         ?l:(tl = (true : [%v: (trial1 * trial2[@tTrial])])) ->
      ( starA (anyA - EShutDown (node == n)),
        EPing (node == n && trial == tl),
        [| EPongLost (node == n && trial == tl) |] ));
  |]

let eShutDown ?l:(n = (true : [%v: (node1 * node2[@tNode])])) =
  (starA (anyA - EShutDown (node == n)), EShutDown (node == n), [||])

(** Detector Machine *)

val eStart : unit [@@gen]

val ePong :
  < node : (node1 * node2[@tNode]) ; trial : (trial1 * trial2[@tTrial]) >
[@@obs]

val ePongLost :
  < node : (node1 * node2[@tNode]) ; trial : (trial1 * trial2[@tTrial]) >
[@@obs]

let eStart =
  [|
    ( epsilonA,
      EStart true,
      [|
        EPing
          (node == ("Node1" : (node1 * node2[@tNode]))
          && trial == ("Trial1" : (trial1 * trial2[@tTrial])));
        EPing
          (node == ("Node2" : (node1 * node2[@tNode]))
          && trial == ("Trial1" : (trial1 * trial2[@tTrial])));
      |] );
  |]

let ePong =
  [|
    (* Trail1: all pongs are received, done *)
    (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])]))
         ?l:(tl =
             (v == ("Trial1" : (trial1 * trial2[@tTrial]))
               : [%v: (trial1 * trial2[@tTrial])])) ->
      ( (allA;
         EPong ((not (node == n)) && trial == tl);
         allA),
        EPong (node == n && trial == tl),
        [||] ));
    (* Trail1: no lost, wait for others *)
    (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])]))
         ?l:(tl =
             (v == ("Trial1" : (trial1 * trial2[@tTrial]))
               : [%v: (trial1 * trial2[@tTrial])])) ->
      ( starA
          (anyA
          - EPong ((not (node == n)) && trial == tl)
          - EPongLost ((not (node == n)) && trial == tl)),
        EPong (node == n && trial == tl),
        [||] ));
    (* Trail1: has lost, goto next trial *)
    (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])]))
         ?l:(tl =
             (v == ("Trial1" : (trial1 * trial2[@tTrial]))
               : [%v: (trial1 * trial2[@tTrial])])) ->
      ( (allA;
         EPongLost ((not (node == n)) && trial == tl);
         allA),
        EPong (node == n && trial == tl),
        [|
          EPing
            ((not (node == n))
            && trial == ("Trial2" : (trial1 * trial2[@tTrial])));
        |] ));
    (* Trail2: all pongs are received, done *)
    (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])]))
         ?l:(tl =
             (v == ("Trial2" : (trial1 * trial2[@tTrial]))
               : [%v: (trial1 * trial2[@tTrial])])) ->
      (allA, EPong (node == n && trial == tl), [||]));
  |]

let ePongLost =
  [|
    (* Trail1: all lost are received, to go next trial *)
    (* (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])])) *)
    (*      ?l:(tl = *)
    (*          (v == ("Trial1" : (trial1 * trial2[@tTrial])) *)
    (*            : [%v: (trial1 * trial2[@tTrial])])) -> *)
    (*   ( (allA; *)
    (*      EPongLost ((not (node == n)) && trial == tl); *)
    (*      allA), *)
    (*     EPongLost (node == n && trial == tl), *)
    (*     [| *)
    (*       EPing (node == n && trial == ("Trial2" : (trial1 * trial2[@tTrial]))); *)
    (*       EPing *)
    (*         ((not (node == n)) *)
    (*         && trial == ("Trial2" : (trial1 * trial2[@tTrial]))); *)
    (*     |] )); *)
    (* Trail1: no lost, wait for others *)
    (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])]))
         ?l:(tl =
             (v == ("Trial1" : (trial1 * trial2[@tTrial]))
               : [%v: (trial1 * trial2[@tTrial])])) ->
      ( starA
          (anyA
          - EPong ((not (node == n)) && trial == tl)
          - EPongLost ((not (node == n)) && trial == tl)),
        EPongLost (node == n && trial == tl),
        [||] ));
    (* Trail1: has pong, goto next trial *)
    (* (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])])) *)
    (*      ?l:(tl = *)
    (*          (v == ("Trial1" : (trial1 * trial2[@tTrial])) *)
    (*            : [%v: (trial1 * trial2[@tTrial])])) -> *)
    (*   ( (allA; *)
    (*      EPong ((not (node == n)) && trial == tl); *)
    (*      allA), *)
    (*     EPongLost (node == n && trial == tl), *)
    (*     [| *)
    (*       EPing (node == n && trial == ("Trial2" : (trial1 * trial2[@tTrial]))); *)
    (*     |] )); *)
    (* Trail2: still lost, done *)
    (fun ?l:(n = (true : [%v: (node1 * node2[@tNode])]))
         ?l:(tl =
             (v == ("Trial2" : (trial1 * trial2[@tTrial]))
               : [%v: (trial1 * trial2[@tTrial])])) ->
      ( allA,
        EPongLost (node == n && trial == tl),
        [| ENotifyNodesDown (node == n) |] ));
  |]

let[@goal] detectFalseNegative (n : (node1 * node2[@tNode])) =
  not
    (starA (anyA - EShutDown (node == n));
     ENotifyNodesDown (node == n);
     starA (anyA - EShutDown (node == n)))
