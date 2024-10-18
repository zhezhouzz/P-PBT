val ( == ) : 'a -> 'a -> bool
val ( > ) : int -> int -> bool
val ( - ) : int -> int -> int
val eInitAccount : < accountId : aid ; balance : int > [@@gen]

let eInitAccount ?l:(ac = (true : [%v: aid])) ?l:(ba = (v > 0 : [%v: int])) =
  ( starA (anyA - EInitAccount (accountId == ac)),
    EInitAccount (accountId == ac && balance == ba),
    [||] )

val eWithDrawReq : < rId : rid ; accountId : aid ; amount : int > [@@gen]

let eWithDrawReq ?l:(id = (true : [%v: rid])) ?l:(ac = (true : [%v: aid]))
    ?l:(am = (v > 0 : [%v: int])) =
  ( allA,
    EWithDrawReq (rId == id && accountId == ac && amount == am),
    [| EReadQuery (accountId == ac) |] )

val eWithDrawResp :
  < rId : rid ; accountId : aid ; balance : int ; status : bool >
[@@obs]

let eWithDrawResp ?l:(id = (true : [%v: rid])) ?l:(ac = (true : [%v: aid]))
    ?l:(ba = (v > 0 : [%v: int])) ?l:(st = (true : [%v: bool])) =
  ( allA,
    EWithDrawResp
      (rId == id && accountId == ac && balance == ba && iff status st),
    [||] )

(** Events used to communicate between the bank server and the backend database *)

(* event: send update the database, i.e. the `balance` associated with the `accountId` *)
val eUpdateQuery : < accountId : aid ; balance : int > [@@obs]

let eUpdateQuery ?l:(ac = (true : [%v: aid])) ?l:(ba = (v > 0 : [%v: int])) =
  (allA, EUpdateQuery (accountId == ac && balance == ba), [||])

(* event: send a read request for the `accountId`. *)
val eReadQuery : < accountId : aid > [@@obs]

let eReadQuery =
  [|
    (fun (ba : int) ?l:(ac = (true : [%v: aid])) ->
      ( (allA;
         EInitAccount (accountId == ac && balance == ba);
         starA
           (anyA - EReadQuery (accountId == ac) - EInitAccount (accountId == ac))),
        EReadQuery (accountId == ac),
        [| EReadQueryResp (accountId == ac && balance == ba) |] ));
    (* (fun (ba : int) ?l:(ac = (true : [%v: aid])) -> *)
    (*   ( (allA; *)
    (*      EReadQueryResp (accountId == ac && balance == ba); *)
    (*      starA *)
    (*        (anyA - EReadQuery (accountId == ac) - EInitAccount (accountId == ac))), *)
    (*     EReadQuery (accountId == ac), *)
    (*     [| EReadQueryResp (accountId == ac && balance == ba) |] )); *)
  |]

(* event: send a response (`balance`) corresponding to the read request for an `accountId` *)
val eReadQueryResp : < accountId : aid ; balance : int > [@@obs]

let eReadQueryResp =
  [|
    (fun (id : rid) (am : int) ?l:(ac = (true : [%v: aid]))
         ?l:(ba = (v > 0 && v > am : [%v: int])) ->
      ( (starA (anyA - EReadQueryResp true - EReadQuery true);
         EWithDrawReq (rId == id && accountId == ac && amount == am);
         starA (anyA - EWithDrawReq true)),
        EReadQueryResp (accountId == ac && balance == ba),
        [|
          EUpdateQuery (accountId == ac && balance == ba - am);
          EWithDrawResp
            (rId == id && accountId == ac && balance == ba - am && status);
        |] ));
    (fun (id : rid) (am : int) ?l:(ac = (true : [%v: aid]))
         ?l:(ba = (v > 0 && not (v > am) : [%v: int])) ->
      ( (starA (anyA - EReadQueryResp true - EReadQuery true);
         EWithDrawReq (rId == id && accountId == ac && amount == am);
         starA (anyA - EWithDrawReq true)),
        EReadQueryResp (accountId == ac && balance == ba),
        [|
          EWithDrawResp
            (rId == id && accountId == ac && balance == ba - am && not status);
        |] ));
  |]

let[@goal] bankWithdrawSuccess (ac : aid) (ba : int) =
  not
    (allA;
     EWithDrawResp (accountId == ac && not status);
     allA)
