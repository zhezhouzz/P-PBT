val ( == ) : 'a -> 'a -> bool
val readReq : unit [@@gen]
val getReq : < va : int > [@@obs]
val readRsp : < va : int > [@@obs]
val writeReq : < va : int > [@@gen]
val putReq : < va : int > [@@obs]
val putRsp : < va : int ; stat : bool > [@@obs]
val writeRsp : < va : int ; stat : bool > [@@obs]
val commit : unit [@@obs]
val abort : unit [@@obs]

let readReq = (allA, ReadReq true, allA)

let getReq =
  [|
    (allA, GetReq true, ReadRsp true);
    (starA (anyA - Commit true), GetReq true, parallel [| ReadRsp (va == -1) |]);
  |]

let readRsp ?l:(x = (true : [%v: int])) = (allA, ReadRsp true, allA)

let writeReq ?l:(x = (true : [%v: int])) =
  (allA, WriteReq (va == x), parallel [| PutReq (va == x) |])

let putReq ?l:(x = (true : [%v: int])) =
  (allA, PutReq (va == x), parallel [| PutRsp (va == x) |])

let putRsp =
  [|
    (fun ?l:(x = (true : [%v: int])) ?l:(s = (v : [%v: bool])) ->
      ( allA,
        PutRsp (va == x && stat == s),
        parallel [| WriteRsp (va == x && stat == s); Commit true |] ));
    (fun ?l:(x = (true : [%v: int])) ?l:(s = (not v : [%v: bool])) ->
      ( allA,
        PutRsp (va == x && stat == s),
        parallel [| WriteRsp (va == x && stat == s); Abort true |] ));
  |]

let[@goal] readAfterWrite (x : int) (y : int) =
  not
    (allA;
     WriteRsp (va == x && stat);
     starA (anyA - WriteRsp stat);
     ReadRsp (va == y && not (y == x));
     starA (anyA - ReadRsp true - WriteRsp true))
