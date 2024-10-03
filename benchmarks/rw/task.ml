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

let readReq = (starA anyA, ReadReq true, starA anyA)

let getReq ?l:(x = (true : [%v: int])) =
  (starA anyA, GetReq true, ReadRsp (va == x))
