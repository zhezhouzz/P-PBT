val readReq : unit [@@gen]
val readRsp : < va : int > [@@obsRecv]
val writeReq : < va : int > [@@gen]
val writeRsp : < va : int ; stat : bool > [@@obsRecv]
