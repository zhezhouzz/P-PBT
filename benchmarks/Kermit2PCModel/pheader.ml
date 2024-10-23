val eStartTxnReq : unit [@@gen]
val eStartTxnRsp : < gid : tGid > [@@obsRecv]
val eReadReq : < gid : tGid ; key : tKey > [@@gen]

val eReadRsp :
  < gid : tGid
  ; key : tKey
  ; value : tVal
  ; status : (uNKNOWN * oK * aBORT[@tCmdStatus]) >
[@@obsRecv]

val eUpdateReq : < gid : tGid ; key : tKey ; value : tVal > [@@gen]

val eUpdateRsp :
  < gid : tGid
  ; key : tKey
  ; value : tVal
  ; status : (uNKNOWN * oK * aBORT[@tCmdStatus]) >
[@@obsRecv]

val eCommitTxnReq : < gid : tGid > [@@gen]

val eCommitTxnRsp :
  < gid : tGid
  ; txnstatus : (eRROR * aCTIVE * cOMMITTED * aBORTED[@tTxnStatus]) >
[@@obsRecv]

val eRollbackTxnReq : < gid : tGid > [@@gen]
