spec axStartTxn (id: tGid) (k: tKey) (v: tVal) {
  atom (req: eStartTxnReq) :: true ;
  atom (rsp: eStartTxnRsp) :: true ;
  regex (not ((. - req)* ~ rsp ~ (.*)))
  }

spec axReadReq (id: tGid) (k: tKey) (v: tVal) {
  atom (req: eReadReq) :: #gid == id && #key == k ;
  atom (rsp: eReadRsp) :: #gid == id && #key == k ;
  regex not ((. - req)* ~ rsp ~.*)                      ;
}

spec axUpdate (id: tGid) (k: tKey) (v: tVal) {
  atom (req: eUpdateReq) :: #gid == id && #key == k && #val == v ;
  atom (rsp: eUpdateRsp) :: #gid == id && #key == k && #val == v ;
  regex not ((. - req)* ~ rsp ~.*)                                     ;
  }

spec axProvenanceGid (id: tGid) (k: tKey) (v: tVal) {
  atom (getid: eStartTxnRsp) :: #gid == id          ;
  atom (useid: eReadReq | eUpdateReq) :: #gid == id ;
  regex not ((. - getid)* ~ useid ~.*)                    ;
  }

spec lastUpdate (id: tGid) (k: tKey) (v: tVal) {
  atom (update: eUpdateRsp) :: #gid == id && #key == k && #val == v ;
  atom (otherUpdate: eUpdateRsp) :: #gid == id && #key == k         ;
  regex .* ~ update ~ (. - otherUpdate)*                                  ;
  }

spec readActive (id1: tGid) (k1: tKey) (v1: tVal) {
  atom (wrongRead: eReadRsp) :: #gid == id1 && #key == k1 && not (#val == v1) ;
  regex not (.* ~ (lastUpdate id1 k1 v1) ~ wrongRead ~ .*) ;
  }

generator Client {
    scope [| eStartTxnReq eStartTxnRsp eReadReq eReadRsp eUpdateReq eUpdateRsp |] ;
    axiom [| axStartTxn axReadReq axUpdate axProvenanceGid |] ;
    config [| tKey tVal |]                                    ;
    violation readActive                                      ;
    step 7                                                    ;
  }
