spec lastUpdate (id: tGid) (k: tKey) (v: tVal) {
  atom (update: UpdateRsp) :: #gid == id && #key == k && #val == v;
  atom (otherUpdate: UpdateRsp) :: #gid == id && #key == k;
  regex .* ~ update ~ (. \ otherUpdate)*;
  }

spec readActive (id1: tGid) (k1: tKey) (v1: tVal) {
  atom (wrongRead: ReadRsp) :: #gid == id1 && #key == k1 && not (#val == v1);
  regex not (.* ~ (lastUpdate id1 k1 v1) ~ wrongRead ~ .*);
  }

spec axStartTxn (id: tGid) (k: tKey) (v: tVal) {
  atom (req: StartTxnReq) :: true;
  atom (rsp: StartTxnRsp) :: true;
  regex (not ((. \ req)* ~ rsp ~ (.*)))
  }

spec axReadReq (id: tGid) (k: tKey) (v: tVal) {
  atom (req: ReadReq) :: #gid == id && #key == k;
  atom (rsp: ReadRsp) :: #gid == id && #key == k;
  regex not ((. \ req)* ~ rsp ~.*);
}

spec axUpdate (id: tGid) (k: tKey) (v: tVal) {
  atom (req: UpdateReq) :: #gid == id && #key == k && #val == v;
  atom (rsp: UpdateRsp) :: #gid == id && #key == k && #val == v;
  regex not ((. \ req)* ~ rsp ~.*);
  }

spec axProvenanceGid (id: tGid) (k: tKey) (v: tVal) {
  atom (getid: StartTxnRsp) :: #gid == id;
  atom (useid: ReadReq | UpdateReq) :: #gid == id ;
  regex not ((. \ getid)* ~ useid ~.*);
  }

generator SynClient {
    scope = [StartTxnReq, StartTxnRsp, ReadReq, ReadRsp, UpdateReq, UpdateRsp];
    axiom = [axStartTxn, axReadReq, axUpdate, axProvenanceGid];
    config = [tKey, tVal];
    violation = readActive;
    step = 6;
  }
