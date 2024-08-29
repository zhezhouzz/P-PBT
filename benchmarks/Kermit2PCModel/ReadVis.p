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

/*
    This spec model validates the following propery for MVCC
    R1. The successfully read response to the client should either
        a. return the write_buff value in the active txn if key exists in write_buff
        b. or else return the committed value whose commit time is the latest time less than the snapshot time.
    R2. If the router commits a txn, there should not be any already committed version whose commit time is greater than or equal to this txn's commit time.
    R3. Commit time of a txn is higher than all shard prepare times of that txn.
*/

spec lastUpdate (id: tGid) (k: tKey) (v: tVal) {
  atom (update: UpdateRsp) :: #gid == id && #key == k && #val == v;
  atom (otherUpdate: UpdateRsp) :: #gid == id && #key == k;
  regex .* ~ update ~ (. \ otherUpdate)*;
}

/* R1.a */
spec readActive (id1: tGid) (k1: tKey) (v1: tVal) {
  atom (wrongRead: ReadRsp) :: #gid == id1 && #key == k1 && not (#val == v1);
  regex not ((lastUpdate id1 k1 v1) ~ wrongRead ~ .*)
}

spec lastVersionTime (id1: tGid) (k1: tKey) (v1: tVal) (t1: tTime) (t2: tTime) {
  atom (lastCommit: MonitorRouterTxnStatus) :: #gid == id1 && #status == (COMMITTED: tTxnStatus) && #commit_time == t1;
  atom (laterCommit: MonitorRouterTxnStatus) :: (t1 < #commit_time) && (#commit_time < t2);
  regex (. \ laterCommit)* ~ lastCommit ~ (. \ laterCommit)* 
}

spec lastVersionConflict (id1: tGid) (k1: tKey) (v1: tVal) (t2: tTime) {
  atom (a: StartTxnRsp) :: #gid == id1 && #start_time == t2;
  atom (b: ReadRsp) :: #gid == id1 && #status == (OK: tCmdStatus) && #key == k1 && not(#val == v1);
  regex (.* ~ a ~ .* ~ .* ~ b ~ .*)
}

/* R1.b */
spec readNonActive (id1: tGid) (k1: tKey) (v1: tVal) (t1: tTime) (t2: tTime) {
  regex not ((lastUpdate id1 k1 v1) && (lastVersionTime id1 k1 v1 t1 t2) && (lastVersionConflict id1 k1 v1 t2)); 
}

spec committedTxn (id1: tGid) (t1: tTime) {
  atom (a: MonitorRouterTxnStatus) :: #gid == id1 && #status == (COMMITTED: tTxnStatus) && #commit_time == t1;
  regex .* ~ a ~ .*
}

spec updatedKey (id1: tGid) (k1: tKey) {
  atom (a: UpdateRsp) :: #gid == id1 && #key == k1;
  regex .* ~ a ~ .*
}

/* R2 */
spec commitTimeIncreasing (id1: tGid) (id2: tGid) (k1: tKey) (t1: tTime) {
  atom (a: MonitorRouterTxnStatus) :: #gid == id1 && #status == (COMMITTED: tTxnStatus) && #commit_time < t1;
  regex not (((committedTxn id1 t1) && (updatedKey id1 k1) && (updatedKey id2 k1)) ~ .* ~ a ~ .*)
}

/* R3 */
spec ShardTimeSafety (id1: tGid) (t1: tTime) {
  atom (a: ShardPrepareRsp) :: #gid == id1 && #status == (SHARD_OK: tShardPrepareStatus) && #prepare_time > t1;
  atom (b: MonitorRouterTxnStatus) :: #gid == id1 && #commit_time == t1;
  regex not (.* ~ a ~ .* ~ b ~ .*)
}

generator SynClient {
  scope = [StartTxnReq, StartTxnRsp, ReadReq, ReadRsp, UpdateReq, UpdateRsp];
  axiom = [axStartTxn, axReadReq, axUpdate, axProvenanceGid];
  config = [tKey, tVal];
  violation = readActive;
  step = 6;
}