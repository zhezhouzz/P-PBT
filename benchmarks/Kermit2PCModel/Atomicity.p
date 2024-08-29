/*
    Client machine issues write txn (one at a time) to a randomly-selected router.
    On receiving a response from the router, confirms the write by sending a
    read txn and checking the read value.
    Client can alsp rollback a write txn request.
*/

/* can be an axiom */
spec eStartTxnRspOnce (gid1: tGid) {
  atom (a: StartTxnRsp) :: #gid == gid1;
  regex not (.* ~ a ~ .* ~ a ~ .*)
  }

/* can be an axiom */
spec eLeadShardCommitRspOnce (gid1: tGid) {
  atom (a: LeadShardCommitRsp) :: #gid == gid1;
  regex not (.* ~ a ~ .* ~ a ~ .*)
  }

/* can be an axiom */
spec eMonitorRouterTxnStatus (gid1: tGid) {
  atom (a: MonitorRouterTxnStatus) :: #gid == gid1;
  regex not (.* ~ a ~ .* ~ a ~ .*)
  }

/* A1. If a txn is reported as committed to a client, then the router/lead-participant committed the txn. */
spec LeadAtomicity1 (gid1: tGid) {
  atom (a: CommitTxnRsp) :: #gid == gid1 && #status == (COMMITTED: tTxnStatus);
  atom (b: LeadShardCommitRsp) :: #gid == gid1;
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A1. If a txn is reported as committed to a client, then the router/lead-participant committed the txn. */
spec RounterAtomicity1 (gid1: tGid) {
  atom (a: CommitTxnRsp) :: #gid == gid1 && #status == (COMMITTED: tTxnStatus);
  atom (b: MonitorRouterTxnStatus) :: #gid == gid1 && #status == (COMMITTED: tTxnStatus);
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A2. If a txn is reported as aborted to a client, then the router aborted the txn. */
spec Atomicity2 (gid1: tGid) {
  atom (a: CommitTxnRsp) :: #gid == gid1 && #status == (ABORTED: tTxnStatus);
  atom (b: MonitorRouterTxnStatus) :: #gid == gid1 && #status == (ABORTED: tTxnStatus);
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A3. If a txn is committed by the router/lead-participant, then it was agreed on by all relevant shards. */
spec LeadAtomicity3 (gid1: tGid) {
  atom (a: LeadShardCommitReq) :: #gid == gid1;
  atom (b: ShardPrepareRsp) :: #gid == gid1 && #status == (SHARD_OK: tShardPrepareStatus );
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A3. If a txn is committed by the router/lead-participant, then it was agreed on by all relevant shards. */
spec RounterAtomicity3 (gid1: tGid) {
  atom (a: MonitorRouterTxnStatus) :: #gid == gid1;
  atom (b: ShardPrepareRsp) :: #gid == gid1 && #status == (SHARD_OK: tShardPrepareStatus );
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A4. If a txn is committed at a shard, then router/lead-participant has committed the txn. */
spec LeadAtomicity4 (gid1: tGid) {
  atom (a: ShardCommitTxn) :: #gid == gid1;
  atom (b: LeadShardCommitRsp) :: #gid == gid1;
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A3. If a txn is committed at a shard, then router/lead-participant has committed the txn. */
spec RounterAtomicity4 (gid1: tGid) {
  atom (a: ShardCommitTxn) :: #gid == gid1;
  atom (b: MonitorRouterTxnStatus) :: #gid == gid1 && #status == (COMMITTED: tTxnStatus);
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A5. If a txn is aborted at a shard, then router has aborted the txn. */
spec RounterAtomicity5 (gid1: tGid) {
  atom (a: ShardAbortTxn) :: #gid == gid1;
  atom (b: MonitorRouterTxnStatus) :: #gid == gid1 && #status == (ABORTED: tTxnStatus);
  regex not ((. \ b)* ~ a ~ .*)
  }

spec dummyAx (id: tGid) {
  regex .*
}
  
spec dummy (id: tGid) {
  regex . ~ . ~ .
}
  
generator SynClient {
    scope = [MonitorRouterTxnStatus, LeadShardCommitRsp, ShardCommitTxn, StartTxnReq, StartTxnRsp, ReadReq, ReadRsp, UpdateReq, UpdateRsp];
    axiom = [dummyAx];
    config = [tKey, tVal];
    violation = dummy;
    step = 3;
}