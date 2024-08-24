/*
    Client machine issues write txn (one at a time) to a randomly-selected router.
    On receiving a response from the router, confirms the write by sending a
    read txn and checking the read value.
    Client can alsp rollback a write txn request.
*/

enum tTxnStatus {
  ERROR,
  ACTIVE,
  COMMITTED,
  ABORTED
}

enum tCmdStatus {
  UNKNOWN,
  OK,
  ABORT
}

type tGid = int;
type tKey = int;
type tVal = int;

event {
  request eStartTxnReq: (client: machine);
  response eStartTxnRsp: (router: machine, gid: tGid, start_time: tTime);
}

event {
  request eReadReq: (gid: tGid, key: tKey);
  response eReadRsp: (router: machine, gid: tGid, key: tKey, val: tVal, status: tCmdStatus);
}

event {
  request tUpdateReq: (gid: tGid, key: tKey, val: tVal);
  response eUpdateRsp: (router: machine, gid: tGid, key: tKey, val: tVal, status: tCmdStatus);
}

event {
  request tCommitTxnReq: (gid: tGid);
  response eCommitTxnRsp: (gid: tGid, status: tTxnStatus);
}

event {
  request tRollbackTxnReq: (gid: tGid);
}

/* the client don't need to know the number of shard (assume there is only one), thus the shard field is omitted. */
hidden eMonitorRouterTxnStatus: (gid: tGid, status: tTxnStatus, commit_time: tTime);
hidden eLeadShardCommitRsp: (gid: tGid, commit_time: tTime); /* the status can only be COMMITTED */
hidden eShardCommitTxn: (gid: tGid, commit_time: tTime);
hidden eShardAbortTxn: (gid: tGid);
hidden eShardPrepareRsp = (gid: tGid, status: tShardPrepareStatus, prepare_time: tTime)
hidden eLeadShardCommitReq: (gid: tGid);
hidden eLeadShardCommitRsp: (gid: tGid, status: tTxnStatus, commit_time: tTime) ;


/* can be an axiom */
spec eStartTxnRspOnce (gid: tGid) {
  atom (a: eStartTxnRsp) :: #gid == gid
  regex not (.* ~ a ~ .* ~ a ~ .*)
  }

/* can be an axiom */
spec eLeadShardCommitRspOnce (gid: tGid) {
  atom (a: eLeadShardCommitRsp) :: #gid == gid
  regex not (.* ~ a .* a ~ .*)
  }

/* can be an axiom */
spec eMonitorRouterTxnStatus (gid: tGid) {
  atom (a: eMonitorRouterTxnStatus) :: #gid == gid
  regex not (.* ~ a .* a ~ .*)
  }

/* A1. If a txn is reported as committed to a client, then the router/lead-participant committed the txn. */
spec LeadAtomicity1 (gid: tGid) {
  atom (a: eCommitTxnRsp) :: #gid == gid && status == COMMITTED
  atom (b: eLeadShardCommitRsp) :: #gid == gid
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A1. If a txn is reported as committed to a client, then the router/lead-participant committed the txn. */
spec RounterAtomicity1 (gid: tGid) {
  atom (a: eCommitTxnRsp) :: #gid == gid && status == COMMITTED
  atom (b: eMonitorRouterTxnStatus) :: #gid == gid && status == COMMITTED
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A2. If a txn is reported as aborted to a client, then the router aborted the txn. */
spec Atomicity2 (gid: tGid) {
  atom (a: eCommitTxnRsp) :: #gid == gid && status == ABORTED
  atom (b: eMonitorRouterTxnStatus) :: #gid == gid && status == ABORTED
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A3. If a txn is committed by the router/lead-participant, then it was agreed on by all relevant shards. */
spec LeadAtomicity3 (gid: tGid) {
  atom (a: eLeadShardCommitReq) :: #gid == gid
  atom (b: eShardPrepareRsp) :: #gid == gid && status == SHARD_OK
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A3. If a txn is committed by the router/lead-participant, then it was agreed on by all relevant shards. */
spec RounterAtomicity3 (gid: tGid) {
  atom (a: eMonitorRouterTxnStatus) :: #gid == gid
  atom (b: eShardPrepareRsp) :: #gid == gid && status == SHARD_OK
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A4. If a txn is committed at a shard, then router/lead-participant has committed the txn. */
spec LeadAtomicity4 (gid: tGid) {
  atom (a: eShardCommitTxn) :: #gid == gid
  atom (b: eLeadShardCommitRsp) :: #gid == gid && status == COMMITTED
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A3. If a txn is committed at a shard, then router/lead-participant has committed the txn. */
spec RounterAtomicity4 (gid: tGid) {
  atom (a: eShardCommitTxn) :: #gid == gid
  atom (b: eMonitorRouterTxnStatus) :: #gid == gid && status == COMMITTED
  regex not ((. \ b)* ~ a ~ .*)
  }

/* A5. If a txn is aborted at a shard, then router has aborted the txn. */
spec RounterAtomicity5 (gid: tGid) {
  atom (a: eShardAbortTxn) :: #gid == gid
  atom (b: eMonitorRouterTxnStatus) :: #gid == gid && status == ABORTED
  regex not ((. \ b)* ~ a ~ .*)
  }
