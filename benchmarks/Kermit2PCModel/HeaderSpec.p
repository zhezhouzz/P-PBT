type tTime = int;
type tMonitorRouterTxnStatus = (gid: tGid, participants: set[machine], status: tTxnStatus, commit_time: tTime);
event eMonitorRouterTxnStatus: tMonitorRouterTxnStatus;
enum tShardPrepareStatus {
    SHARD_OK,
    SHARD_ABORT
}
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
type tStartTxnReq = (client: machine);
event eStartTxnReq: tStartTxnReq;
type tStartTxnRsp = (router: machine, gid: tGid, start_time: tTime);
event eStartTxnRsp: tStartTxnRsp;
type tReadReq = (gid: tGid, key: tKey);
event eReadReq: tReadReq;
type tReadRsp = (router: machine, gid: tGid, key: tKey, val: tVal, status: tCmdStatus);
event eReadRsp: tReadRsp;
type tUpdateReq = (gid: tGid, key: tKey, val: tVal);
event eUpdateReq: tUpdateReq;
type tUpdateRsp = (router: machine, gid: tGid, key: tKey, val: tVal, status: tCmdStatus);
event eUpdateRsp: tUpdateRsp;
type tCommitTxnReq = (gid: tGid);
event eCommitTxnReq: tCommitTxnReq;
type tCommitTxnRsp = (gid: tGid, status: tTxnStatus);
event eCommitTxnRsp: tCommitTxnRsp;
type tRollbackTxnReq = (gid: tGid);
event eRollbackTxnReq: tRollbackTxnReq;
type tShardPrepareRsp = (shard: machine, gid: tGid, status: tShardPrepareStatus, prepare_time: tTime);
event eShardPrepareRsp: tShardPrepareRsp;
type tShardCommitTxn = (gid: tGid, commit_time: tTime);
event eShardCommitTxn: tShardCommitTxn;
type tShardAbortTxn = (gid: tGid);
event eShardAbortTxn: tShardAbortTxn;
type tLeadShardCommitReq = (router: machine, gid: tGid, max_prepare_time: tTime, participants: set[machine]);
event eLeadShardCommitReq: tLeadShardCommitReq;
type tLeadShardCommitRsp = (shard: machine, gid: tGid, status: tTxnStatus, commit_time: tTime);
event eLeadShardCommitRsp: tLeadShardCommitRsp;

REQ StartTxnReq = eStartTxnReq;
RSP StartTxnRsp = eStartTxnRsp: (gid: tGid, start_time: tTime);
REQRSP StartTxnReq StartTxnRsp                                ;

REQ ReadReq = eReadReq: (gid: tGid, key: tKey);
RSP ReadRsp = eReadRsp: (gid: tGid, key: tKey, val: tVal, status: tCmdStatus);
REQRSP ReadReq ReadRsp                                                       ;

REQ UpdateReq = eUpdateReq: (gid: tGid, key: tKey, val: tVal);
RSP UpdateRsp = eUpdateRsp: (gid: tGid, key: tKey, val: tVal, status: tCmdStatus);
REQRSP UpdateReq UpdateRsp      ;

REQ CommitTxnReq = eCommitTxnReq: (gid: tGid);
RSP CommitTxnRsp = eCommitTxnRsp: (gid: tGid, status: tTxnStatus);
REQRSP CommitTxnReq CommitTxnRsp                                 ;

REQ RollbackTxnReq = eRollbackTxnReq: (gid: tGid);

/* the client don't need to know the number of shard (assume there is only one), thus the shard field is omitted. */
HIDDEN MonitorRouterTxnStatus = eMonitorRouterTxnStatus: (gid: tGid, status: tTxnStatus, commit_time: tTime);
HIDDEN LeadShardCommitRsp = eLeadShardCommitRsp: (gid: tGid, commit_time: tTime); /* the status can only be COMMITTED */
HIDDEN ShardCommitTxn = eShardCommitTxn: (gid: tGid, commit_time: tTime);
HIDDEN ShardAbortTxn = eShardAbortTxn: (gid: tGid);
HIDDEN ShardPrepareRsp = eShardPrepareRsp: (gid: tGid, status: tShardPrepareStatus, prepare_time: tTime) ;
HIDDEN LeadShardCommitReq = eLeadShardCommitReq: (gid: tGid);
