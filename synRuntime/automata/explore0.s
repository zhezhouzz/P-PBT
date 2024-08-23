  func "==" : 'a -> 'a -> bool   ;
  enum tTxnStatus = ERROR | ACTIVE | COMMITTED | ABORTED ;
  enum tCmdStatus = UNKNOWN | OK | ABORT                 ;
  type tGid = int              ;
  type tKey = int              ;
  type tVal = int              ;
  type tTime = int             ;

  request event eStartTxnReq: <>;
  response event eStartTxnRsp: <gid: tGid, start_time: tTime>;

  request event eReadReq: < gid: tGid, key: tKey>;
  response event eReadRsp: < gid: tGid, key: tKey, val: tVal, status: tCmdStatus>;

  request event eUpdateReq: < gid: tGid, key: tKey, val: tVal>;
  response event eUpdateRsp: < gid: tGid, key: tKey, val: tVal, status: tCmdStatus>;

  request event eCommitTxnReq: <gid: tGid>;
  response event eCommitTxnRsp: <gid: tGid, status: tTxnStatus>;

  request event eRollbackTxnReq: <gid: tGid> ;

  hidden event eShardReadKeyRsp: <shard: machine, gid: tGid, status: tShardPrepareStatus, prepare_time: tTime>;
  hidden event eShardCommitTxn: <gid: tGid, commit_time: tTime>;
  hidden event eShardAbortTxn: <gid: tGid>;
  hidden event eMonitorRouterTxnStatus: <gid: tGid, participants: bool, status: tTxnStatus, commit_time: tTime>;

  spec ax_eStartTxn (id: tGid) (k: tKey) (v: tVal) =
  not ((. - <[eStartTxnReq| true]>)* ~ <[eStartTxnRsp| true]> ~.*) ;

  spec ax_eReadReq (id: tGid) (k: tKey) (v: tVal) =
  not ((. - <[eReadReq| gid == id && key == k]>)* ~ <[eReadRsp| gid == id && key == k]> ~.*) ;

  spec ax_eUpdate  (id: tGid) (k: tKey) (v: tVal) =
  not ((. - <[eUpdateReq| gid == id && key == k && val == v]>)* ~ <[eUpdateRsp| gid == id && key == k && val == v]> ~.*) ;

  spec ax_provenance_gid (id: tGid) (k: tKey) (v: tVal) =
  not ((. - <[eStartTxnRsp| gid == id]>)* ~ (<[eReadReq| gid == id]> || <[eUpdateReq| gid == id]>) ~.*) ;

  spec has_update (k: tKey) = .* ~ <[eUpdateRsp|  key == k]> ~ .* ;
  spec last_update (id: tGid) (k: tKey) (v: tVal) =
  .* ~ <[eUpdateRsp| gid == id && key == k && val == v]> ~ (. - <[eUpdateRsp| gid == id && key == k ]>)*;

  spec read_active (id1: tGid) (k1: tKey) (v1: tVal) =
  not (.* ~ (last_update id1 k1 v1) ~ <[eReadRsp| gid == id1 && key == k1 && not (val == v1)]> ~ .*);

  client client1 =
    scope [| eStartTxnReq eStartTxnRsp eReadReq eReadRsp eUpdateReq eUpdateRsp |]
    axiom [| ax_eStartTxn ax_eReadReq ax_eUpdate ax_provenance_gid |]
    config [| tKey tVal |]
    violation read_active
    step 9
