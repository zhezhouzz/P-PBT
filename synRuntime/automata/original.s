
spec ax_eStartTxn (id: tGid) (k: tKey) (v: tVal) {
  regex not ((. - <[eStartTxnReq| true]>)* ~ <[eStartTxnRsp| true]> ~.*) ;
}

spec ax_eReadReq (id: tGid) (k: tKey) (v: tVal) {
  regex not ((. - <[eReadReq| gid == id && key == k]>)* ~ <[eReadRsp| gid == id && key == k]> ~.*);
}

spec ax_eUpdate (id: tGid) (k: tKey) (v: tVal) {
  regex not ((. - <[eUpdateReq| gid == id && key == k && val == v]>)* ~ <[eUpdateRsp| gid == id && key == k && val == v]> ~.*) ;
}

spec ax_provenance_gid (id: tGid) (k: tKey) (v: tVal) {
  regex not ((. - <[eStartTxnRsp| gid == id]>)* ~ (<[eReadReq| gid == id]> || <[eUpdateReq| gid == id]>) ~.*) ;
  }

spec has_update (k: tKey) {
  regex .* ~ <[eUpdateRsp|  key == k]> ~ .* ;
  }

spec last_update (id: tGid) (k: tKey) (v: tVal) {
  regex .* ~ <[eUpdateRsp| gid == id && key == k && val == v]> ~ (. - <[eUpdateRsp| gid == id && key == k ]>)*;
}

spec read_active (id1: tGid) (k1: tKey) (v1: tVal) {
  regex not (.* ~ (last_update id1 k1 v1) ~ <[eReadRsp| gid == id1 && key == k1 && not (val == v1)]> ~ .*);
}

generator Client1 {
    scope [| eStartTxnReq eStartTxnRsp eReadReq eReadRsp eUpdateReq eUpdateRsp |] ;
    axiom [| ax_eStartTxn ax_eReadReq ax_eUpdate ax_provenance_gid |] ;
    config [| tKey tVal |]                                            ;
    violation read_active                                             ;
    step 7                                                            ;
  }
