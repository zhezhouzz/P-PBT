machine SynClient {
  start state Syn {
    entry (input: (setting: machine, domain_bool: set[bool], domain_tGid: set[int], domain_tKey: set[int], domain_tVal: set[int], domain_tCmdStatus: set[tCmdStatus], domain_tTxnStatus: set[tTxnStatus])) {
      var setting: machine;
      var domain_bool: set[bool];
      var domain_tGid: set[int];
      var domain_tKey: set[int];
      var domain_tVal: set[int];
      var domain_tCmdStatus: set[tCmdStatus];
      var domain_tTxnStatus: set[tTxnStatus];
      var input_eStartTxnRsp: (gid: tGid);
      var id: tGid;
      var k: tKey;
      var v2: tVal;
      var tmp_26: tGid;
      var tmp_27: tKey;
      var tmp_28: tVal;
      var tmp_23: tGid;
      var tmp_24: tKey;
      var tmp_25: tVal;
      var st_26: tCmdStatus;
      var input_eUpdateRsp: (gid: tGid, key: tKey, value: tVal, status: tCmdStatus);
      var tmp_19: tGid;
      var tmp_20: tKey;
      var tmp_21: tVal;
      var tmp_22: tCmdStatus;
      var v1: tVal;
      var tmp_16: tGid;
      var tmp_17: tKey;
      var tmp_18: tVal;
      var tmp_13: tGid;
      var tmp_14: tKey;
      var tmp_15: tVal;
      var st_13: tCmdStatus;
      var tmp_9: tGid;
      var tmp_10: tKey;
      var tmp_11: tVal;
      var tmp_12: tCmdStatus;
      var tmp_7: tGid;
      var tmp_8: tKey;
      var tmp_4: tGid;
      var tmp_5: tKey;
      var tmp_6: tVal;
      var st_0: tCmdStatus;
      var input_eReadRsp: (gid: tGid, key: tKey, value: tVal, status: tCmdStatus);
      var tmp_0: tGid;
      var tmp_1: tKey;
      var tmp_2: tVal;
      var tmp_3: tCmdStatus;
      setting = input.setting;
      domain_bool = input.domain_bool;
      domain_tGid = input.domain_tGid;
      domain_tKey = input.domain_tKey;
      domain_tVal = input.domain_tVal;
      domain_tCmdStatus = input.domain_tCmdStatus;
      domain_tTxnStatus = input.domain_tTxnStatus;
      send_eStartTxnReq(this, setting);
      receive { case eStartTxnRsp: (input: tStartTxnRsp) {
        input_eStartTxnRsp = cast_eStartTxnRsp(input);
        id = input_eStartTxnRsp.gid;
      }};
      assert true;
      while(true){
        k = choose(domain_tKey);
        v2 = choose(domain_tVal);
        if (true) {
          break;
        };
      };
      send_eUpdateReq(this, setting, (gid = id, key = k, value = v2));
      while(true){
        tmp_26 = choose(domain_tGid);
        tmp_27 = choose(domain_tKey);
        tmp_28 = choose(domain_tVal);
        if ((((tmp_26 == id) && (tmp_27 == k)) && (tmp_28 == v2))) {
          break;
        };
      };
      while(true){
        tmp_23 = choose(domain_tGid);
        tmp_24 = choose(domain_tKey);
        tmp_25 = choose(domain_tVal);
        st_26 = choose(domain_tCmdStatus);
        if (((((tmp_23 == id) && (tmp_24 == k)) && (tmp_25 == v2)) && (st_26 == OK))) {
          break;
        };
      };
      receive { case eUpdateRsp: (input: tUpdateRsp) {
        input_eUpdateRsp = cast_eUpdateRsp(input);
        tmp_19 = input_eUpdateRsp.gid;
        tmp_20 = input_eUpdateRsp.key;
        tmp_21 = input_eUpdateRsp.value;
        tmp_22 = input_eUpdateRsp.status;
      }};
      assert ((((tmp_19 == id) && (tmp_20 == k)) && (tmp_21 == v2)) && (tmp_22 == st_26));
      while(true){
        v1 = choose(domain_tVal);
        if (!((v2 == v1))) {
          break;
        };
      };
      send_eUpdateReq(this, setting, (gid = id, key = k, value = v1));
      while(true){
        tmp_16 = choose(domain_tGid);
        tmp_17 = choose(domain_tKey);
        tmp_18 = choose(domain_tVal);
        if ((((tmp_16 == id) && (tmp_17 == k)) && (tmp_18 == v1))) {
          break;
        };
      };
      while(true){
        tmp_13 = choose(domain_tGid);
        tmp_14 = choose(domain_tKey);
        tmp_15 = choose(domain_tVal);
        st_13 = choose(domain_tCmdStatus);
        if ((((((tmp_13 == id) && (tmp_14 == k)) && (tmp_15 == v1)) && (st_26 == st_13)) && (st_13 == OK))) {
          break;
        };
      };
      receive { case eUpdateRsp: (input: tUpdateRsp) {
        input_eUpdateRsp = cast_eUpdateRsp(input);
        tmp_9 = input_eUpdateRsp.gid;
        tmp_10 = input_eUpdateRsp.key;
        tmp_11 = input_eUpdateRsp.value;
        tmp_12 = input_eUpdateRsp.status;
      }};
      assert ((((tmp_9 == id) && (tmp_10 == k)) && (tmp_11 == v1)) && (tmp_12 == st_13));
      send_eReadReq(this, setting, (gid = id, key = k));
      while(true){
        tmp_7 = choose(domain_tGid);
        tmp_8 = choose(domain_tKey);
        if (((tmp_7 == id) && (tmp_8 == k))) {
          break;
        };
      };
      while(true){
        tmp_4 = choose(domain_tGid);
        tmp_5 = choose(domain_tKey);
        tmp_6 = choose(domain_tVal);
        st_0 = choose(domain_tCmdStatus);
        if (((((((tmp_4 == id) && (tmp_5 == k)) && (tmp_6 == v2)) && (st_26 == st_0)) && (st_13 == st_0)) && (st_0 == OK))) {
          break;
        };
      };
      receive { case eReadRsp: (input: tReadRsp) {
        input_eReadRsp = cast_eReadRsp(input);
        tmp_0 = input_eReadRsp.gid;
        tmp_1 = input_eReadRsp.key;
        tmp_2 = input_eReadRsp.value;
        tmp_3 = input_eReadRsp.status;
      }};
      assert ((((tmp_0 == id) && (tmp_1 == k)) && (tmp_2 == v2)) && (tmp_3 == st_0));
    }

  }
}

