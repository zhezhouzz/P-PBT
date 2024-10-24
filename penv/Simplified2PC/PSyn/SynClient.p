machine SynClient {
  start state Syn {
    entry (input: (setting: machine, domain_int: set[int], domain_bool: set[bool])) {
      var setting: machine;
      var domain_int: set[int];
      var domain_bool: set[bool];
      var x: int;
      var tmp_2: int;
      var tmp_1: int;
      var s_8: bool;
      var input_writeRsp: (va: int, stat: bool);
      var tmp_0: int;
      var s_6: bool;
      var input_readRsp: (va: int);
      var y: int;
      setting = input.setting;
      domain_int = input.domain_int;
      domain_bool = input.domain_bool;
      while(true){
        x = choose(domain_int);
        if (!((x == -1))) {
          break;
        };
      };
      send_writeReq(this, setting, (va = x,));
      while(true){
        tmp_2 = choose(domain_int);
        if ((tmp_2 == x)) {
          break;
        };
      };
      while(true){
        tmp_1 = choose(domain_int);
        s_8 = choose(domain_bool);
        if (((tmp_1 == x) && s_8)) {
          break;
        };
      };
      receive { case writeRsp: (input: triteRsp) {
        input_writeRsp = cast_writeRsp(input);
        tmp_0 = input_writeRsp.va;
        s_6 = input_writeRsp.stat;
      }};
      assert ((tmp_0 == x) && s_6);
      send_readReq(this, setting);
      receive { case readRsp: (input: teadRsp) {
        input_readRsp = cast_readRsp(input);
        y = input_readRsp.va;
      }};
      assert (!((y == x)) && (y == -1));
    }

  }
}

