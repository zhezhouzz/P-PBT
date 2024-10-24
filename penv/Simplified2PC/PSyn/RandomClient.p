machine RandomClient {
    var counter: int;
    var timer: Timer;
    var setting: machine;
    var domain_int: set[int];
    var bound: int;
    start state Syn {
      entry (input: (setting: machine, domain_int: set[int], bound: int)) {
        timer = CreateTimer(this);
        counter = 0;
        setting = input.setting;
        domain_int = input.domain_int;
        bound = input.bound;
        goto Do;        
      }

      ignore readRsp, writeRsp;
    }

    state Do {
        entry {
            if (counter < bound) {
                StartTimer(timer);
            }
        } 

        on eTimeOut do {
            counter = counter + 1;
            if ($) {
                send_writeReq(this, setting, (va = choose(domain_int),)); 
            } else {
                send_readReq(this, setting);
            }
            goto Do;
        }
        ignore readRsp, writeRsp;
    }
  }
  
  