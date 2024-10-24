machine Coordinator
{
  var database: machine;
  var user: machine;
  var timer: Timer;
  var purRsp_buffer: (va: int, stat: bool);
  var is_committed: bool;

  start state WaitForRequests {
    entry (input:(database: machine)){
        database = input.database;
        timer = CreateTimer(this);
    }

    on writeReq do (input: (src: machine, va: int)) {
        user = input.src;
        send database, putReq, (src = this, va = input.va);
    }

    on readReq do (input: (src: machine)) {
        send database, getReq, (src = input.src,);
    }

    on putRsp do (input: (va: int, stat: bool)) {
        // print format("input: {0}", input);
        purRsp_buffer = input;
        if (input.stat) {
            if ($) {
                is_committed = true;
                send database, commit;
            } else {
                is_committed = false;
                send user, writeRsp, purRsp_buffer;
            }
            StartTimer(timer);
        } else {
            send database, abort;
            send user, writeRsp, input;
        }
    }

    on eTimeOut do {
        if (is_committed) {
            send user, writeRsp, purRsp_buffer; 
        } else {
            send database, commit; 
        }
    }
  }
}


