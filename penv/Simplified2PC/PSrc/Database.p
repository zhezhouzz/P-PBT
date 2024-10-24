machine Database
{
  var store: int;
  var buffer: int;

  start state WaitForRequests {
    entry {
      store = -1;
    }

    on putReq do (input: (src: machine, va: int)) {
      var res: (va: int, stat: bool); 
      if($){
        buffer = input.va;
        res.va = input.va;
        res.stat = true;   
      } else {
        res.va = input.va;
        res.stat = false;
      }
      send input.src, putRsp, res;
    }

    on getReq do (input: (src: machine)) {
      var res: (va: int);
      res.va = store; 
      send input.src, readRsp, res;
    }

    on commit do {
      store = buffer;
      buffer = -1;
    }

    on abort do {
      buffer = -1;
    }
  }
}


