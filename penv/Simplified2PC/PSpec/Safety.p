spec strong_consistenty
observes readRsp, writeRsp
{
  var store: int;
  var is_init: bool;
  start state StartUp {
    entry {
      is_init = false;
    }

    on writeRsp do (input: (va: int, stat: bool)) {
      if (input.stat) {
        store = input.va;
        is_init = true;
      } 
    }

    on readRsp do (input: (va: int)) {
      if (is_init) {
        assert (store == input.va), "spec violation";
      }
    }
  }
}