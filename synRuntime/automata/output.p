machine Client {
  var action_domain: seq[string];
  var transitions: map[int, map[string, map[int, int]]];
  var world: map[int, map[int, int]];
  var server_Domain: seq[int];
  var key_Domain: seq[int];
  var fuel: int;
  state Init  {
    entry (s: int) = {
      fuel = s;
      return ;
    }

    on writeResp do (s: int) = {
      fuel = (s + 1);
      return ;
    }

  }
  state Loop  {
    entry (s: int) = {
      fuel = (s + 5);
      return ;
    }

    on writeResp do (a: int) = {
      fuel = 1;
      goto Loop;
    }

  }
  fun action_domain_init () = {
    action_domain += ("write");
    action_domain += ("read");
    return ;
  }
  fun get_available_actions (): seq[string] = {
    var res: seq[string];
    res = action_domain;
    foreach ((serv, _w!4) in world) {
      foreach ((y, _w!5) in _w!4) {
        res = intersection(res, keys(transitions[_w!5]));
      };
    };
    return res;
  }
  fun validate_write (serv: int,y: int,m: map[int, int],input: (x_0: server, x_1: key, x_2: int)): (bool, int) = {
    var next_state: int;
    var if_valid: bool;
    if_valid = false;
    if (prop_write_0(serv, y, input)) {
      next_state = m[0];
      if_valid = true;
    };
    if (prop_write_1(serv, y, input)) {
      next_state = m[1];
      if_valid = true;
    };
    if (prop_write_2(serv, y, input)) {
      next_state = m[2];
      if_valid = true;
    };
    return (if_valid, next_state);
  }
  fun validate_read (serv: int,y: int,m: map[int, int],input: (x_0: server, x_1: key)): (bool, int) = {
    var next_state: int;
    var if_valid: bool;
    if_valid = false;
    if (prop_read_0(serv, y, input)) {
      next_state = m[0];
      if_valid = true;
    };
    return (if_valid, next_state);
  }
  fun next_world_write (input: (x_0: server, x_1: key, x_2: int)): bool = {
    var tmp_world: map[int, map[int, int]];
    var if_valid: bool;
    if_valid = true;
    tmp_world = world;
    foreach ((serv, _w!2) in world) {
      foreach ((y, _w!3) in _w!2) {
        res = validate_write(_w!2, _w!3, transitions[_w!3]["write"], input);
        if ((res).0) {
          _w!3 = (res).1;
        } else {
          if_valid = false;
        };
      };
    };
    if (!(if_valid)) {
      world = tmp_world;
    };
    return if_valid;
  }
  fun next_world_read (input: (x_0: server, x_1: key)): bool = {
    var tmp_world: map[int, map[int, int]];
    var if_valid: bool;
    if_valid = true;
    tmp_world = world;
    foreach ((serv, _w!0) in world) {
      foreach ((y, _w!1) in _w!0) {
        res = validate_read(_w!0, _w!1, transitions[_w!1]["read"], input);
        if ((res).0) {
          _w!1 = (res).1;
        } else {
          if_valid = false;
        };
      };
    };
    if (!(if_valid)) {
      world = tmp_world;
    };
    return if_valid;
  }
  fun transition_init_function () = {
    transitions = default(map[int, map[string, map[int, int]]]);
    transitions[4] = default(map[string, map[int, int]]);
    transitions[4]["write"] = default(map[int, int]);
    transitions[4]["write"][0] = 4;
    transitions[3] = default(map[string, map[int, int]]);
    transitions[3]["write"] = default(map[int, int]);
    transitions[3]["write"][1] = 4;
    transitions[3]["read"] = default(map[int, int]);
    transitions[3]["read"][0] = 4;
    transitions[2] = default(map[string, map[int, int]]);
    transitions[2]["write"] = default(map[int, int]);
    transitions[2]["write"][1] = 3;
    transitions[2]["read"] = default(map[int, int]);
    transitions[2]["read"][0] = 3;
    transitions[1] = default(map[string, map[int, int]]);
    transitions[1]["write"] = default(map[int, int]);
    transitions[1]["write"][1] = 2;
    transitions[1]["read"] = default(map[int, int]);
    transitions[1]["read"][0] = 2;
    transitions[0] = default(map[string, map[int, int]]);
    transitions[0]["write"] = default(map[int, int]);
    transitions[0]["write"][2] = 1;
  }
  fun prop_write_2 (serv: int,y: int,input: (x_0: server, x_1: key, x_2: int)): bool = {
    var x_0: server;
    var x_1: key;
    var x_2: int;
    x_0 = (input).x_0;
    x_1 = (input).x_1;
    x_2 = (input).x_2;
    return ((((x_1 == y) && !((x_1 != y))) && (x_0 == serv)) && (((x_1 == y) && (x_1 != y)) && (x_0 == serv)));
  }
  fun prop_write_1 (serv: int,y: int,input: (x_0: server, x_1: key, x_2: int)): bool = {
    var x_0: server;
    var x_1: key;
    var x_2: int;
    x_0 = (input).x_0;
    x_1 = (input).x_1;
    x_2 = (input).x_2;
    return (((((((((!((x_1 == y)) && !((x_1 != y))) && !((x_0 == serv))) && (((x_1 == y) && !((x_1 != y))) && !((x_0 == serv)))) && ((!((x_1 == y)) && !((x_1 != y))) && (x_0 == serv))) && (((x_1 == y) && !((x_1 != y))) && (x_0 == serv))) && ((!((x_1 == y)) && (x_1 != y)) && !((x_0 == serv)))) && (((x_1 == y) && (x_1 != y)) && !((x_0 == serv)))) && ((!((x_1 == y)) && (x_1 != y)) && (x_0 == serv))) && (((x_1 == y) && (x_1 != y)) && (x_0 == serv)));
  }
  fun prop_write_0 (serv: int,y: int,input: (x_0: server, x_1: key, x_2: int)): bool = {
    var x_0: server;
    var x_1: key;
    var x_2: int;
    x_0 = (input).x_0;
    x_1 = (input).x_1;
    x_2 = (input).x_2;
    return (((!((x_1 == y)) && (x_1 != y)) && (x_0 == serv)) && (((x_1 == y) && (x_1 != y)) && (x_0 == serv)));
  }
  fun prop_read_0 (serv: int,y: int,input: (x_0: server, x_1: key)): bool = {
    var x_0: server;
    var x_1: key;
    x_0 = (input).x_0;
    x_1 = (input).x_1;
    return (!((x_0 == serv)) && (x_0 == serv));
  }
  fun world_init_function () = {
    foreach (serv in server_Domain) {
      foreach (y in key_Domain) {
        world[serv][y] = 0;
      };
    };
  }
  fun qtype_init_function (_server_Domain: seq[int],_key_Domain: seq[int]) = {
    server_Domain = _server_Domain;
    key_Domain = _key_Domain;
    return ;
  }
  fun randomEvent2 (actions: seq[action]): bool = {
    return ((1 + 3) > 4);
  }
}

