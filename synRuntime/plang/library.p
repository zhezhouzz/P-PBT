event error;

fun set_is_empty(s: set[any]): bool {
  return 0 == sizeof(s);
}

fun intersection (s1: set[string], s2: seq[string]): set[string] {
  var res: set[string];
  var elem: string;
  res = s1;
  foreach (elem in s1) {
    if (!(elem in s2)) {
      res -= (elem);
    }
  }
  return res;
}

fun mk_index_set (s: seq[any]): set[int] {
  var index: int;
  var res: set[int];
  var elem: any;
  index = 0;
  foreach (elem in s) {
    res += (index);
    index = index + 1;
  }
  return res;
}

fun mk_machine_set (s: seq[machine]): set[machine] {
  var res: set[machine];
  var elem: machine;
  foreach (elem in s) {
    res += (elem);
  }
  return res;
}

fun mk_machine_seq (s: set[machine]): seq[machine] {
  var res: seq[machine];
  var elem: machine;
  foreach (elem in s) {
    res += (0, elem);
  }
  return res;
}

fun mk_int_set_from_bound (bound: int) : set[int] {
  var elem: int;
  var res: set[int];
  elem = 0;
  while(elem <= bound) {
    res += (elem);
    elem = elem + 1;
  }
  return res;
}

fun mk_total_int_set () : set[int] {
  return mk_int_set_from_bound(1999);
}

fun int_set_union(a: set[int], b: set[int]): set[int] {
  var res: set[int];
  var elem: int;
  foreach (elem in a) {
    res += (elem);
  }
  foreach (elem in b) {
    res += (elem);
  }
  return res;
}

fun mk_total_bool_set () : set[bool] {
  var res: set[bool];
  res += (true);
  res += (false);
  return res;
}

fun seq_int_to_set (s: seq[int]): set[int] {
  var elem: int;
  var res: set[int];
  foreach (elem in s) {
    res += (elem);
  }
  return res;
}

fun seq_string_to_set (s: seq[string]): set[string] {
  var elem: string;
  var res: set[string];
  foreach (elem in s) {
    res += (elem);
  }
  return res;
}

fun intersection_set (s1: set[string], s2: set[string]): set[string] {
  var res: set[string];
  var elem: string;
  res = s1;
  foreach (elem in s1) {
    if (!(elem in s2)) {
      res -= (elem);
    }
  }
  return res;
}

fun set_int_from_range (min: int, max: int): set[int] {
  var elem: int;
  var res: set[int];
  elem = min;
  while (elem < max) {
    res += (elem);
    elem = elem + 1;
  }
  return res;
}