let[@regex] a1 =
  starA a;
  b;
  starA (a || b)

let[@regex] b1 =
  starA b;
  a;
  starA (a || b)
