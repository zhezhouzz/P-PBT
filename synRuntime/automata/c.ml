let[@regex] a1 = ctx [| a; b; c |] (starA anyA - starA a - starA b)
