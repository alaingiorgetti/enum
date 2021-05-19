let b_comb (a: (Z.t) array) (k2: Z.t) : bool =
  if Z.leq k2 Z.zero
  then false
  else Barray__Barray.b_barray a k2 && ArrayExtension__Inc.b_inc a

