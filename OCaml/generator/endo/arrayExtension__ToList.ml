let rec to_list (a: (Z.t) array) (l: Z.t) (u: Z.t) : (Z.t) list =
  if Z.leq u l then []  else a.(Z.to_int l) :: to_list a (Z.add l Z.one) u

