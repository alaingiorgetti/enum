let rec to_list (a: (Z.t) array) (l1: Z.t) (u: Z.t) : (Z.t) list =
  if Z.leq u l1 then []  else a.(Z.to_int l1) :: to_list a (Z.add l1 Z.one) u

