let rec to_list : type a. (a array) -> (Z.t) -> (Z.t) ->  (a list) =
  fun a l u -> if Z.leq u l
               then []
               else a.(Z.to_int l) :: to_list a (Z.add l Z.one) u

