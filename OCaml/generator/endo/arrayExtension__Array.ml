let copy (a: (Z.t) array) (b: (Z.t) array) : unit =
  let o = Z.sub (Z.of_int (Array.length a)) Z.one in
  let o1 = Z.zero in
  let rec for_loop_to2 i =
    if Z.leq i o
    then begin b.(Z.to_int i) <- a.(Z.to_int i); for_loop_to2 (Z.succ i) end
  in for_loop_to2 o1

