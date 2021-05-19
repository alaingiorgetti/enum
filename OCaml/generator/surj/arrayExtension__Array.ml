let copy (a: (Z.t) array) (b: (Z.t) array) : unit =
  let o = Z.sub (Z.of_int (Array.length a)) Z.one in
  let o1 = Z.zero in
  let rec for_loop_to9 i3 =
    if Z.leq i3 o
    then begin
      b.(Z.to_int i3) <- a.(Z.to_int i3);
      for_loop_to9 (Z.succ i3)
    end
  in for_loop_to9 o1

