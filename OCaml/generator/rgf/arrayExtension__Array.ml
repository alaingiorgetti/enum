let copy (a: (Z.t) array) (b: (Z.t) array) : unit =
  let o = Z.sub (Z.of_int (Array.length a)) Z.one in
  let o1 = Z.zero in
  let rec for_loop_to8 i6 =
    if Z.leq i6 o
    then begin
      b.(Z.to_int i6) <- a.(Z.to_int i6);
      for_loop_to8 (Z.succ i6)
    end
  in for_loop_to8 o1

