let copy (a: (Z.t) array) (b: (Z.t) array) : unit =
  let o = Z.sub (Z.of_int (Array.length a)) Z.one in
  let o1 = Z.zero in
  let rec for_loop_to7 i5 =
    if Z.leq i5 o
    then begin
      b.(Z.to_int i5) <- a.(Z.to_int i5);
      for_loop_to7 (Z.succ i5)
    end
  in for_loop_to7 o1

