let b_barray (a: (Z.t) array) (b: Z.t) : bool =
  let exception QtReturn3 of (bool) in
  try
    (let o = Z.sub (Z.of_int (Array.length a)) Z.one in let o1 = Z.zero in
     let rec for_loop_to5 i =
       if Z.leq i o
       then begin
         if not (let q1_ = a.(Z.to_int i) in Z.leq Z.zero q1_ && Z.lt q1_ b)
         then raise (QtReturn3 false);
         for_loop_to5 (Z.succ i)
       end
     in for_loop_to5 o1);
    true
  with
  | QtReturn3 r3 -> r3

