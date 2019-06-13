let b_endo (a: (Z.t) array) : bool =
  let exception QtReturn2 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to5 i3 =
       if Z.leq i3 o
       then begin
         if
           not (let q1_ = a.(Z.to_int i3) in
                Z.leq Z.zero q1_ && Z.lt q1_ (Z.of_int (Array.length a)))
         then raise (QtReturn2 false);
         for_loop_to5 (Z.succ i3)
       end
     in for_loop_to5 o1);
    true
  with
  | QtReturn2 r2 -> r2

