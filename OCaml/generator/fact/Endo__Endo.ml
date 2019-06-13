let b_endo (a: (Z.t) array) : bool =
  let exception QtReturn1 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to4 i2 =
       if Z.leq i2 o
       then begin
         if
           not (let q1_ = a.(Z.to_int i2) in
                Z.leq Z.zero q1_ && Z.lt q1_ (Z.of_int (Array.length a)))
         then raise (QtReturn1 false);
         for_loop_to4 (Z.succ i2)
       end
     in for_loop_to4 o1);
    true
  with
  | QtReturn1 r1 -> r1

