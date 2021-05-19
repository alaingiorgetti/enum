let b_inc1 (a: (Z.t) array) : bool =
  let exception QtReturn4 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.one in
     let rec for_loop_to6 i1 =
       if Z.leq i1 o
       then begin
         if not (Z.leq a.(Z.to_int (Z.sub i1 Z.one)) a.(Z.to_int i1))
         then raise (QtReturn4 false);
         for_loop_to6 (Z.succ i1)
       end
     in for_loop_to6 o1);
    true
  with
  | QtReturn4 r4 -> r4

let b_sorted (a: (Z.t) array) (b: Z.t) : bool =
  Barray__Barray.b_barray a b && b_inc1 a

