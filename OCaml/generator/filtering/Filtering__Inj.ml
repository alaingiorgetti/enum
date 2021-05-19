let b_linear (a: (Z.t) array) : bool =
  let exception QtReturn5 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to9 i4 =
       if Z.leq i4 o
       then begin
         if not (ArrayExtension__ArrayInjection.b_diff a i4)
         then raise (QtReturn5 false);
         for_loop_to9 (Z.succ i4)
       end
     in for_loop_to9 o1);
    true
  with
  | QtReturn5 r5 -> r5

let b_inj (a: (Z.t) array) (k2: Z.t) : bool =
  if Z.lt k2 (Z.of_int (Array.length a))
  then false
  else Barray__Barray.b_barray a k2 && b_linear a

