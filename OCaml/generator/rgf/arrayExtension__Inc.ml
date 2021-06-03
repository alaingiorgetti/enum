let b_inc (a: (Z.t) array) : bool =
  let exception QtReturn of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.one in
     let rec for_loop_to2 i =
       if Z.leq i o
       then begin
         if not (Z.lt a.(Z.to_int (Z.sub i Z.one)) a.(Z.to_int i))
         then raise (QtReturn false);
         for_loop_to2 (Z.succ i)
       end
     in for_loop_to2 o1);
    true
  with
  | QtReturn r -> r

