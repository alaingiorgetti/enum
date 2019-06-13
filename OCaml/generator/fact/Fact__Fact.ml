let b_fact (a: (Z.t) array) : bool =
  let exception QtReturn of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to2 i =
       if Z.leq i o
       then begin
         if not (let q1_ = a.(Z.to_int i) in Z.leq Z.zero q1_ && Z.leq q1_ i)
         then raise (QtReturn false);
         for_loop_to2 (Z.succ i)
       end
     in for_loop_to2 o1);
    true
  with
  | QtReturn r -> r

