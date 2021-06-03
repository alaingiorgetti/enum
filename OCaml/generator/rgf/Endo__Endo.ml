let b_endo (a: (Z.t) array) : bool =
  let exception QtReturn2 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to5 i3 =
       if Z.leq i3 o
       then begin
         if not (let q1_ = a.(Z.to_int i3) in Z.leq Z.zero q1_ && Z.lt q1_ n)
         then raise (QtReturn2 false);
         for_loop_to5 (Z.succ i3)
       end
     in for_loop_to5 o1);
    true
  with
  | QtReturn2 r2 -> r2

let b_endo_wrong (a: (Z.t) array) : bool =
  let exception QtReturn3 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to6 i4 =
       if Z.leq i4 o
       then begin
         if
           not (let q1_ = a.(Z.to_int i4) in
                Z.leq Z.zero q1_ && Z.lt q1_ (Z.sub n Z.one))
         then raise (QtReturn3 false);
         for_loop_to6 (Z.succ i4)
       end
     in for_loop_to6 o1);
    true
  with
  | QtReturn3 r3 -> r3

