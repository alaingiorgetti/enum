let b_endo (a: (Z.t) array) : bool =
  let exception QtReturn of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to2 i =
       if Z.leq i o
       then begin
         if not (let q1_ = a.(Z.to_int i) in Z.leq Z.zero q1_ && Z.lt q1_ n)
         then raise (QtReturn false);
         for_loop_to2 (Z.succ i)
       end
     in for_loop_to2 o1);
    true
  with
  | QtReturn r -> r

let b_endo_wrong (a: (Z.t) array) : bool =
  let exception QtReturn1 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to3 i1 =
       if Z.leq i1 o
       then begin
         if
           not (let q1_ = a.(Z.to_int i1) in
                Z.leq Z.zero q1_ && Z.lt q1_ (Z.sub n Z.one))
         then raise (QtReturn1 false);
         for_loop_to3 (Z.succ i1)
       end
     in for_loop_to3 o1);
    true
  with
  | QtReturn1 r1 -> r1

