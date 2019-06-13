let in_interval (x: Z.t) (l: Z.t) (u: Z.t) : bool = Z.leq l x && Z.lt x u

let b_diff (a: (Z.t) array) (i: Z.t) : bool =
  let exception QtReturn of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to2 j =
       if Z.leq j o
       then begin
         if Z.equal (a.(Z.to_int j)) (a.(Z.to_int i)) && not (Z.equal j i)
         then raise (QtReturn false);
         for_loop_to2 (Z.succ j)
       end
     in for_loop_to2 o1);
    true
  with
  | QtReturn r -> r

let b_inj (a: (Z.t) array) : bool =
  let exception QtReturn1 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to3 j1 =
       if Z.leq j1 o
       then begin
         if not (b_diff a j1) then raise (QtReturn1 false);
         for_loop_to3 (Z.succ j1)
       end
     in for_loop_to3 o1);
    true
  with
  | QtReturn1 r1 -> r1

let b_range (a: (Z.t) array) : bool =
  let exception QtReturn2 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to4 j2 =
       if Z.leq j2 o
       then begin
         if not (in_interval (a.(Z.to_int j2)) Z.zero n)
         then raise (QtReturn2 false);
         for_loop_to4 (Z.succ j2)
       end
     in for_loop_to4 o1);
    true
  with
  | QtReturn2 r2 -> r2

