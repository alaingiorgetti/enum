let b_pre_img (a: (Z.t) array) (j3: Z.t) : bool =
  let exception QtReturn4 of (bool) in
  try
    (let o = Z.sub (Z.of_int (Array.length a)) Z.one in let o1 = Z.zero in
     let rec for_loop_to7 i2 =
       if Z.leq i2 o
       then begin
         if Z.equal a.(Z.to_int i2) j3 then raise (QtReturn4 true);
         for_loop_to7 (Z.succ i2)
       end
     in for_loop_to7 o1);
    false
  with
  | QtReturn4 r4 -> r4

let b_init_pre_img (a: (Z.t) array) (k2: Z.t) : bool =
  let exception QtReturn5 of (bool) in
  try
    (let o = Z.sub k2 Z.one in let o1 = Z.zero in
     let rec for_loop_to8 j3 =
       if Z.leq j3 o
       then begin
         if not (b_pre_img a j3) then raise (QtReturn5 false);
         for_loop_to8 (Z.succ j3)
       end
     in for_loop_to8 o1);
    true
  with
  | QtReturn5 r5 -> r5

