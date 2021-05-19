let create_cursor (n: Z.t) : Lexgen__Cursor.cursor =
  let a = Array.make (Z.to_int n) Z.zero in
  (let o = Z.sub n Z.one in let o1 = Z.zero in
   let rec for_loop_to6 i1 =
     if Z.leq i1 o
     then begin a.(Z.to_int i1) <- i1; for_loop_to6 (Z.succ i1) end
   in for_loop_to6 o1);
  { Lexgen__Cursor.current = a; Lexgen__Cursor.new1 = true }

let reverse (a: (Z.t) array) (l: Z.t) (u: Z.t) : unit =
  let m = Z.ediv (Z.sub (Z.add l u) Z.one) (Z.of_string "2") in
  let rec for_loop_to7 i2 =
    if Z.leq i2 m
    then begin
      Array__ArraySwap.swap a i2 (Z.sub (Z.sub (Z.add u l) Z.one) i2);
      for_loop_to7 (Z.succ i2)
    end
  in for_loop_to7 l

let next (c: Lexgen__Cursor.cursor) : unit =
  let a = c.Lexgen__Cursor.current in
  let n = Z.of_int (Array.length a) in
  if Z.leq n Z.one
  then c.Lexgen__Cursor.new1 <- false
  else
    begin
      let r4 = ref (Z.sub n (Z.of_string "2")) in
      while Z.geq !r4 Z.zero && Z.gt a.(Z.to_int !r4)
                                a.(Z.to_int (Z.add !r4 Z.one)) do
        r4 := Z.sub !r4 Z.one
      done;
      if Z.lt !r4 Z.zero
      then c.Lexgen__Cursor.new1 <- false
      else
        begin
          let j3 = ref (Z.sub n Z.one) in
          while Z.gt a.(Z.to_int !r4) a.(Z.to_int !j3) do
            j3 := Z.sub !j3 Z.one
          done;
          Array__ArraySwap.swap a !r4 !j3;
          reverse a (Z.add !r4 Z.one) n;
          c.Lexgen__Cursor.new1 <- true end end

