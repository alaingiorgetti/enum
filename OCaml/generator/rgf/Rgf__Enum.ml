let create_cursor (n: Z.t) : Lexgen__Cursor.cursor =
  let a = Array.make (Z.to_int n) Z.zero in
  { Lexgen__Cursor.current = a; Lexgen__Cursor.new1 = true }

let next (c: Lexgen__Cursor.cursor) : unit =
  let a = c.Lexgen__Cursor.current in
  let n = Z.of_int (Array.length a) in
  if Z.leq n Z.one
  then c.Lexgen__Cursor.new1 <- false
  else
    begin
      let r2 = ref (Z.sub n Z.one) in
      while Z.geq !r2 Z.one && Z.equal a.(Z.to_int !r2)
                               (Z.add a.(Z.to_int (Z.sub !r2 Z.one)) Z.one) do
        r2 := Z.sub !r2 Z.one
      done;
      if Z.equal !r2 Z.zero
      then c.Lexgen__Cursor.new1 <- false
      else
        begin
          a.(Z.to_int !r2) <- Z.add a.(Z.to_int !r2) Z.one;
          (let o = Z.sub n Z.one in let o1 = Z.add !r2 Z.one in
           let rec for_loop_to4 i2 =
             if Z.leq i2 o
             then begin
               a.(Z.to_int i2) <- Z.zero;
               for_loop_to4 (Z.succ i2)
             end
           in for_loop_to4 o1);
          c.Lexgen__Cursor.new1 <- true
        end end

