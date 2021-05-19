let create_cursor (n: Z.t) (b: Z.t) : Lexgen__Cursor.cursor =
  let a = Array.make (Z.to_int n) Z.zero in
  if Z.leq b Z.zero
  then { Lexgen__Cursor.current = a; Lexgen__Cursor.new1 = false }
  else { Lexgen__Cursor.current = a; Lexgen__Cursor.new1 = true }

let next (c: Lexgen__Cursor.cursor) (b: Z.t) : unit =
  if Z.leq b Z.zero
  then c.Lexgen__Cursor.new1 <- false
  else
    begin
      let a = c.Lexgen__Cursor.current in
      let n = Z.of_int (Array.length a) in let r4 = ref (Z.sub n Z.one) in
      while Z.geq !r4 Z.zero && Z.equal a.(Z.to_int !r4) (Z.sub b Z.one) do
        r4 := Z.sub !r4 Z.one
      done;
      if Z.lt !r4 Z.zero
      then c.Lexgen__Cursor.new1 <- false
      else
        begin
          a.(Z.to_int !r4) <- Z.add a.(Z.to_int !r4) Z.one;
          (let o = Z.sub n Z.one in let o1 = Z.add !r4 Z.one in
           let rec for_loop_to6 i1 =
             if Z.leq i1 o
             then begin
               a.(Z.to_int i1) <- Z.zero;
               for_loop_to6 (Z.succ i1)
             end
           in for_loop_to6 o1);
          c.Lexgen__Cursor.new1 <- true
        end end

