let create_cursor (n: Z.t) : Lexgen__Cursor.cursor =
  let a = Array.make (Z.to_int n) Z.zero in
  { Lexgen__Cursor.current = a; Lexgen__Cursor.new1 = true }

let next (c: Lexgen__Cursor.cursor) : unit =
  let a = c.Lexgen__Cursor.current in
  let n = Z.of_int (Array.length a) in
  let r1 = ref (Z.sub n Z.one) in
  while Z.geq !r1 Z.zero && Z.equal a.(Z.to_int !r1) !r1 do
    r1 := Z.sub !r1 Z.one
  done;
  if Z.lt !r1 Z.zero
  then c.Lexgen__Cursor.new1 <- false
  else
    begin
      a.(Z.to_int !r1) <- Z.add a.(Z.to_int !r1) Z.one;
      (let o = Z.sub n Z.one in let o1 = Z.add !r1 Z.one in
       let rec for_loop_to3 i1 =
         if Z.leq i1 o
         then begin a.(Z.to_int i1) <- Z.zero; for_loop_to3 (Z.succ i1) end
       in for_loop_to3 o1);
      c.Lexgen__Cursor.new1 <- true
    end

