let create_cursor (n: Z.t) : Lexgen__Cursor.cursor =
  let a = Array.make (Z.to_int n) Z.zero in
  { Lexgen__Cursor.current = a; Lexgen__Cursor.new1 = true }

let next (c: Lexgen__Cursor.cursor) : unit =
  let a = c.Lexgen__Cursor.current in
  let n = Z.of_int (Array.length a) in
  let r3 = ref (Z.sub n Z.one) in
  while Z.geq (!r3) Z.zero && Z.equal (a.(Z.to_int (!r3))) (Z.sub n Z.one) do
    r3 := Z.sub (!r3) Z.one
  done;
  if Z.lt (!r3) Z.zero
  then c.Lexgen__Cursor.new1 <- false
  else
    begin
      a.(Z.to_int (!r3)) <- Z.add (a.(Z.to_int (!r3))) Z.one;
      (let o = Z.sub n Z.one in let o1 = Z.add (!r3) Z.one in
       let rec for_loop_to6 i4 =
         if Z.leq i4 o
         then begin a.(Z.to_int i4) <- Z.zero; for_loop_to6 (Z.succ i4) end
       in for_loop_to6 o1);
      c.Lexgen__Cursor.new1 <- true
    end

