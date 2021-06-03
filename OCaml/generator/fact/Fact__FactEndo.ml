let create_cursor (n: Z.t) : Lexgen__Cursor.cursor =
  let c = Endo__Enum.create_cursor n in
  while c.Lexgen__Cursor.new1 && not (Fact__Fact.b_fact c.Lexgen__Cursor.current) do
    Endo__Enum.next c
  done;
  c

let next (c: Lexgen__Cursor.cursor) : unit =
  let a =
    Array.make (Z.to_int (Z.of_int (Array.length c.Lexgen__Cursor.current))) Z.zero in
  ArrayExtension__Array.copy c.Lexgen__Cursor.current a;
  if c.Lexgen__Cursor.new1 then Endo__Enum.next c;
  while c.Lexgen__Cursor.new1 && not (Fact__Fact.b_fact c.Lexgen__Cursor.current) do
    Endo__Enum.next c
  done;
  if not (Fact__Fact.b_fact c.Lexgen__Cursor.current)
  then begin
         ArrayExtension__Array.copy a c.Lexgen__Cursor.current;
         c.Lexgen__Cursor.new1 <- false
       end

