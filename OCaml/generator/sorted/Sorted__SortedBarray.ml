let create_cursor (n: Z.t) (k2: Z.t) : Lexgen__Cursor.cursor =
  let c = Barray__Enum.create_cursor n k2 in
  while c.Lexgen__Cursor.new1 && not (Sorted__Sorted.b_sorted c.Lexgen__Cursor.current
                                      k2) do
    Barray__Enum.next c k2
  done;
  c

let next (c: Lexgen__Cursor.cursor) (k2: Z.t) : unit =
  let a =
    Array.make (Z.to_int (Z.of_int (Array.length c.Lexgen__Cursor.current))) Z.zero in
  ArrayExtension__Array.copy c.Lexgen__Cursor.current a;
  if c.Lexgen__Cursor.new1 then Barray__Enum.next c k2;
  while c.Lexgen__Cursor.new1 && not (Sorted__Sorted.b_sorted c.Lexgen__Cursor.current
                                      k2) do
    Barray__Enum.next c k2
  done;
  if not (Sorted__Sorted.b_sorted c.Lexgen__Cursor.current k2)
  then begin
         ArrayExtension__Array.copy a c.Lexgen__Cursor.current;
         c.Lexgen__Cursor.new1 <- false
       end

