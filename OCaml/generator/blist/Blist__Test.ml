let run (_: unit) : ((Z.t) list) list =
  let n = Z.of_string "3" in
  let b = Z.of_string "4" in
  let c = Blist__Enum.create_cursor n b in
  let l1 = ref ([] ) in
  while c.LexgenList__Cursor.new1 do
    let f = c.LexgenList__Cursor.current in
    l1 := f :: !l1; Blist__Enum.next c b
  done;
  !l1

