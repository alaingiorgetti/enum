let run (_: unit) : ((Z.t) list) list =
  let n = Z.of_string "3" in
  let c = Endo__Enum.create_cursor n in
  let l2 = ref ([] ) in
  while c.Lexgen__Cursor.new1 do
    let f = c.Lexgen__Cursor.current in
    let g =
      ArrayExtension__ToList.to_list f Z.zero (Z.of_int (Array.length f)) in
    l2 := g :: !l2; Endo__Enum.next c
  done;
  !l2

