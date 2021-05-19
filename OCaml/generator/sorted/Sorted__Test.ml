let run (_: unit) : ((Z.t) list) list =
  let n = Z.of_string "3" in
  let k4 = Z.of_string "3" in
  let c = Sorted__Enum.create_cursor n k4 in
  let l1 = ref ([] ) in
  while c.Lexgen__Cursor.new1 do
    let f = c.Lexgen__Cursor.current in
    let g =
      ArrayExtension__ToList.to_list f Z.zero (Z.of_int (Array.length f)) in
    l1 := g :: !l1; Sorted__Enum.next c k4
  done;
  !l1

