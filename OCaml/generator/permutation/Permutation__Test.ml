let run (_: unit) : ((Z.t) list) list =
  let n = Z.of_string "3" in
  let c = Permutation__Enum.create_cursor n in
  let l3 = ref [] in
  while c.Lexgen__Cursor.new1 do
    let f = c.Lexgen__Cursor.current in
    let g = Array__ToList.to_list f Z.zero (Z.of_int (Array.length f)) in
    l3 := g :: !l3; Permutation__Enum.next c
  done;
  !l3

