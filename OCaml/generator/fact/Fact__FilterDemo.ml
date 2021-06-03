let run (_: unit) : ((Z.t) list) list =
  let n = Z.of_string "3" in
  let c = Fact__FactEndo.create_cursor n in
  let l1 = ref ([] ) in
  if c.Lexgen__Cursor.new1
  then while c.Lexgen__Cursor.new1 do
         let f = c.Lexgen__Cursor.current in
         let g =
           ArrayExtension__ToList.to_list f
           Z.zero
           (Z.of_int (Array.length f)) in
         l1 := g :: !l1; Fact__FactEndo.next c
       done;
  !l1

