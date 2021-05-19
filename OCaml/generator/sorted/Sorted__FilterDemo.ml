let run (_: unit) : ((Z.t) list) list =
  let n = Z.of_string "3" in
  let k2 = Z.of_string "3" in
  let c = Sorted__SortedBarray.create_cursor n k2 in
  let l = ref ([] ) in
  if c.Lexgen__Cursor.new1
  then while c.Lexgen__Cursor.new1 do
         let f = c.Lexgen__Cursor.current in
         let g =
           ArrayExtension__ToList.to_list f
           Z.zero
           (Z.of_int (Array.length f)) in
         l := g :: !l; Sorted__SortedBarray.next c k2
       done;
  !l

