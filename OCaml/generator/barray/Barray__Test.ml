let rec to_list (a: (Z.t) array) (l1: Z.t) (u: Z.t) : (Z.t) list =
  if Z.leq u l1 then []  else a.(Z.to_int l1) :: to_list a (Z.add l1 Z.one) u

let run (_: unit) : ((Z.t) list) list =
  let n = Z.of_string "3" in
  let k4 = Z.of_string "4" in
  let c = Barray__Enum.create_cursor n k4 in
  let l1 = ref ([] ) in
  while c.Lexgen__Cursor.new1 do
    let f = c.Lexgen__Cursor.current in
    let g = to_list f Z.zero (Z.of_int (Array.length f)) in
    l1 := g :: !l1; Barray__Enum.next c k4
  done;
  !l1

