module SmallCheckInt =
struct
  type verdict = {
    witness: ((Z.t) list) option;
    rank: Z.t;
    }
  
  let small_check_int (oracle: (Z.t) list -> Z.t -> bool) (n: Z.t) (k2: Z.t) :
    verdict =
    let exception QtReturn4 of verdict in
    try
      let c = Barray__Enum.create_cursor n k2 in
      let r4 = ref Z.zero in
      while c.Lexgen__Cursor.new1 do
        r4 := Z.add !r4 Z.one;
        let a = c.Lexgen__Cursor.current in
        let l = Array__ToList.to_list a Z.zero (Z.of_int (Array.length a)) in
        if oracle l k2
        then Barray__Enum.next c k2
        else raise (QtReturn4 { witness = Some l; rank = !r4 })
      done;
      { witness = None ; rank = !r4 }
    with
    | QtReturn4 r4 -> r4
end

let test_b_barray (_: unit) : SmallCheckInt.verdict =
  let n = Z.of_string "5" in
  let k2 = Z.of_string "3" in
  SmallCheckInt.small_check_int (fun (l: (Z.t) list)
                                   (k3: Z.t) ->
                                   Barray__Barray.b_barray (ListExtension__ArrayList.to_array l)
                                   k3)
  n
  k2

