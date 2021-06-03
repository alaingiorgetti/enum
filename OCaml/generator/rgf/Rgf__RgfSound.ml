module SmallCheck =
struct
  type verdict = {
    witness: ((Z.t) list) option;
    rank: Z.t;
    }
  
  let small_check (oracle: (Z.t) list -> bool) (n: Z.t) : verdict =
    let exception QtReturn4 of verdict in
    try
      let c = Rgf__Enum.create_cursor n in
      let r4 = ref Z.zero in
      while c.Lexgen__Cursor.new1 do
        r4 := Z.add !r4 Z.one;
        let a = c.Lexgen__Cursor.current in
        let l = Array__ToList.to_list a Z.zero (Z.of_int (Array.length a)) in
        if oracle l
        then Rgf__Enum.next c
        else raise (QtReturn4 { witness = Some l; rank = !r4 })
      done;
      { witness = None ; rank = !r4 }
    with
    | QtReturn4 r4 -> r4
end

let test_b_rgf (_: unit) : SmallCheck.verdict =
  let n = Z.of_string "5" in
  SmallCheck.small_check (fun (l: (Z.t) list) ->
                            Rgf__Rgf.b_rgf (ListExtension__ArrayList.to_array l))
  n

