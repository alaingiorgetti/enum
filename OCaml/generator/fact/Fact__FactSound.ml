module SmallCheck =
struct
  type verdict = {
    witness: ((Z.t) list) option;
    rank: Z.t;
    }
  
  let small_check (oracle: (Z.t) list -> bool) (n: Z.t) : verdict =
    let exception QtReturn3 of verdict in
    try
      let c = Fact__Enum.create_cursor n in
      let r3 = ref Z.zero in
      while c.Lexgen__Cursor.new1 do
        r3 := Z.add !r3 Z.one;
        let a = c.Lexgen__Cursor.current in
        let l = Array__ToList.to_list a Z.zero (Z.of_int (Array.length a)) in
        if oracle l
        then Fact__Enum.next c
        else raise (QtReturn3 { witness = Some l; rank = !r3 })
      done;
      { witness = None ; rank = !r3 }
    with
    | QtReturn3 r3 -> r3
end

let test_b_fact (_: unit) : SmallCheck.verdict =
  let n = Z.of_string "5" in
  SmallCheck.small_check (fun (l: (Z.t) list) ->
                            Fact__Fact.b_fact (ListExtension__ArrayList.to_array l))
  n

