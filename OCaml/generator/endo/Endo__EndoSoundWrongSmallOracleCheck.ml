module SmallOracleCheck =
struct
  type verdict = {
    witness: ((Z.t) array) option;
    rank: Z.t;
    }
  
  let small_check (n: Z.t) : verdict =
    let exception QtReturn4 of verdict in
    try
      let c = Endo__Enum.create_cursor n in
      let r4 = ref Z.zero in
      while c.Lexgen__Cursor.new1 do
        r4 := Z.add !r4 Z.one;
        let a = c.Lexgen__Cursor.current in
        if Endo__Endo.b_endo_wrong a
        then Endo__Enum.next c
        else raise (QtReturn4 { witness = Some a; rank = !r4 })
      done;
      { witness = None ; rank = !r4 }
    with
    | QtReturn4 r4 -> r4
end

let test_b_endo_wrong (_: unit) : SmallOracleCheck.verdict =
  let n = Z.of_string "6" in SmallOracleCheck.small_check n

