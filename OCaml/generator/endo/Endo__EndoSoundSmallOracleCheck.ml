module SmallOracleCheck =
struct
  type verdict = {
    witness: ((Z.t) array) option;
    rank: Z.t;
    }
  
  let small_check (n: Z.t) : verdict =
    let exception QtReturn3 of verdict in
    try
      let c = Endo__Enum.create_cursor n in
      let r3 = ref Z.zero in
      while c.Lexgen__Cursor.new1 do
        r3 := Z.add !r3 Z.one;
        let a = c.Lexgen__Cursor.current in
        if Endo__Endo.b_endo a
        then Endo__Enum.next c
        else raise (QtReturn3 { witness = Some a; rank = !r3 })
      done;
      { witness = None ; rank = !r3 }
    with
    | QtReturn3 r3 -> r3
end

let test_b_endo (_: unit) : SmallOracleCheck.verdict =
  let n = Z.of_string "5" in SmallOracleCheck.small_check n

