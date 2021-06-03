module SmallCheck3 =
struct
  type verdict = {
    witness: ((Z.t) array) option;
    rank: Z.t;
    }
  
  let small_check (n: Z.t) : verdict =
    let exception QtReturn2 of verdict in
    try
      let c = Endo__Enum.create_cursor n in
      let r2 = ref Z.zero in
      while c.Lexgen__Cursor.new1 do
        r2 := Z.add (!r2) Z.one;
        let a = c.Lexgen__Cursor.current in
        if Endo__Endo.b_endo a
        then Endo__Enum.next c
        else raise (QtReturn2 ({ witness = Some a; rank = !r2 }))
      done;
      { witness = None; rank = !r2 }
    with
    | QtReturn2 r2 -> r2
end

let main (_: unit) : SmallCheck3.verdict =
  let n = Z.of_string "5" in SmallCheck3.small_check n

