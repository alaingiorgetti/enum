module SmallCheck =
struct
  type verdict = {
    witness: ((Z.t) list) option;
    rank: Z.t;
    }
  
  let small_check (oracle: (Z.t) list -> bool) (n: Z.t) : verdict =
    let exception QtReturn2 of verdict in
    try
      let c = Endo__Enum.create_cursor n in
      let r2 = ref Z.zero in
      while c.Lexgen__Cursor.new1 do
        r2 := Z.add !r2 Z.one;
        let a = c.Lexgen__Cursor.current in
        let l = Array__ToList.to_list a Z.zero (Z.of_int (Array.length a)) in
        if oracle l
        then Endo__Enum.next c
        else raise (QtReturn2 { witness = Some l; rank = !r2 })
      done;
      { witness = None ; rank = !r2 }
    with
    | QtReturn2 r2 -> r2
end

let test_b_endo (_: unit) : SmallCheck.verdict =
  let n = Z.of_string "5" in
  SmallCheck.small_check (fun (l: (Z.t) list) ->
                            Endo__Endo.b_endo (ListExtension__ArrayList.to_array l))
  n

let test_b_endo_wrong (_: unit) : SmallCheck.verdict =
  let n = Z.of_string "4" in
  SmallCheck.small_check (fun (l1: (Z.t) list) ->
                            Endo__Endo.b_endo_wrong (ListExtension__ArrayList.to_array l1))
  n

