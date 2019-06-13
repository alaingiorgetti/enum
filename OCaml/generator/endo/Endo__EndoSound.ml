module SmallCheck =
struct
  type verdict = {
    witness: (Z.t) list;
    rank: Z.t;
    }
  
  let small_check (oracle: ((Z.t) list) -> (bool)) (n: Z.t) : verdict =
    let c = Endo__Enum.create_cursor n in
    let r1 = ref Z.zero in
    let ce = ref [] in
    while c.Lexgen__Cursor.new1 do
      r1 := Z.add (!r1) Z.one;
      let a = c.Lexgen__Cursor.current in
      let l = Array__ToList.to_list a Z.zero (Z.of_int (Array.length a)) in
      if oracle l
      then Endo__Enum.next c
      else begin ce := l; c.Lexgen__Cursor.new1 <- false end
    done;
    { witness = !ce; rank = !r1 }
end

let test_b_endo (_: unit) : SmallCheck.verdict =
  let n = Z.of_string "5" in
  SmallCheck.small_check (fun (l: (Z.t) list) ->
                            Endo__Endo.b_endo (ListExtension__ToArray.to_array l))
    n

