module SmallCheckInt =
struct
  type verdict = {
    witness: (Z.t) list;
    rank: Z.t;
    }
  
  let small_check_int (oracle: ((Z.t) list) -> ((Z.t) -> (bool))) (n: Z.t)
                      (k2: Z.t) : verdict =
    let c = Sorted__Enum.create_cursor n k2 in
    let r5 = ref Z.zero in
    let ce = ref [] in
    while c.Lexgen__Cursor.new1 do
      r5 := Z.add (!r5) Z.one;
      let a = c.Lexgen__Cursor.current in
      let l = Array__ToList.to_list a Z.zero (Z.of_int (Array.length a)) in
      if oracle l k2
      then Sorted__Enum.next c k2
      else begin ce := l; c.Lexgen__Cursor.new1 <- false end
    done;
    { witness = !ce; rank = !r5 }
end

let test_b_sorted (_: unit) : SmallCheckInt.verdict =
  let n = Z.of_string "5" in
  let k2 = Z.of_string "3" in
  SmallCheckInt.small_check_int (fun (l: (Z.t) list)
                                   (k3: Z.t) ->
                                   Sorted__Sorted.b_sorted (ListExtension__ToArray.to_array l)
                                     k3) n k2

