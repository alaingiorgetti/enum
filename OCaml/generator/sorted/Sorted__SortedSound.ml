module SmallCheckInt =
struct
  type verdict = {
    witness: ((Z.t) list) option;
    rank: Z.t;
    }
  
  let small_check_int (oracle: (Z.t) list -> Z.t -> bool) (n: Z.t) (k2: Z.t) :
    verdict =
    let exception QtReturn5 of verdict in
    try
      let c = Sorted__Enum.create_cursor n k2 in
      let r5 = ref Z.zero in
      while c.Lexgen__Cursor.new1 do
        r5 := Z.add !r5 Z.one;
        let a = c.Lexgen__Cursor.current in
        let l = Array__ToList.to_list a Z.zero (Z.of_int (Array.length a)) in
        if oracle l k2
        then Sorted__Enum.next c k2
        else raise (QtReturn5 { witness = Some l; rank = !r5 })
      done;
      { witness = None ; rank = !r5 }
    with
    | QtReturn5 r5 -> r5
end

let test_b_sorted (_: unit) : SmallCheckInt.verdict =
  let n = Z.of_string "5" in
  let k2 = Z.of_string "3" in
  SmallCheckInt.small_check_int (fun (l: (Z.t) list)
                                   (k3: Z.t) ->
                                   Sorted__Sorted.b_sorted (ListExtension__ArrayList.to_array l)
                                   k3)
  n
  k2

