module SmallCheckInt =
struct
  type verdict = {
    witness: ((Z.t) list) option;
    rank: Z.t;
    }
  
  let small_check_int (oracle: (Z.t) list -> Z.t -> bool) (n: Z.t) (k: Z.t) :
    verdict =
    let exception QtReturn of verdict in
    try
      let c = Blist__Enum.create_cursor n k in
      let r = ref Z.zero in
      while c.LexgenList__Cursor.new1 do
        r := Z.add !r Z.one;
        let l = c.LexgenList__Cursor.current in
        if oracle l k
        then Blist__Enum.next c k
        else raise (QtReturn { witness = Some l; rank = !r })
      done;
      { witness = None ; rank = !r }
    with
    | QtReturn r -> r
end

let test_b_blist (_: unit) : SmallCheckInt.verdict =
  let n = Z.of_string "5" in
  let k = Z.of_string "3" in
  SmallCheckInt.small_check_int (fun (l: (Z.t) list)
                                   (k1: Z.t) ->
                                   Blist__Blist.is_blist l k1)
  n
  k

