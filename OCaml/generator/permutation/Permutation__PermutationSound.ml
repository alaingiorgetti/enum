module SmallCheck =
struct
  type verdict = {
    witness: ((Z.t) list) option;
    rank: Z.t;
    }
  
  let small_check (oracle: (Z.t) list -> bool) (n: Z.t) : verdict =
    let exception QtReturn4 of verdict in
    try
      let c = Permutation__Enum.create_cursor n in
      let r4 = ref Z.zero in
      while c.Lexgen__Cursor.new1 do
        r4 := Z.add !r4 Z.one;
        let a = c.Lexgen__Cursor.current in
        let l = Array__ToList.to_list a Z.zero (Z.of_int (Array.length a)) in
        if oracle l
        then Permutation__Enum.next c
        else raise (QtReturn4 { witness = Some l; rank = !r4 })
      done;
      { witness = None ; rank = !r4 }
    with
    | QtReturn4 r4 -> r4
end

let test_b_permut (_: unit) : SmallCheck.verdict =
  let n = Z.of_string "5" in
  SmallCheck.small_check (fun (l: (Z.t) list) ->
                            Permutation__Permutation.b_permut (ListExtension__ArrayList.to_array l))
  n

let reverse (a: (Z.t) array) : unit =
  let n = Z.of_int (Array.length a) in
  if Z.lt Z.zero n
  then begin
    let x = ref Z.zero in let y = ref (Z.sub n Z.one) in
    while Z.lt !x !y do
      Array__ArraySwap.swap a !x !y; y := Z.sub !y Z.one; x := Z.add !x Z.one
    done end

let test (_: unit) : SmallCheck.verdict =
  let n = Z.of_string "6" in
  SmallCheck.small_check (fun (l1: (Z.t) list) ->
                            (let a = ListExtension__ArrayList.to_array l1 in
                             reverse a; Permutation__Permutation.b_permut a))
  n

let b_range_wrong (a: (Z.t) array) : bool =
  let exception QtReturn5 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    (let o = Z.sub n Z.one in let o1 = Z.zero in
     let rec for_loop_to8 j3 =
       if Z.leq j3 o
       then begin
         if
           not (ArrayExtension__ArrayInjection.in_interval a.(Z.to_int j3)
                Z.zero (Z.sub n Z.one))
         then raise (QtReturn5 false);
         for_loop_to8 (Z.succ j3)
       end
     in for_loop_to8 o1);
    true
  with
  | QtReturn5 r5 -> r5

let test1 (_: unit) : SmallCheck.verdict =
  let n = Z.of_string "6" in
  SmallCheck.small_check (fun (l2: (Z.t) list) ->
                            b_range_wrong (ListExtension__ArrayList.to_array l2))
  n

