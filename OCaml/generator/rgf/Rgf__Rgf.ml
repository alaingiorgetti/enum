let b_rgf (a: (Z.t) array) : bool =
  let exception QtReturn1 of (bool) in
  try
    let n = Z.of_int (Array.length a) in
    if Z.equal n Z.zero
    then raise (QtReturn1 true)
    else
      begin
        if not (Z.equal a.(Z.to_int Z.zero) Z.zero)
        then raise (QtReturn1 false)
        else
          begin
            let o = Z.sub n Z.one in let o1 = Z.one in
            let rec for_loop_to3 i1 =
              if Z.leq i1 o
              then begin
                if
                  not (let q1_ = a.(Z.to_int i1) in
                       Z.leq Z.zero q1_ && Z.leq q1_
                                           (Z.add a.(Z.to_int (Z.sub i1
                                                               Z.one))
                                            Z.one))
                then raise (QtReturn1 false);
                for_loop_to3 (Z.succ i1)
              end
            in for_loop_to3 o1 end end;
    true
  with
  | QtReturn1 r1 -> r1

