let swap : type a. (a array) -> (Z.t) -> (Z.t) ->  unit =
  fun a i j -> let v = a.(Z.to_int i) in
               a.(Z.to_int i) <- a.(Z.to_int j); a.(Z.to_int j) <- v

