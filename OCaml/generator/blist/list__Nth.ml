let rec nth : type a. (Z.t) -> (a list) ->  (a option) =
  fun n l -> match l with
    | [] -> None 
    | x :: r -> if Z.equal n Z.zero then Some x else nth (Z.sub n Z.one) r

