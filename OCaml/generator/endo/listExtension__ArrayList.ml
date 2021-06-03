let rec to_array_rec (l: (Z.t) list) (a: (Z.t) array) : unit =
  match l with
  | [] -> ()
  | y :: m ->
    a.(Z.to_int (Z.sub (Z.of_int (Array.length a))
                 (Z.of_int (List.length l)))) <- y;
    to_array_rec m a

let to_array (l: (Z.t) list) : (Z.t) array =
  let a = Array.make (Z.to_int (Z.of_int (List.length l))) Z.zero in
  to_array_rec l a; a

