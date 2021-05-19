let rec is_blist (l: (Z.t) list) (b: Z.t) : bool =
  match l with
  | [] -> true
  | x :: r -> (Z.leq Z.zero x && Z.lt x b) && is_blist r b

