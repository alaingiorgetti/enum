let rec id_aux (n: Z.t) (i: Z.t) : (Z.t) list =
  if Z.leq n Z.zero then []  else i :: id_aux (Z.sub n Z.one) (Z.add i Z.one)

let id (n: Z.t) : (Z.t) list = id_aux n Z.zero

let rec rm_nth (x: Z.t) (l: ((Z.t) list) ref) : Z.t =
  match !l with
  | [] -> l := [] ; Z.zero
  | y :: m ->
    if Z.equal x Z.zero
    then begin l := m; y end
    else
      begin
        let r = ref m in let z = rm_nth (Z.sub x Z.one) r in l := y :: !r; z end

let rec make (n: Z.t) (v: Z.t) : (Z.t) list =
  if Z.equal n Z.zero then []  else v :: make (Z.sub n Z.one) v

let rec nth_func_rec (i: Z.t) (l: (Z.t) list) : Z.t =
  match l with
  | x :: r -> if Z.equal i Z.zero then x else nth_func_rec (Z.sub i Z.one) r
  | _ -> assert false (* absurd *)

let in_interval (x: Z.t) (l: Z.t) (u: Z.t) : bool = Z.leq l x && Z.lt x u

