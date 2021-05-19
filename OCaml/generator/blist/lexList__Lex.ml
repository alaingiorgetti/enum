let rec list_eq (l1: (Z.t) list) (l2: (Z.t) list) : bool =
  Z.equal (Z.of_int (List.length l1)) (Z.of_int (List.length l2)) && 
  begin match l1
  with
  | [] -> begin match l2 with
          | [] -> true
          | _ -> false
          end
  | x1 :: r1 ->
    begin match l2 with
    | [] -> false
    | x2 :: r2 -> Z.equal x1 x2 && list_eq r1 r2
    end
  end

let rec lt_lex (l1: (Z.t) list) (l2: (Z.t) list) : bool =
  Z.equal (Z.of_int (List.length l1)) (Z.of_int (List.length l2)) && 
  begin match l1
  with
  | [] -> begin match l2 with
          | [] -> false
          | _ -> true
          end
  | x1 :: r1 ->
    begin match l2 with
    | [] -> false
    | x2 :: r2 -> Z.lt x1 x2 || Z.equal x1 x2 && lt_lex r1 r2
    end
  end

