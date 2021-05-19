let create_cursor (n: Z.t) (b: Z.t) : LexgenList__Cursor.cursor =
  let l = ListExtension__ListExtension.make n Z.zero in
  if Z.lt b Z.zero
  then { LexgenList__Cursor.current = l; LexgenList__Cursor.new1 = false }
  else
    begin
      if Blist__Blist.is_blist l b
      then { LexgenList__Cursor.current = l; LexgenList__Cursor.new1 = true }
      else
        { LexgenList__Cursor.current = l; LexgenList__Cursor.new1 = false } end

let rec next_blist_rec (l: (Z.t) list) (b: Z.t) : ((Z.t) list) option =
  match l with
  | [] -> None 
  | x :: r ->
    if Z.lt x (Z.sub b Z.one)
    then Some (Z.add x Z.one :: r)
    else
      begin match next_blist_rec r b with
      | None -> None 
      | Some m -> Some (x :: m)
      end

let next (c: LexgenList__Cursor.cursor) (b: Z.t) : unit =
  if Z.lt b Z.zero
  then c.LexgenList__Cursor.new1 <- false
  else
    begin match next_blist_rec c.LexgenList__Cursor.current b with
    | None -> c.LexgenList__Cursor.new1 <- false
    | Some l ->
      c.LexgenList__Cursor.current <- l; c.LexgenList__Cursor.new1 <- true
    end

