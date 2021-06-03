let is_none : type a. (a option) ->  (bool) =
  fun o -> match o with
    | None -> true
    | Some _ -> false

