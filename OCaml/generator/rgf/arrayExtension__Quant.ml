let for_all_sub :
  type a. (a -> (bool)) -> (a array) -> (Z.t) -> (Z.t) ->  (bool) =
  fun p a l u -> let exception QtReturn2 of (bool) in
                 try
                   begin
                     let rec for_loop_to6 i4 =
                       if Z.leq i4 u
                       then begin
                         if not (p a.(Z.to_int i4))
                         then raise (QtReturn2 false);
                         for_loop_to6 (Z.succ i4)
                       end
                     in for_loop_to6 l end;
                   true
                 with
                 | QtReturn2 r2 -> r2

let for_all : type a. (a -> (bool)) -> (a array) ->  (bool) =
  fun p a -> let exception QtReturn3 of (bool) in
             try
               (let o = Z.sub (Z.of_int (Array.length a)) Z.one in
                let o1 = Z.zero in
                let rec for_loop_to7 i5 =
                  if Z.leq i5 o
                  then begin
                    if not (p a.(Z.to_int i5)) then raise (QtReturn3 false);
                    for_loop_to7 (Z.succ i5)
                  end
                in for_loop_to7 o1);
               true
             with
             | QtReturn3 r3 -> r3

let for_some_sub :
  type a. (a -> (bool)) -> (a array) -> (Z.t) -> (Z.t) ->  (bool) =
  fun p a l u -> let exception QtReturn4 of (bool) in
                 try
                   begin
                     let rec for_loop_to8 i6 =
                       if Z.leq i6 u
                       then begin
                         if p a.(Z.to_int i6) then raise (QtReturn4 true);
                         for_loop_to8 (Z.succ i6)
                       end
                     in for_loop_to8 l end;
                   false
                 with
                 | QtReturn4 r4 -> r4

let for_some : type a. (a -> (bool)) -> (a array) ->  (bool) =
  fun p a -> let exception QtReturn5 of (bool) in
             try
               (let o = Z.sub (Z.of_int (Array.length a)) Z.one in
                let o1 = Z.zero in
                let rec for_loop_to9 i7 =
                  if Z.leq i7 o
                  then begin
                    if p a.(Z.to_int i7) then raise (QtReturn5 true);
                    for_loop_to9 (Z.succ i7)
                  end
                in for_loop_to9 o1);
               false
             with
             | QtReturn5 r5 -> r5

let mem_sub :
  type a. (a -> (a -> (bool))) -> a -> (a array) -> (Z.t) -> (Z.t) ->  (bool) =
  fun eq x a l u -> for_some_sub (eq x) a l u

let mem : type a. (a -> (a -> (bool))) -> a -> (a array) ->  (bool) =
  fun eq x a -> for_some (eq x) a

