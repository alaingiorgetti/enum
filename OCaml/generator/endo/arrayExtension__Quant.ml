let for_all_sub :
  type a. (a -> (bool)) -> (a array) -> (Z.t) -> (Z.t) ->  (bool) =
  fun p a l u -> let exception QtReturn of (bool) in
                 try
                   begin
                     let rec for_loop_to3 i1 =
                       if Z.leq i1 u
                       then begin
                         if not (p a.(Z.to_int i1))
                         then raise (QtReturn false);
                         for_loop_to3 (Z.succ i1)
                       end
                     in for_loop_to3 l end;
                   true
                 with
                 | QtReturn r -> r

let for_all : type a. (a -> (bool)) -> (a array) ->  (bool) =
  fun p a -> let exception QtReturn1 of (bool) in
             try
               (let o = Z.sub (Z.of_int (Array.length a)) Z.one in
                let o1 = Z.zero in
                let rec for_loop_to4 i2 =
                  if Z.leq i2 o
                  then begin
                    if not (p a.(Z.to_int i2)) then raise (QtReturn1 false);
                    for_loop_to4 (Z.succ i2)
                  end
                in for_loop_to4 o1);
               true
             with
             | QtReturn1 r1 -> r1

let for_some_sub :
  type a. (a -> (bool)) -> (a array) -> (Z.t) -> (Z.t) ->  (bool) =
  fun p a l u -> let exception QtReturn2 of (bool) in
                 try
                   begin
                     let rec for_loop_to5 i3 =
                       if Z.leq i3 u
                       then begin
                         if p a.(Z.to_int i3) then raise (QtReturn2 true);
                         for_loop_to5 (Z.succ i3)
                       end
                     in for_loop_to5 l end;
                   false
                 with
                 | QtReturn2 r2 -> r2

let for_some : type a. (a -> (bool)) -> (a array) ->  (bool) =
  fun p a -> let exception QtReturn3 of (bool) in
             try
               (let o = Z.sub (Z.of_int (Array.length a)) Z.one in
                let o1 = Z.zero in
                let rec for_loop_to6 i4 =
                  if Z.leq i4 o
                  then begin
                    if p a.(Z.to_int i4) then raise (QtReturn3 true);
                    for_loop_to6 (Z.succ i4)
                  end
                in for_loop_to6 o1);
               false
             with
             | QtReturn3 r3 -> r3

let mem_sub :
  type a. (a -> (a -> (bool))) -> a -> (a array) -> (Z.t) -> (Z.t) ->  (bool) =
  fun eq x a l u -> for_some_sub (eq x) a l u

let mem : type a. (a -> (a -> (bool))) -> a -> (a array) ->  (bool) =
  fun eq x a -> for_some (eq x) a

