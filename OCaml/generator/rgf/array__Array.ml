exception OutOfBounds

let self_blit : type a. (a array) -> (Z.t) -> (Z.t) -> (Z.t) ->  unit =
  fun a ofs1 ofs2 len -> if Z.leq ofs1 ofs2
                         then
                           let o = Z.zero in
                           let o1 = Z.sub len Z.one in
                           let rec for_loop_to k =
                             if Z.geq k o
                             then begin
                               a.(Z.to_int (Z.add ofs2 k)) <- a.(Z.to_int 
                                                              (Z.add ofs1 k));
                               for_loop_to (Z.pred k)
                             end
                           in for_loop_to o1
                         else
                           begin
                             let o = Z.sub len Z.one in let o1 = Z.zero in
                             let rec for_loop_to1 k1 =
                               if Z.leq k1 o
                               then begin
                                 a.(Z.to_int (Z.add ofs2 k1)) <- a.(Z.to_int 
                                                                 (Z.add ofs1 k1));
                                 for_loop_to1 (Z.succ k1)
                               end
                             in for_loop_to1 o1 end

