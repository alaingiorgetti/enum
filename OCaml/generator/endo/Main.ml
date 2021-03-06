(* Added to the files generated by Why3 to run a test function. *)

open Format

let z_int_list (l : Z.t list) : string =
  List.fold_left (fun s x -> s ^ (Z.to_string x) ^ " ") "" l

let print_z_int_list (l: Z.t list) =
  Format.printf "[%s]\n" (z_int_list l)

(* Main function, running a test function returning a verdict. *)

let () =
  let v = Endo__EndoSound.test_b_endo () in
  let r = Z.to_string v.rank in
  if v.witness = [] then
    Format.printf "Test passed. %s data tested.\n\n" r
  else begin
    Format.printf "Test failed after %s tests. Counterexample:\n" r;
    print_z_int_list v.witness
  end

