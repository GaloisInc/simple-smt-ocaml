open Printf
open Simple_smt

exception NotSat

let check_sat s =
  match check s with
  | Sat -> ()
  | _   -> raise NotSat


let main () =
  printf "Start\n%!";

  let s = new_solver cvc5 in
  let ext = s.config.exts in
  let sx = ack_command s (declare "sx" (t_set t_int)); atom "sx" in
  let sy = set_empty ext t_int in
  let sz = set_universe ext t_int in
  ack_command s (assume (eq sx sy));
  ack_command s (assume (set_member ext (num_k 2) sz));
  ack_command s (assume (set_subset ext sx sy));
  check_sat s;
  let w = 8 in
  let f = ack_command s (declare_fun "f" [t_int] (t_bits w)); atom "f" in
  ack_command s (assume (eq (app f [num_k 2]) (bv_k w (Z.of_int 10))));
  ack_command s (assume (eq (app f [num_k 3]) (bv_k w (Z.of_int 11))));
  let x = ack_command s (declare "x" (t_bits w)); atom "x" in
  ack_command s (assume (eq x (bv_k w (Z.of_int (-17)))));
  check_sat s;

  let m = get_model s in
  let s1 = model_eval s.config m in
  let _r = s1.eval [] x in
  print_endline "111";
  let _r = s1.eval [] x in
  print_endline "222";
  let _r = s1.eval [("y",[],t_bits w,bv_k w (Z.of_int 20))]
          (bv_add x (atom "y")) in
  print_endline "333";
  let _r = s1.eval [] x in

  let m = get_expr s x in
  let a = to_bits w true m in
  printf "%s\n" (Z.to_string a);

  let m = get_expr s x in
  let a = to_bits w true m in
  printf "%s\n" (Z.to_string a);




  ack_command s (declare_datatype "X" [] [ ("A",[]); ("B",[]) ]);
  let y = ack_command s (declare "y" (atom "X")); atom "y" in
  check_sat s;
  let (c,_args) = to_con (get_expr s y) in
  print_endline c;
  let p = ack_command s (declare "p" t_int); atom "p" in
  ack_command s (assume (lt p (num_k 0)));
  check_sat s;
  let m = get_expr s p in
  let p = to_z m in
  print_endline (Z.to_string p);
  let q = ack_command s (declare "q" t_real); atom "q" in
  ack_command s (assume (eq (num_mul (num_k 2) q) (num_k (-5))));
  check_sat s;
  let m = get_expr s q in
  let q = to_q m in
  print_endline (Q.to_string q);

  ack_command s (declare_datatype "list" ["a"]
    [ ("nil",[])
    ; ("cons",[("head",atom "a"); ("tail", app_ "list" [atom "a"])])
    ]);

  s.stop ()

let _ = main()
