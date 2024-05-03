open Printf
open Simple_smt

exception NotSat

let check_sat s =
  match check s with
  | Sat -> ()
  | _   -> raise NotSat


let main () =
  printf "Start\n%!";

  let s = new_solver z3 in
  let ext = s.config.exts in
  let sx = declare s "sx" (t_set t_int) in
  let sy = set_empty ext t_int in
  let sz = set_universe ext t_int in
  assume s (eq sx sy);
  assume s (set_member ext (num_k 2) sz);
  assume s (set_subset ext sx sy);
  check_sat s;
  let w = 8 in
  let f = declare_fun s "f" [t_int] (t_bits w) in
  assume s (eq (app f [num_k 2]) (bv_k w (Z.of_int 10)));
  assume s (eq (app f [num_k 3]) (bv_k w (Z.of_int 11)));
  let x = declare s "x" (t_bits w) in
  assume s (eq x (bv_k w (Z.of_int (-17))));
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




  declare_datatype s "X" [] [ ("A",[]); ("B",[]) ];
  let y = declare s "y" (atom "X") in
  check_sat s;
  let (c,_args) = to_con (get_expr s y) in
  print_endline c;
  let p = declare s "p" t_int in
  assume s (lt p (num_k 0));
  check_sat s;
  let m = get_expr s p in
  let p = to_z m in
  print_endline (Z.to_string p);
  let q = declare s "q" t_real in
  assume s (eq (num_mul (num_k 2) q) (num_k (-5)));
  check_sat s;
  let m = get_expr s q in
  let q = to_q m in
  print_endline (Q.to_string q);

  declare_datatype s "list" ["a"]
    [ ("nil",[])
    ; ("cons",[("head",atom "a"); ("tail", app_ "list" [atom "a"])])
    ];

  s.stop ()

let _ = main()
