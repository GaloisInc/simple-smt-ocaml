open Printf
open Simple_smt


let main () =
  printf "Start\n%!";
  let s = new_solver cvc5 in
  let _ = check s in
  let w = 8 in
  let x = declare s "x" (t_bits w) in
  assume s (eq x (bv_k w (Z.of_int (-17))));
  let Sat = check s in
  let [ m ] = get_exprs s [ x ] in
  let Some a = to_bits w true m in
  printf "%s\n" (Z.to_string a);
  declare_datatype s "X" [] [ ("A",[]); ("B",[]) ];
  let y = declare s "y" (atom "X") in
  let Sat = check s in
  let _ = get_exprs s [ y ] in
  let p = declare s "p" t_int in
  assume s (lt p (num_k 0));
  let Sat = check s in
  let [ m ] = get_exprs s [ p ] in
  let Some p_ = to_z m in
  print_endline (Z.to_string p_);
  let q = declare s "q" t_real in
  assume s (eq (num_mul (num_k 2) q) (num_k (-5)));
  let Sat = check s in
  let [ m ] = get_exprs s [ q ] in
  let Some q = to_q m in
  print_endline (Q.to_string q);

  declare_datatype s "list" ["a"]
    [ ("nil",[])
    ; ("cons",[("head",atom "a"); ("tail", app_ "list" [atom "a"])])
    ];

  s.stop ()

let _ = main()
