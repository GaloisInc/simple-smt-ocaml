open Printf
open Simple_smt

exception NotSat

let check_sat s =
  match check s with
  | Sat -> ()
  | _   -> raise NotSat


let main () =
  printf "Start\n%!";

  let s = new_solver { z3 with log = printf_log } in

  ack_command s (declare_datatype "list" ["a"]
    [ ("nil", [])
    ; ("cons", [ ("head", atom "a"); ("tail", app_ "list" [atom "a"]) ])
    ]);

  ack_command s (declare_datatypes

    [ ( "zig"
      , ["a"]
      , [ ("nil_zig", [])
        ; ("cons", [ ("head", atom "a"); ("tail", app_ "zag" [atom "a"]) ])
        ]
      )
    ; ( "zag"
      , ["a"]
      , [ ("nil_zag", [])
        ; ("cons", [ ("head", atom "a"); ("tail", app_ "zig" [atom "a"]) ])
        ]
      )
    ]);





  ack_command s (push 1);
  ack_command s (declare "xs" (app_ "list" [t_int]));
  ack_command s (assume (is_con "cons" (atom "xs")));
  check_sat s;
  ack_command s (pop 1);

  ack_command s (assume (eq (let_ [("x", int_k 2)] (atom "x")) (int_k 2)));
  check_sat s;

  ack_command s (define "zz" t_real (real_k (Q.of_int 0)));

  let ext = s.config.exts in
  let sx = ack_command s (declare "sx" (t_set t_int)); atom "sx" in
  let sy = set_empty ext t_int in
  let sz = set_universe ext t_int in
  ack_command s (assume (eq sx sy));
  ack_command s (assume (set_member ext (int_k 2) sz));
  ack_command s (assume (set_subset ext sx sy));
  check_sat s;
  let w = 8 in
  let f = ack_command s (declare_fun "f" [t_int] (t_bits w)); atom "f" in
  ack_command s (assume (eq (app f [int_k 2]) (bv_k w (Z.of_int 10))));
  ack_command s (assume (eq (app f [int_k 3]) (bv_k w (Z.of_int 11))));
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
  let _ = s1.stop () in

  let m = get_expr s x in
  let a = to_bits w true m in
  printf "%s\n" (Z.to_string a);

  let m = get_expr s x in
  let a = to_bits w true m in
  printf "%s\n" (Z.to_string a);



  ack_command s (declare_datatype "X" [] [ ("A",[("x",t_int)]); ("B",[]) ]);
  let y = ack_command s (declare "y" (atom "X")); atom "y" in
  ack_command s (assume (eq (int_k 0) (match_datatype y [ (PCon ("A",["a"]),atom"a")
                                                        ; (PCon ("B",[]),int_k 1)
                                                        ])));

  check_sat s;

  let (c,_args) = to_con (get_expr s y) in
  print_endline c;
  let p = ack_command s (declare "p" t_int); atom "p" in
  ack_command s (assume (num_lt p (int_k 0)));
  check_sat s;
  let m = get_expr s p in
  let p = to_z m in
  print_endline (Z.to_string p);
  let q = ack_command s (declare "q" t_real); atom "q" in
  ack_command s (assume (eq (num_mul (int_k 2) q) (int_k (-5))));
  check_sat s;
  let m = get_expr s q in
  let q = to_q m in
  print_endline (Q.to_string q);

  ack_command s (define "arr" (t_array t_int t_bool)
                (arr_const t_int t_bool (bool_k true)));
  let arr = atom "arr" in
  ack_command s (assume (arr_select arr (int_k 10)));
  check_sat s;
  let (xs,res) = to_array (get_expr s arr) in


  ack_command s (define "arr2" (t_array t_int t_int)
                      (arr_store
                          (arr_const t_int t_int (int_k 5))
                          (int_k 5) (int_k 10)
                      ));
  let arr2 = atom "arr2" in
  check_sat s;
  let (xs2,res2) = to_array (get_expr s arr2) in



  s.stop ()

let _ = main ()
