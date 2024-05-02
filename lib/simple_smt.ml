open Printf
open Sexplib

(** {1 SMT Basics } *)

type sexp = Sexp.t

let atom f: sexp                = Sexp.Atom f
let list (xs: sexp list): sexp  = Sexp.List xs

(** Apply a function to some arguments. *)
let app f args =
  if List.is_empty args then f else list (f :: args)

(** Apply a function to some arguments *)
let app_ f (args: sexp list): sexp = app (atom f) args

(** Non-negative numeric constant. *)
let nat_k x = atom (string_of_int x)

(** Non-negative numeric constant. *)
let nat_zk x = atom (Z.to_string x)

(** Int-indexed family *)
let fam f is = list (atom "_" :: atom f :: List.map nat_k is)

(** Attributes *)
let named x e = app_ "!" [e; atom ":named"; atom x ]

(** Symbols are either simple or quoted (c.f. SMTLIB v2.6 S3.1).
This predicate indicates whether a character is allowed in a simple 
symbol.  Note that only ASCII letters are allowed. *)
let allowed_simple_char c =
  let co = Char.code c in
  let in_range a b = Char.code a <= co && co <= Char.code b in
  in_range 'a' 'z' ||
  in_range 'A' 'Z' ||
  in_range '0' '9' ||
  String.contains "~!@$%^&*_-+=<>.?/" c

let is_simple_symbol s =
  not (String.equal "" s) && String.for_all allowed_simple_char s

let quote_symbol s =
  if is_simple_symbol s
    then s
    else "|" ^ s ^ "|"

(** Make an SMT name, quoting if needed. Note that even with quoting
the name should not contain pipe (|) or backslash (\) *)
let symbol x = atom (quote_symbol x)









(** {1 Booleans } *)

(** The type of booleans. *)
let t_bool = atom "Bool"

(** Boolean constant *)
let bool_k b = atom (if b then "true" else "false")

(** If-then-else. This is polymorphic and can be used to construct any term. *)
let ite x y z = app_ "ite" [x;y;z]

(** Arguments are equal . *)
let eq x y = app_ "=" [x;y]

(** All arguments are different *)
let distinct xs = if List.is_empty xs then bool_k true else app_ "distinct" xs

(** Logical negation. *)
let bool_not p = app_ "not" [p]

(** Conjunction. *)
let bool_and p q = app_ "and" [p;q]

(** Conjunction. *)
let bool_ands ps = if List.is_empty ps then bool_k true else app_ "and" ps

(** Disjunction. *)
let bool_or p q = app_ "or" [p;q]

(** Disjunction. *)
let bool_ors ps = if List.is_empty ps then bool_k false else app_ "or" ps

(** Exclusive-or. *)
let bool_xor p q = app_ "xor" [p;q]

(** Implication. *)
let bool_implies p q = app_ "=>" [p;q]




(** {1 Integers and Reals} *)

(** The type of integers. *)
let t_int = atom "Int"

(** The type of reals. *)
let t_real = atom "Real"

(** Numeric negation *)
let num_neg x = app_ "-" [x]

(** Numeric constant *)
let num_k x = if x < 0 then num_neg (nat_k (-x)) else nat_k x

(** Numeric constant *)
let num_zk x = if Z.lt x Z.zero then num_neg (nat_zk (Z.neg x)) else nat_zk x

(** Division of real numbers. *)
let real_div x y = app_ "/" [x;y]

(** Numeric constant *)
let num_qk (q: Q.t) = real_div (num_zk q.num) (num_zk q.den)

(** Greater-then for numbers *)
let gt x y = app_ ">" [x;y]

(** Less-then for num *)
let lt x y = app_ "<" [x;y]

(** Greater-than-or-equal-to for numbers *)
let geq x y = app_ ">=" [x;y]

(** Less-than-or-equal-to for numbers *)
let leq x y = app_ "<=" [x;y]

(** Numeric addition *)
let num_add x y = app_ "+" [x;y]

(** Numeric addition *)
let num_adds xs = if List.is_empty xs then num_k 0 else app_ "+" xs

(** Numeric subtraction *)
let num_sub x y = app_ "-" [x;y]

(** Numeric multiplication. *)
let num_mul x y = app_ "*" [x;y]

(** Numeric absolute value. *)
let num_abs x = app_ "abs" [x]

(** Numeric division. *)
let num_div x y = app_ "div" [x;y]

(** Numeric modulus. *)
let num_mod x y = app_ "mod" [x;y]

(** Is the number divisible by the given constant. *)
let num_divisible x n = app (fam "divisible" [n]) [x]


(** real Satisfies [real_to_int x <= x] (i.e., this is like [floor]) *)
let real_to_int e = app_ "to_int" [e]

(** Promote an integer to a real *)
let int_to_real e = app_ "to_real" [e]


(** {1 Bit-vectors} *)

(** The type of bit vectors. *)
let t_bits w = fam "BitVec" [w]

(** A bit-vector represented in binary.
- The number should be non-negative.
- The number should not exceed the number of bits.
*)
let bv_nat_bin w v = atom ("#b" ^ Z.format ("0" ^ string_of_int w ^ "b") v)

(** A bit-vector represented in hex.
- The number should be non-negative.
- The number should not exceed the number of bits.
- The width should be a multiple of 4.
*)
let bv_nat_hex w v = atom ("#x" ^ Z.format ("0" ^ string_of_int (w/4) ^ "x") v)

(** Bit vector arithmetic negation. *)
let bv_neg x = app_ "bvneg" [x]

(** A bit-vector represented in binary.
The number should fit in the given number of bits. *)
let bv_bin w v =
  if Z.geq v Z.zero
    then bv_nat_bin w v
    else bv_neg (bv_nat_bin w (Z.neg v))

(** A bit-vector represented in hex .
- The number should fit in the given number of bits.
- The width should be a multiple of 4. *)
let bv_hex w v =
  if Z.geq v Z.zero
    then bv_nat_hex w v
    else bv_neg (bv_nat_hex w (Z.neg v))

(** Make a bit-vector litera.  Uses hex representation if the size
is a multiple of 4, and binary otherwise. *)
let bv_k w v =
  if w mod 4 = 0
    then bv_hex w v
    else bv_bin w v



(** Unsigned less-than on bit-vectors. *)
let bv_ult x y = app_ "bvult" [x;y]

(** Unsigned less-than-or-equal on bit-vectors. *)
let bv_uleq x y = app_ "bvule" [x;y]

(** Signed less-than on bit-vectors. *)
let bv_slt x y = app_ "bvslt" [x;y]

(** Signed less-than-or-equal on bit-vectors. *)
let bv_sleq x y = app_ "bvsle" [x;y]

(** Bit vector concatenation. *)
let bv_concat x y = app_ "concat" [x;y]

(** Extend to the signed equivalent bitvector by the given number of bits. *)
let bv_sign_extend i x = app (fam "sign_extend" [i]) [x]

(** Zero extend by the given number of bits. *)
let bv_zero_extend i x = app (fam "zero_extend" [i]) [x]

(** Extract a sub-sequence of a bit vector. *)
let bv_extract x y z = app (fam "extract" [y;z]) [ x ]

(** Bitwise negation. *)
let bv_not x = app_ "bvnot" [x]

(** Bitwise conjuction. *)
let bv_and x y = app_ "bvand" [x;y]

(** Bitwise disjunction. *)
let bv_or x y = app_ "bvor" [x;y]

(** Bitwise exclusive or. *)
let bv_xor x y = app_ "bvxor" [x;y]

(** Addition of bit vectors. *)
let bv_add x y = app_ "bvadd" [x;y]

(** Subtraction of bit vectors. *)
let bv_sub x y = app_ "bvsub" [x;y]

(** Multiplication of bit vectors. *)
let bv_mul x y = app_ "bvmul" [x;y]

(** Bit vector unsigned division. *)
let bv_udiv x y = app_ "bvudiv" [x;y]

(** Bit vector unsigned reminder. *)
let bv_urem x y = app_ "bvurem" [x;y]

(** Bit vector signed division. *)
let bv_sdiv x y = app_ "bvsdiv" [x;y]

(** Bit vector signed reminder. *)
let bv_srem x y = app_ "bvsrem" [x;y]

(** Shift left. *)
let bv_shl x y = app_ "bvshl" [x;y]

(** Logical shift right. *)
let bv_lshr x y = app_ "bvlshr" [x;y]

(** Arithemti shift right (copies most significant bit). *)
let bv_ashr x y = app_ "bvashr" [x;y]



(** {1 Arrays} *)

(** The type of arrays. *)
let t_array x y = app_ "Array" [x;y]

(** Get an elemeent of an array. *)
let arr_select x y = app_ "select" [x;y]

(** Update an array *)
let arr_store x y z = app_ "store" [x;y;z]




(** {1 Solver} *)


(** A connection to a solver *)
type solver =
  { command:    sexp -> sexp
  ; stop:       unit -> Unix.process_status
  ; force_stop: unit -> Unix.process_status
  }

exception UnexpectedSolverResponse of sexp

(** Issue a command and wait for it to succeed.
    Throws {! UnexpectedSolverResponse} *)
let ack_command (s: solver) cmd =
  match s.command cmd with
  | Sexp.Atom "success" -> ()
  | ans                 -> raise (UnexpectedSolverResponse ans)

let simple_command s xs = ack_command s (list (List.map atom xs))
let set_option s x y    = simple_command s [ "set-option"; x; y ]
let set_logic s l       = simple_command s [ "set-logic"; l ]
let push s              = simple_command s [ "push"; "1" ]
let pop s               = simple_command s [ "pop"; "1" ]

(** Declare a sort *)
let declare_sort s f arity =
  let e = atom f in
  ack_command s (app_ "declare-sort" [ e; atom (string_of_int arity) ]);
  e

(** Declare a function *)
let declare_fun s f ps r =
  let e = atom f in
  ack_command s (app_ "declare-fun" [ e; List ps; r ]);
  e

(** Declare a constant *)
let declare s f t = declare_fun s f [] t

type con_field = string * sexp

(** Declare an ADT using the format introduced in SmtLib 2.6. *)
let declare_datatype s name type_params cons =
  let mk_field ((f,argTy):con_field)  = list [atom f; argTy] in
  let mk_con (c,fs)       = list (atom c :: List.map mk_field fs) in
  let mk_cons             = list (List.map mk_con cons) in
  let def =
    match type_params with
    | [] -> mk_cons
    | _  -> app_ "par" [ List (List.map atom type_params); mk_cons ]
  in
  ack_command s (app_ "declare-datatype" [ atom name; def ])

(** Add an assertion *)
let assume s e = ack_command s (app_ "assert" [e])


type result = Unsat | Unknown | Sat
  [@@deriving show]

let check s =
  match s.command (Sexp.of_string "(check-sat)") with
  | Sexp.Atom "unsat" -> Unsat
  | Sexp.Atom "sat" -> Sat
  | Sexp.Atom "unknown" -> Unknown
  | ans -> raise (UnexpectedSolverResponse ans)

(** {2 Decoding Results} *)

(** Get all definitions currently in scope. Only valid after a [Sat] result.
See also [model_eval] *)
let get_model s = s.command (list [ atom "get-model" ])

(** Get the values of some s-expressions. Only valid after a 'Sat' result. *)
let get_exprs s vals: sexp list =
  let res = s.command (list [ atom "get-value"; list vals ]) in
  match res with
  | Sexp.List xs ->
    let get_val pair =
          match pair with
          | Sexp.List [_;x] -> x
          | _ -> raise (UnexpectedSolverResponse res)
    in List.map get_val xs
  | _ -> raise (UnexpectedSolverResponse res)

let get_expr s v =
  let res = s.command (list [ atom "get-value"; list [v]]) in
  match res with
  | Sexp.List [ Sexp.List [_;x] ] -> x
  | _ -> raise (UnexpectedSolverResponse res)

(** Try to decode an s-expression as a boolean *)
let to_bool (exp: sexp) =
  match exp with
  | Sexp.Atom "true"  -> true
  | Sexp.Atom "false" -> false
  | _ -> raise (UnexpectedSolverResponse exp)

(** Try to decode an s-expression as a bitvector of the given width.
The 2nd argument indicates if the number is signed.
*)
let to_bits w signed (exp: sexp) =
  let bad () = raise (UnexpectedSolverResponse exp) in
  let get_num base digs =
    try
      let z = Z.of_string_base base digs in
      if signed then Z.signed_extract z 0 w else z
    with Invalid_argument _ -> bad ()
  in
  match exp with
  | Sexp.Atom s ->
    let tot_len = String.length s in
    if tot_len < 2 || not (Char.equal (String.get s 0) '#') then bad () else ();
    let dig_len = tot_len - 2 in
    let digs = String.sub s 2 dig_len in
    begin match String.get s 1 with
    | 'b' -> if     dig_len = w then get_num  2 digs else bad ()
    | 'x' -> if 4 * dig_len = w then get_num 16 digs else bad ()
    | _   -> bad ()
    end
  | _ -> bad ()

(** Try to decode an s-expression as an integer. *)
let to_z (exp: sexp) =
  let parse do_neg s =
        try
          let r = Z.of_string s in
          if do_neg then Z.neg r else r
        with Invalid_argument _ -> raise (UnexpectedSolverResponse exp)
  in
  match exp with
  | Sexp.Atom s -> parse false s
  | Sexp.List [ Sexp.Atom "-"; Sexp.Atom s ] -> parse true s
  | _ -> raise (UnexpectedSolverResponse exp)

(** Try to decode an s-expression as a rational number. *)
let to_q (exp: sexp) =
  let bad () = raise (UnexpectedSolverResponse exp) in
  let rec eval e =
    match e with
    | Sexp.Atom s -> Q.of_string s
    | Sexp.List [ Sexp.Atom "-"; e1] -> Q.neg (eval e1)
    | Sexp.List [ Sexp.Atom "/"; e1; e2] -> Q.div (eval e1) (eval e2)
    | _ -> bad ()
  in
  try eval exp with Invalid_argument _ -> bad ()


(** Try to decode an s-expression as a particular constructor number. *)
let to_con (exp: sexp): string * sexp list =
  let bad () = raise (UnexpectedSolverResponse exp) in
  match exp with
  | Sexp.Atom x -> (x, [])
  | Sexp.List xs ->
    match xs with
    | y :: ys ->
      begin match y with
      | Sexp.Atom x -> (x,ys)
      | Sexp.List [_; Sexp.Atom x; _] -> (x,ys) (*cvc5: (as con ty)*)
      | _ -> bad ()
      end
    | _ -> bad ()


(** {2 Creating Solvers} *)

type solver_config =
  { exe: string
  ; opts: string list
  }

let new_solver (cfg: solver_config): solver =
  let args = Array.of_list (cfg.exe :: cfg.opts) in
  let proc = Unix.open_process_args_full cfg.exe args [| |] in
  let pid = Unix.process_full_pid proc in
  let (in_chan, out_chan, in_err_chan) = proc in
  let in_buf = Lexing.from_channel in_chan in

  let send_string s =
        printf "[->] %s\n%!" s;
        fprintf out_chan "%s\n%!" s in

  let send_command c =
        send_string (Sexp.to_string c);
        let ans = match Sexp.scan_sexp_opt in_buf with
                    | Some x -> x
                    | None -> Sexp.Atom (In_channel.input_all in_err_chan)
        in printf "[<-] %s\n%!" (Sexp.to_string ans); ans
  in

  let stop_command () =
        send_string "(exit)";
        Unix.close_process_full proc
  in
  let force_stop_command () =
        Unix.kill pid 9;
        Unix.close_process_full proc
  in
  let s =
    { command = send_command
    ; stop = stop_command
    ; force_stop = force_stop_command
    }
  in
    set_option s ":print-success" "true";
    set_option s ":produce-models" "true";
    s

(* Start a new solver process, used to evaluate expressions in a model.
Unlike a normal solver, the [command] field expects an expression to
evalute, and gives the value of the expression in the context of the model. *)
let model_eval (cfg: solver_config) (m: sexp) =
  match m with
  | Sexp.List defs ->
    let s = new_solver cfg in
    List.iter (ack_command s) defs;
    begin match check s with
    | Sat ->
      { command    = get_expr s
      ; stop       = s.stop
      ; force_stop = s.force_stop
      }
    | _ -> raise (UnexpectedSolverResponse m)
    end
  | _ -> raise (UnexpectedSolverResponse m)


let cvc5 : solver_config =
  { exe = "cvc5"
  ; opts = ["--incremental"]
  }

let z3 : solver_config =
  { exe = "z3"
  ; opts = ["-in"; "-smt2" ]
  }
