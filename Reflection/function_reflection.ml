(* Function reflection for concrete Lisp programs: the deep theory, executable
   evaluator, and trusted registration are kept together in this file. *)
needs "define.ml";;

(* ------------------------------------------------------------------------- *)
(* Deep embedding and defining equations.                                    *)
(* ------------------------------------------------------------------------- *)

(* One untyped datatype for Lisp code and data. Function bodies are a proper
   S-expression list; each takes one argument at environment index zero.
   Bare symbols are local variable indices; symbols at the head of a form
   select a special form/primitive. No expression or program datatype. *)
let lisp_sexp_INDUCT,lisp_sexp_RECURSION = define_type
 "lisp_sexp = LNil | LBoolean bool | LNumber num | LSymbol num
            | LPair lisp_sexp lisp_sexp";;

let LISP_VALUE_DISTINCT = distinctness "lisp_sexp";;
let LISP_VALUE_INJ = injectivity "lisp_sexp";;

let lisp_bind = new_recursive_definition option_RECURSION
 `(lisp_bind NONE (f:A->B option) = NONE) /\
  (lisp_bind (SOME x) f = f x)`;;

let lisp_lookup = new_recursive_definition list_RECURSION
 `(lisp_lookup [] n = (NONE:A option)) /\
  (lisp_lookup (CONS x xs) n =
     if n = 0 then SOME x else lisp_lookup xs (PRE n))`;;

let lisp_number = new_recursive_definition lisp_sexp_RECURSION
 `(lisp_number LNil = NONE) /\ (lisp_number (LBoolean flag) = NONE) /\
  (lisp_number (LNumber n) = SOME n) /\ (lisp_number (LSymbol n) = NONE) /\
  (lisp_number (LPair a b) = NONE)`;;

let lisp_car = new_recursive_definition lisp_sexp_RECURSION
 `(lisp_car LNil = NONE) /\ (lisp_car (LBoolean flag) = NONE) /\
  (lisp_car (LNumber n) = NONE) /\ (lisp_car (LSymbol n) = NONE) /\
  (lisp_car (LPair a b) = SOME a)`;;

let lisp_cdr = new_recursive_definition lisp_sexp_RECURSION
 `(lisp_cdr LNil = NONE) /\ (lisp_cdr (LBoolean flag) = NONE) /\
  (lisp_cdr (LNumber n) = NONE) /\ (lisp_cdr (LSymbol n) = NONE) /\
  (lisp_cdr (LPair a b) = SOME b)`;;

let lisp_iscons = new_recursive_definition lisp_sexp_RECURSION
 `(lisp_iscons LNil = F) /\ (lisp_iscons (LBoolean flag) = F) /\
  (lisp_iscons (LNumber n) = F) /\ (lisp_iscons (LSymbol n) = F) /\
  (lisp_iscons (LPair a b) = T)`;;

let lisp_branch = new_recursive_definition lisp_sexp_RECURSION
 `(lisp_branch LNil x y = (NONE:lisp_sexp option)) /\
  (lisp_branch (LBoolean flag) x y = if flag then x else y) /\
  (lisp_branch (LNumber n) x y = NONE) /\
  (lisp_branch (LSymbol n) x y = NONE) /\
  (lisp_branch (LPair a b) x y = NONE)`;;

(* Direct evaluation. Recursive expression calls are on strict subexpressions;
   recursive function calls go through call, where lisp_exec accounts for fuel. *)
let lisp_run_equations =
 `(lisp_run LNil call env = SOME LNil) /\
  (lisp_run (LBoolean flag) call env = SOME (LBoolean flag)) /\
  (lisp_run (LNumber n) call env = SOME (LNumber n)) /\
  (lisp_run (LSymbol n) call env = lisp_lookup env n) /\
  (lisp_run (LPair op args) call env =
    match args with
    | LPair a LNil ->
        if op = LSymbol 0 then SOME a else
        if op = LSymbol 4 then lisp_bind (lisp_run a call env) lisp_car else
        if op = LSymbol 5 then lisp_bind (lisp_run a call env) lisp_cdr else
        if op = LSymbol 6 then lisp_bind (lisp_run a call env)
          (\v. SOME (LBoolean (lisp_iscons v))) else NONE
    | LPair a (LPair b LNil) ->
        if op = LSymbol 1 then lisp_bind (lisp_run a call env)
          (\v. lisp_run b call (CONS v env)) else
        if op = LSymbol 3 then lisp_bind (lisp_run a call env)
          (\x. lisp_bind (lisp_run b call env) (\y. SOME (LPair x y))) else
        if op = LSymbol 7 then lisp_bind (lisp_run a call env)
          (\x. lisp_bind (lisp_run b call env) (\y. SOME (LBoolean (x = y)))) else
        if op = LSymbol 8 then lisp_bind (lisp_number a)
          (\fn. lisp_bind (lisp_run b call env) (call fn)) else NONE
    | LPair c (LPair a (LPair b LNil)) ->
        if op = LSymbol 2 then lisp_bind (lisp_run c call env)
          (\v. lisp_branch v (lisp_run a call env) (lisp_run b call env)) else NONE
    | _ -> NONE)`;;

let lisp_size = new_recursive_definition lisp_sexp_RECURSION
 `(lisp_size LNil = 1) /\ (lisp_size (LBoolean flag) = 1) /\
  (lisp_size (LNumber n) = 1) /\ (lisp_size (LSymbol n) = 1) /\
  (lisp_size (LPair a b) = 1 + lisp_size a + lisp_size b)`;;

let LISP_SUBTERMS = prove
 (`(!op a. lisp_size a < lisp_size (LPair op (LPair a LNil))) /\
   (!op a b. lisp_size a < lisp_size (LPair op (LPair a (LPair b LNil))) /\
             lisp_size b < lisp_size (LPair op (LPair a (LPair b LNil)))) /\
   (!op a b c.
      lisp_size a < lisp_size (LPair op (LPair a (LPair b (LPair c LNil)))) /\
      lisp_size b < lisp_size (LPair op (LPair a (LPair b (LPair c LNil)))) /\
      lisp_size c < lisp_size (LPair op (LPair a (LPair b (LPair c LNil)))))`,
  REWRITE_TAC[lisp_size] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN ARITH_TAC);;

let lisp_run =
  let fn = repeat rator (lhs (hd(conjuncts lisp_run_equations))) in
  let clauses = list_mk_conj (map (fun c ->
    list_mk_forall(subtract (frees c) [fn],c)) (conjuncts lisp_run_equations)) in
  let existence = prove_general_recursive_function_exists (mk_exists(fn,clauses)) in
  let termination = prove(hd(hyp existence),
    EXISTS_TAC `MEASURE (\x:lisp_sexp#(num->lisp_sexp->lisp_sexp option)#
                               (lisp_sexp list). lisp_size (FST x))` THEN
    REWRITE_TAC[WF_MEASURE; admissible; MEASURE; FORALL_PAIR_THM; FST] THEN
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    REPEAT(FIRST_X_ASSUM (fun th ->
      let l,r = dest_eq(concl th) in
      if is_var r && not(vfree_in r l) then SUBST_ALL_TAC (SYM th)
      else if is_var l && not(vfree_in l r) then SUBST_ALL_TAC th
      else failwith "not a variable substitution")) THEN
    ASM_SIMP_TAC[LISP_SUBTERMS; LISP_VALUE_INJ; LISP_VALUE_DISTINCT;
                 FUN_EQ_THM]) in
  new_specification ["lisp_run"] (PROVE_HYP termination existence);;

let lisp_functions = new_recursive_definition lisp_sexp_RECURSION
 `(lisp_functions LNil = SOME []) /\
  (lisp_functions (LBoolean flag) = NONE) /\
  (lisp_functions (LNumber n) = NONE) /\
  (lisp_functions (LSymbol n) = NONE) /\
  (lisp_functions (LPair a b) =
     lisp_bind (lisp_functions b) (\xs. SOME (CONS a xs)))`;;

let lisp_exec = new_recursive_definition num_RECURSION
 `(lisp_exec 0 program fn input = NONE) /\
  (lisp_exec (SUC n) program fn input =
     lisp_bind (lisp_functions program) (\bodies.
       lisp_bind (lisp_lookup bodies fn) (\body.
         lisp_run body (lisp_exec n program) [input])))`;;

let lisp_eval = new_definition
 `lisp_eval fuel program input = lisp_exec fuel program 0 input`;;

let lisp_returns = new_definition
 `lisp_returns result expected <=> result = NONE \/ result = SOME expected`;;

(* Construction abbreviations only: all these return the SAME sexp type. *)
let lisp_list = new_recursive_definition list_RECURSION
 `(lisp_list [] = LNil) /\
  (lisp_list (CONS x xs) = LPair x (lisp_list xs))`;;
let lisp_form = new_definition
 `lisp_form tag xs = LPair (LSymbol tag) (lisp_list xs)`;;
let LQuote = new_definition `LQuote v = lisp_form 0 [v]`;;
let LVar = new_definition `LVar n = LSymbol n`;;
let LLet = new_definition `LLet a b = lisp_form 1 [a;b]`;;
let LIf = new_definition `LIf c a b = lisp_form 2 [c;a;b]`;;
let LCons = new_definition `LCons a b = lisp_form 3 [a;b]`;;
let LCar = new_definition `LCar x = lisp_form 4 [x]`;;
let LCdr = new_definition `LCdr x = lisp_form 5 [x]`;;
let LIsCons = new_definition `LIsCons x = lisp_form 6 [x]`;;
let LEqual = new_definition `LEqual a b = lisp_form 7 [a;b]`;;
let LCall = new_definition `LCall n x = lisp_form 8 [LNumber n;x]`;;
let LProgram = new_definition `LProgram bodies = lisp_list bodies`;;
let LISP_SYNTAX =
 [LQuote; LVar; LLet; LIf; LCons; LCar; LCdr; LIsCons; LEqual; LCall;
  LProgram; lisp_form; lisp_list];;

(* Derived evaluation equations for the S-expression abbreviations. These are
   theorems about the one untyped representation, not another interpreter. *)
let LISP_RUN_CLAUSES = prove
 (`(lisp_run (LQuote v) call env = SOME v) /\
   (lisp_run (LVar n) call env = lisp_lookup env n) /\
   (lisp_run (LLet a b) call env =
      lisp_bind (lisp_run a call env) (\x. lisp_run b call (CONS x env))) /\
   (lisp_run (LIf c a b) call env =
      lisp_bind (lisp_run c call env) (\x.
        lisp_branch x (lisp_run a call env) (lisp_run b call env))) /\
   (lisp_run (LCons a b) call env =
      lisp_bind (lisp_run a call env) (\x.
        lisp_bind (lisp_run b call env) (\y. SOME (LPair x y)))) /\
   (lisp_run (LCar a) call env = lisp_bind (lisp_run a call env) lisp_car) /\
   (lisp_run (LCdr a) call env = lisp_bind (lisp_run a call env) lisp_cdr) /\
   (lisp_run (LIsCons a) call env =
      lisp_bind (lisp_run a call env) (\x. SOME (LBoolean (lisp_iscons x)))) /\
   (lisp_run (LEqual a b) call env =
      lisp_bind (lisp_run a call env) (\x.
        lisp_bind (lisp_run b call env) (\y. SOME (LBoolean (x = y))))) /\
   (lisp_run (LCall n a) call env = lisp_bind (lisp_run a call env) (call n))`,
  REWRITE_TAC (LISP_SYNTAX @
    [lisp_run; lisp_number; lisp_bind; LISP_VALUE_DISTINCT; LISP_VALUE_INJ;
      ARITH_EQ]));;

(* ------------------------------------------------------------------------- *)
(* Executable evaluator over the same concrete HOL S-expressions.             *)
(* It has no access to thm and constructs no intermediate expression AST.    *)
(* ------------------------------------------------------------------------- *)

module Reflection_eval (Term : sig
  type t
  val constant_name : t -> string
  val dest_comb : t -> t * t
  val constant : string -> t
  val combine : t * t -> t
end) = struct
  let node tm =
    let rec strip args t =
      if (try ignore(Term.constant_name t); true with Failure _ -> false)
      then Term.constant_name t,args
      else let f,x = Term.dest_comb t in strip (x::args) f in
    strip [] tm

  let rec natural tm = match node tm with
    | "_0",[] -> 0
    | "NUMERAL",[n] -> natural n
    | ("BIT0" | "BIT1" as bit),[n] ->
        let n = natural n in
        if n > (max_int - 1) / 2 then failwith "Lisp: numeral out of range";
        2 * n + (if bit = "BIT1" then 1 else 0)
    | _ -> failwith "Lisp: expected a concrete numeral"

  let bool b = Term.combine(Term.constant "LBoolean",
                            Term.constant (if b then "T" else "F"))
  let pair a b = Term.combine(Term.combine(Term.constant "LPair",a),b)
  let bind x f = match x with None -> None | Some v -> f v
  let rec lookup xs n = match xs with
    | [] -> None | x::rest -> if n = 0 then Some x else lookup rest (n - 1)

  let rec check tm = match node tm with
    | "LNil",[] -> ()
    | "LBoolean",[b] ->
        (match node b with "T",[] | "F",[] -> ()
         | _ -> failwith "Lisp: expected a concrete Boolean")
    | ("LNumber" | "LSymbol"),[n] -> ignore(natural n)
    | "LPair",[a;b] -> check a; check b
    | _ -> failwith "Lisp: expected a concrete S-expression"

  let rec equal a b = match node a,node b with
    | ("LNil",[]),("LNil",[]) -> true
    | ("LBoolean",[a]),("LBoolean",[b]) -> node a = node b
    | ("LNumber",[a]),("LNumber",[b])
    | ("LSymbol",[a]),("LSymbol",[b]) -> natural a = natural b
    | ("LPair",[a;b]),("LPair",[c;d]) -> equal a c && equal b d
    | _ -> false

  let rec list tm = match node tm with
    | "LNil",[] -> Some []
    | "LPair",[x;xs] -> bind (list xs) (fun xs -> Some(x::xs))
    | _ -> None

  let eval fuel program input =
    check program; check input;
    let bodies = list program in
    let rec run fuel env tm =
      if fuel = 0 then None else
      match node tm with
      | "LNil",[] | "LBoolean",[_] | "LNumber",[_] -> Some tm
      | "LSymbol",[n] -> lookup env (natural n)
      | "LPair",[op;args] ->
          bind (list args) (fun args ->
            match node op,args with
            | ("LSymbol",[n]),args ->
                let eval = run fuel env in
                (match natural n,args with
                 | 0,[x] -> Some x
                 | 1,[x;body] -> bind (eval x) (fun v -> run fuel (v::env) body)
                 | 2,[c;x;y] -> bind (eval c) (fun v -> match node v with
                     | "LBoolean",[b] ->
                         (match node b with "T",[] -> eval x | "F",[] -> eval y
                          | _ -> None)
                     | _ -> None)
                 | 3,[a;b] -> bind (eval a) (fun a -> bind (eval b) (fun b -> Some(pair a b)))
                 | 4,[x] -> bind (eval x) (fun v -> match node v with
                     | "LPair",[a;_] -> Some a | _ -> None)
                 | 5,[x] -> bind (eval x) (fun v -> match node v with
                     | "LPair",[_;b] -> Some b | _ -> None)
                 | 6,[x] -> bind (eval x) (fun v -> Some(bool(match node v with
                     | "LPair",[_;_] -> true | _ -> false)))
                 | 7,[a;b] -> bind (eval a) (fun a -> bind (eval b) (fun b -> Some(bool(equal a b))))
                 | 8,[fn;x] -> (match node fn with
                     | "LNumber",[n] -> bind (eval x) (fun input ->
                         bind bodies (fun bodies -> bind (lookup bodies (natural n))
                           (fun body -> run (fuel - 1) [input] body)))
                     | _ -> None)
                 | _ -> None)
            | _ -> None)
      | _ -> None in
    bind bodies (fun bodies -> bind (lookup bodies 0) (run fuel [input]))
end;;

(* ------------------------------------------------------------------------- *)
(* Trusted binding of the definition above to its executable handler.         *)
(* ------------------------------------------------------------------------- *)

module Lisp_evaluator = Reflection_eval(struct
  type t = term
  let constant_name tm = fst(dest_const tm)
  let dest_comb = dest_comb
  let constant n = mk_const(n,[])
  let combine = mk_comb
end);;

let lisp_evaluator application =
  match snd(strip_comb application) with
  | [fuel_term; program; input] ->
      let fuel = Lisp_evaluator.natural fuel_term in
      let result = Lisp_evaluator.eval fuel program input in
      (match result with
       | None -> mk_const("NONE",[`:lisp_sexp`,`:A`])
       | Some value -> mk_comb(mk_const("SOME",[`:lisp_sexp`,`:A`]),value))
  | _ -> failwith "lisp_evaluator: expected fuel, program, and input";;

(* lisp_eval is the definition theorem identifying the HOL operation.
   lisp_evaluator is the executable handler FUNCTION_REFLECT will look up. *)
reflect_function lisp_eval lisp_evaluator;;
