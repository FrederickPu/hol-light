needs "Examples/reflection_sat.ml";;

let rf_expect_failure f =
  let rejected = try ignore(f()); false with Failure _ -> true in
  if not rejected then failwith "Expected rejection";;

(* A separate user-defined operation and predicate: neither requires any
   knowledge of Lisp or the demo's formula datatype in the kernel. *)
let DEMO_FLIP_DEF = new_definition `demo_reflected_flip b = ~b`;;
let demo_flip_evaluator application =
  let input = rand application in
  if aconv input `T` then `F`
  else if aconv input `F` then `T`
  else failwith "demo_flip_evaluator: expected a concrete Boolean";;
reflect_function DEMO_FLIP_DEF demo_flip_evaluator;;

let demo_flip_execution = FUNCTION_REFLECT `demo_reflected_flip T`;;
if hyp demo_flip_execution <> [] ||
   not(aconv (concl demo_flip_execution) `demo_reflected_flip T = F`) then
  failwith "Custom function reflection failed";;
let demo_flip_checked = REWRITE_CONV[DEMO_FLIP_DEF] `demo_reflected_flip T`;;
if not(aconv (concl demo_flip_execution) (concl demo_flip_checked)) then
  failwith "Custom evaluator disagrees with its definition";;

let DEMO_PRED_DEF = new_definition `demo_reflected_pred b <=> b`;;
reflect_pred DEMO_PRED_DEF (fun proposition -> proposition);;
let demo_pred_reflected = PROOF_REFLECT (ASSUME `demo_reflected_pred p`);;
if hyp demo_pred_reflected <> [`demo_reflected_pred p`] ||
   not(aconv (concl demo_pred_reflected) `p:bool`) then
  failwith "Custom predicate reflection failed";;

if not(exists (equals_thm DEMO_FLIP_DEF) (function_reflections())) ||
   not(exists (equals_thm DEMO_PRED_DEF) (predicate_reflections())) ||
   not(exists (equals_thm lisp_eval) (function_reflections())) ||
   not(exists (equals_thm RF_PROVABLE_RULES) (predicate_reflections())) then
  failwith "Reflection registration evidence was not recorded";;

let registrations_before =
  length(function_reflections()),length(predicate_reflections());;
rf_expect_failure (fun () -> reflect_function DEMO_FLIP_DEF demo_flip_evaluator);;
rf_expect_failure (fun () -> reflect_pred DEMO_PRED_DEF (fun x -> x));;
rf_expect_failure (fun () -> reflect_function TRUTH (fun x -> x));;
rf_expect_failure (fun () -> reflect_function (REFL `p:bool`) (fun x -> x));;
rf_expect_failure (fun () -> reflect_function
  (ASSUME `demo_reflected_flip T = F`) demo_flip_evaluator);;
rf_expect_failure (fun () -> reflect_function
  (CONJ DEMO_FLIP_DEF DEMO_PRED_DEF) demo_flip_evaluator);;
if registrations_before <>
   (length(function_reflections()),length(predicate_reflections())) then
  failwith "Rejected registration changed the registry";;

rf_expect_failure (fun () -> FUNCTION_REFLECT `demo_reflected_flip p`);;
rf_expect_failure (fun () -> FUNCTION_REFLECT `demo_reflected_flip`);;
rf_expect_failure (fun () -> FUNCTION_REFLECT `~T`);;

let DEMO_WRONG_RESULT_DEF = new_definition `demo_wrong_result b <=> b`;;
reflect_function DEMO_WRONG_RESULT_DEF (fun _ -> `0`);;
rf_expect_failure (fun () -> FUNCTION_REFLECT `demo_wrong_result T`);;
let DEMO_OPEN_RESULT_DEF = new_definition `demo_open_result b <=> b`;;
reflect_function DEMO_OPEN_RESULT_DEF (fun _ -> `p:bool`);;
rf_expect_failure (fun () -> FUNCTION_REFLECT `demo_open_result T`);;
let DEMO_WRONG_PRED_DEF = new_definition `demo_wrong_pred b <=> b`;;
reflect_pred DEMO_WRONG_PRED_DEF (fun _ -> `0`);;
rf_expect_failure (fun () -> PROOF_REFLECT (ASSUME `demo_wrong_pred T`));;
let DEMO_NOT_PRED_DEF = new_definition `demo_not_pred n = SUC n`;;
rf_expect_failure (fun () -> reflect_pred DEMO_NOT_PRED_DEF (fun _ -> `T`));;

(* Registrations are keyed by the constant's full type, not its name alone. *)
let DEMO_POLY_DEF = new_definition `demo_reflected_id (x:A) = x`;;
reflect_function (INST_TYPE[bool_ty,`:A`] DEMO_POLY_DEF) rand;;
ignore(FUNCTION_REFLECT `demo_reflected_id T`);;
rf_expect_failure (fun () -> FUNCTION_REFLECT `demo_reflected_id 0`);;

(* Only convenience abbreviations are unfolded before entering the kernel. *)
let rf_test_execution tm =
  let expansion = REWRITE_CONV LISP_SYNTAX tm in
  TRANS expansion (FUNCTION_REFLECT (rhs(concl expansion)));;

(* Generic Lisp examples: identity, quotation, local bindings, data operations,
   branching, recursion, invalid operations and exhaustion. No formula input
   representation is needed by these programs or by FUNCTION_REFLECT. *)
let rf_execution_tests =
 [`lisp_eval 0 (LProgram [LQuote (LBoolean T)]) LNil`, `NONE:lisp_sexp option`;
  `lisp_eval 1 (LProgram [LVar 0]) (LNumber 7)`, `SOME (LNumber 7)`;
  `lisp_eval 1 (LProgram [LQuote (LPair (LSymbol 2) LNil)]) LNil`,
    `SOME (LPair (LSymbol 2) LNil)`;
  `lisp_eval 1 (LProgram [LCar (LVar 0)]) (LPair (LNumber 2) LNil)`,
    `SOME (LNumber 2)`;
  `lisp_eval 1 (LProgram [LCdr (LVar 0)]) (LPair (LNumber 2) (LNumber 3))`,
    `SOME (LNumber 3)`;
  `lisp_eval 1 (LProgram [LLet (LCar (LVar 0))
    (LCons (LVar 0) (LCdr (LVar 1)))]) (LPair (LNumber 2) (LNumber 3))`,
    `SOME (LPair (LNumber 2) (LNumber 3))`;
  `lisp_eval 1 (LProgram [LIf (LBoolean T) (LNumber 4) (LCar (LNumber 0))]) LNil`,
    `SOME (LNumber 4)`;
  `lisp_eval 1 (LProgram [LIf (LBoolean F) (LCar (LNumber 0)) (LNumber 4)]) LNil`,
    `SOME (LNumber 4)`;
  `lisp_eval 1 (LProgram [LIf (LNumber 0) (LBoolean T) (LBoolean F)]) LNil`,
    `NONE:lisp_sexp option`;
  `lisp_eval 1 (LProgram [LCar LNil]) LNil`, `NONE:lisp_sexp option`;
  `lisp_eval 1 (LProgram [LVar 1]) LNil`, `NONE:lisp_sexp option`;
  `lisp_eval 2 (LProgram [LCall 42 (LVar 0)]) LNil`, `NONE:lisp_sexp option`;
  `lisp_eval 1 (LProgram []) LNil`, `NONE:lisp_sexp option`;
  `lisp_eval 1 (LProgram [LPair (LSymbol 99) LNil]) LNil`, `NONE:lisp_sexp option`;
  `lisp_eval 1 (LPair (LBoolean T) (LNumber 0)) LNil`, `NONE:lisp_sexp option`;
  `lisp_eval 1 (LProgram [LIsCons (LVar 0)]) LNil`, `SOME (LBoolean F)`;
  `lisp_eval 1 (LProgram [LIsCons (LVar 0)]) (LPair LNil LNil)`, `SOME (LBoolean T)`;
  `lisp_eval 1 (LProgram [LEqual (LVar 0) (LQuote (LNumber 2))]) (LNumber 2)`,
    `SOME (LBoolean T)`;
  `lisp_eval 1 (LProgram [LEqual (LVar 0) (LQuote (LSymbol 2))]) (LNumber 2)`,
    `SOME (LBoolean F)`;
  `lisp_eval 3 (LProgram [LCall 0 (LVar 0)]) LNil`, `NONE:lisp_sexp option`;
  `lisp_eval 3 (LProgram [LIf (LIsCons (LVar 0)) (LCall 0 (LCdr (LVar 0)))
    (LBoolean T)]) (LPair (LNumber 1) (LPair (LNumber 2) LNil))`,
    `SOME (LBoolean T)`];;

List.iter (fun (tm,expected) ->
  let execution = rf_test_execution tm in
  if hyp execution <> [] || not(aconv (rhs(concl execution)) expected) then
    failwith ("Unexpected Lisp result: " ^ string_of_term tm)) rf_execution_tests;;

(* Differential checks against HOL's defined semantics, using ordinary kernel
   inference rather than FUNCTION_REFLECT to establish the expected equation. *)
let rf_checked_rules =
  map (fun i -> num_CONV (mk_small_numeral i)) [1;2;3;4;5;6;7;8;42;99] @
  LISP_SYNTAX @
  [lisp_eval; lisp_exec; lisp_run; lisp_functions; lisp_number;
   lisp_lookup; lisp_bind; lisp_car; lisp_cdr; lisp_iscons; lisp_branch;
   FST; SND; LENGTH; EL; HD; TL; PRE; SUC_INJ; NOT_SUC;
   LISP_VALUE_DISTINCT; LISP_VALUE_INJ];;

List.iter (fun (tm,_) ->
  let checked = (REWRITE_CONV rf_checked_rules THENC NUM_REDUCE_CONV) tm in
  let execution = rf_test_execution tm in
  if not(aconv (concl execution) (concl checked)) then
    failwith ("Executable and embedded semantics disagree: " ^ string_of_term tm))
  rf_execution_tests;;

(* Reflection accepts concrete syntax only, even under quote. *)
rf_expect_failure (fun () -> rf_test_execution
  `lisp_eval 1 (LProgram [LQuote x]) LNil`);;
rf_expect_failure (fun () -> rf_test_execution
  `lisp_eval 1 (LProgram [LVar 0]) x`);;
rf_expect_failure (fun () -> rf_test_execution
  `lisp_eval 1 p LNil`);;
rf_expect_failure (fun () -> rf_test_execution
  `lisp_eval n (LProgram [LVar 0]) LNil`);;
rf_expect_failure (fun () -> FUNCTION_REFLECT `T`);;

(* Quotation and proof reflection are independent of the Lisp evaluator. *)
let RF_QUOTE_TEST = `⌈T ==> T⌉`;;
if not(aconv RF_QUOTE_TEST `Implies Truth Truth`) then
  failwith "Ceiling quotation failed";;
let RF_ATOM_QUOTE_TEST = `⌈p ==> p⌉`;;
if not(aconv RF_ATOM_QUOTE_TEST `Implies (Atom 0) (Atom 0)`) then
  failwith "Ceiling quotation with atoms failed";;
if not(aconv (rf_quote `p /\ p`) `Conj (Atom 0) (Atom 0)`) ||
   not(aconv (rf_quote `p /\ q`) `Conj (Atom 0) (Atom 1)`) then
  failwith "Quotation did not preserve atom identity";;
rf_expect_failure (fun () -> rf_quote `x:num`);;
rf_expect_failure (fun () -> rf_quote `!x:bool. x ==> x`);;
rf_expect_failure (fun () -> PROOF_REFLECT TRUTH);;
let rf_assumed = PROOF_REFLECT (ASSUME `rf_provable (Atom 0)`);;
if hyp rf_assumed <> [`rf_provable (Atom 0)`] ||
   not(aconv (concl rf_assumed) `rf_atom_0:bool`) then
  failwith "Proof reflection lost assumptions or decoded an atom incorrectly";;

rf_expect_failure (fun () -> rf_register (ASSUME `rf_sound rf_solver`));;
let rf_test_discharge = rf_register
  (REWRITE_RULE[rf_solver; rf_bodies; rf_decider; rf_pick_code;
                rf_subst_code; rf_ground] RF_DECIDER_SOUND);;
rf_expect_failure (fun () -> rf_test_discharge 20 `Falsity`);;
rf_expect_failure (fun () -> rf_test_discharge 0 `Truth`);;
rf_expect_failure (fun () -> rf_test_discharge 20 `Atom 0`);;
rf_expect_failure (fun () -> rf_test_discharge 20 `Implies (Atom 0) (Atom 1)`);;

let RF_UNSAT_CNF = prove
 (`~((p \/ q) /\ (~p \/ q) /\ (p \/ ~q) /\ (~p \/ ~q))`, RF_SAT_TAC 30);;
let RF_RENAMED = prove
 (`(rf_atom_1 /\ rf_atom_0) ==> rf_atom_1`, RF_SAT_TAC 20);;
let RF_EXAMPLE = prove
 (`(T /\ F) ==> (F \/ T)`, RF_SAT_TAC 10);;
let RF_EXCLUDED_MIDDLE = prove (`p \/ ~p`, RF_SAT_TAC 12);;
let RF_MODUS_PONENS = prove (`((p ==> q) /\ p) ==> q`, RF_SAT_TAC 18);;
let RF_DISTRIBUTIVITY = prove
 (`(p /\ (q \/ r)) <=> ((p /\ q) \/ (p /\ r))`, RF_SAT_TAC 30);;
if List.exists (fun th -> hyp th <> [])
  [RF_EXAMPLE; RF_EXCLUDED_MIDDLE; RF_MODUS_PONENS;
   RF_DISTRIBUTIVITY; RF_UNSAT_CNF; RF_RENAMED; RF_DECIDER_SOUND] then
  failwith "Unexpected undischarged assumptions";;

print_endline "REFLECTION_TEST_OK";;
