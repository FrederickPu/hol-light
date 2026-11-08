(* Certificate-free propositional decision by Boolean case splitting.
   The program returns true precisely for tautologies when fuel suffices.
   Equivalently, it checks unsatisfiability of a goal's negation. *)
needs "Reflection/reflection.ml";;
needs "Reflection/quote.ml";;

(* Solver-specific formula operations and their encoding as ordinary Lisp
   data. Neither reflection mechanism depends on these definitions. *)
let rf_hasatom = new_recursive_definition rf_formula_RECURSION
 `(rf_hasatom Truth = F) /\ (rf_hasatom Falsity = F) /\
  (rf_hasatom (Atom n) = T) /\
  (rf_hasatom (Conj a b) = (rf_hasatom a \/ rf_hasatom b)) /\
  (rf_hasatom (Disj a b) = (rf_hasatom a \/ rf_hasatom b)) /\
  (rf_hasatom (Implies a b) = (rf_hasatom a \/ rf_hasatom b))`;;

let rf_pick = new_recursive_definition rf_formula_RECURSION
 `(rf_pick Truth = 0) /\ (rf_pick Falsity = 0) /\
  (rf_pick (Atom n) = n) /\
  (rf_pick (Conj a b) = if rf_hasatom a then rf_pick a else rf_pick b) /\
  (rf_pick (Disj a b) = if rf_hasatom a then rf_pick a else rf_pick b) /\
  (rf_pick (Implies a b) = if rf_hasatom a then rf_pick a else rf_pick b)`;;

let rf_subst = new_recursive_definition rf_formula_RECURSION
 `(rf_subst Truth n x = Truth) /\ (rf_subst Falsity n x = Falsity) /\
  (rf_subst (Atom i) n x = if i = n then (if x then Truth else Falsity)
                          else Atom i) /\
  (rf_subst (Conj a b) n x = Conj (rf_subst a n x) (rf_subst b n x)) /\
  (rf_subst (Disj a b) n x = Disj (rf_subst a n x) (rf_subst b n x)) /\
  (rf_subst (Implies a b) n x = Implies (rf_subst a n x) (rf_subst b n x))`;;

(* Tags: truth=0, falsity=1, conjunction=2, disjunction=3,
   implication=4, atom=5. Binary nodes use (tag . (left . right)). *)
let rf_encode = new_recursive_definition rf_formula_RECURSION
 `(rf_encode Truth = LSymbol 0) /\
  (rf_encode Falsity = LSymbol 1) /\
  (rf_encode (Atom n) = LPair (LSymbol 5) (LNumber n)) /\
  (rf_encode (Conj a b) = LPair (LSymbol 2) (LPair (rf_encode a) (rf_encode b))) /\
  (rf_encode (Disj a b) = LPair (LSymbol 3) (LPair (rf_encode a) (rf_encode b))) /\
  (rf_encode (Implies a b) = LPair (LSymbol 4) (LPair (rf_encode a) (rf_encode b)))`;;

let rf_pack = new_definition
 `rf_pack q n x = LPair (rf_encode q) (LPair (LNumber n) (LBoolean x))`;;

let rf_pick_value = new_definition
 `rf_pick_value q = if rf_hasatom q then LNumber (rf_pick q) else LNil`;;

(* Untrusted proof automation composing the two reflection mechanisms. *)
let rf_sound = new_definition
 `rf_sound program <=>
    !n q. lisp_eval n program (rf_encode q) = SOME (LBoolean T)
          ==> rf_provable q`;;

let RF_IFF_EXPAND = TAUT `(p <=> q) <=> ((p ==> q) /\ (q ==> p))`;;

let rf_register sound_thm =
  let c = concl sound_thm in
  if not (is_comb c && aconv (rator c) `rf_sound`) || hyp sound_thm <> [] then
    failwith "rf_register: expected a closed theorem of rf_sound program";
  let program = rand c in
  fun fuel quotation ->
    let expression = list_mk_comb(`lisp_eval`,
      [mk_small_numeral fuel; program; mk_comb(`rf_encode`,quotation)]) in
    let encoding = REWRITE_CONV (rf_encode :: LISP_SYNTAX) expression in
    let execution = TRANS encoding (FUNCTION_REFLECT (rhs(concl encoding))) in
    if not (aconv (rhs(concl execution)) `SOME (LBoolean T)`) then
      failwith "reflection: false result, exhausted fuel, or invalid input";
    MATCH_MP
      (SPECL [mk_small_numeral fuel; quotation]
        (REWRITE_RULE[rf_sound] sound_thm)) execution;;

let RF_DISCHARGE_TAC sound_thm fuel : tactic =
  let discharge = rf_register sound_thm in
  fun (asl,w as goal) ->
    let normalization =
      (PURE_REWRITE_CONV[NOT_DEF; RF_IFF_EXPAND] THENC
       DEPTH_CONV BETA_CONV) w in
    let quotation,bindings = rf_quote_with_env (rhs(concl normalization)) in
    let reflected = INST bindings (PROOF_REFLECT (discharge fuel quotation)) in
    ACCEPT_TAC (EQ_MP (SYM normalization) reflected) goal;;

let RF_SUBST_VALUE = prove
 (`!q n x v. rf_value (rf_subst q n x) v =
             rf_value q (\i. if i = n then x else v i)`,
  MATCH_MP_TAC rf_formula_INDUCT THEN
  REWRITE_TAC[rf_subst; rf_value] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[rf_value] THEN ASM_MESON_TAC[]);;

let RF_SPLIT = prove
 (`!q n. rf_provable q <=>
         rf_provable (rf_subst q n T) /\ rf_provable (rf_subst q n F)`,
  REWRITE_TAC[RF_PROVABLE_RULES; RF_SUBST_VALUE] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[];
    STRIP_TAC THEN X_GEN_TAC `v:num->bool` THEN
    SUBGOAL_THEN
     `rf_value q v = rf_value q (\i. if i = n then v n else v i)`
     SUBST1_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[];
      ASM_CASES_TAC `(v:num->bool) n` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]]]);;

let RF_CLOSED_VALUE = prove
 (`!q. ~rf_hasatom q ==> !v. rf_value q v = rf_value q (\n. F)`,
  MATCH_MP_TAC rf_formula_INDUCT THEN
  REWRITE_TAC[rf_hasatom; rf_value; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let RF_CLOSED_PROVABLE = prove
 (`!q. ~rf_hasatom q ==> (rf_provable q <=> rf_value q (\n. F))`,
  GEN_TAC THEN DISCH_THEN (fun th ->
    REWRITE_TAC[RF_PROVABLE_RULES] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
      [MATCH_MP (SPEC `q:rf_formula` RF_CLOSED_VALUE) th]) THEN
  REWRITE_TAC[]);;

let RF_CLOSED_RULES = prove
 (`rf_provable Truth /\ ~rf_provable Falsity /\
   (!a b. ~rf_hasatom a /\ ~rf_hasatom b ==>
     ((rf_provable (Conj a b) <=> rf_provable a /\ rf_provable b) /\
      (rf_provable (Disj a b) <=> rf_provable a \/ rf_provable b) /\
      (rf_provable (Implies a b) <=> (rf_provable a ==> rf_provable b))))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SIMP_TAC[RF_CLOSED_PROVABLE; rf_hasatom; rf_value] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RF_CLOSED_PROVABLE; rf_hasatom; rf_value]);;

let rf_ground = new_definition
 `rf_ground =
    LIf (LEqual (LVar 0) (LQuote (LSymbol 0))) (LQuote (LBoolean T))
     (LIf (LEqual (LVar 0) (LQuote (LSymbol 1))) (LQuote (LBoolean F))
      (LIf (LEqual (LCar (LVar 0)) (LQuote (LSymbol 5))) (LQuote (LBoolean F))
       (LIf (LEqual (LCar (LVar 0)) (LQuote (LSymbol 2)))
         (LIf (LCall 3 (LCar (LCdr (LVar 0))))
              (LCall 3 (LCdr (LCdr (LVar 0)))) (LQuote (LBoolean F)))
        (LIf (LEqual (LCar (LVar 0)) (LQuote (LSymbol 3)))
          (LIf (LCall 3 (LCar (LCdr (LVar 0))))
               (LQuote (LBoolean T)) (LCall 3 (LCdr (LCdr (LVar 0)))))
          (LIf (LCall 3 (LCar (LCdr (LVar 0))))
               (LCall 3 (LCdr (LCdr (LVar 0)))) (LQuote (LBoolean T)))))))`;;

let rf_pick_code = new_definition
 `rf_pick_code =
    LIf (LEqual (LVar 0) (LQuote (LSymbol 0))) (LQuote LNil)
     (LIf (LEqual (LVar 0) (LQuote (LSymbol 1))) (LQuote LNil)
      (LIf (LEqual (LCar (LVar 0)) (LQuote (LSymbol 5))) (LCdr (LVar 0))
       (LLet (LCall 1 (LCar (LCdr (LVar 0))))
         (LIf (LEqual (LVar 0) (LQuote LNil))
           (LCall 1 (LCdr (LCdr (LVar 1)))) (LVar 0)))))`;;

let rf_subst_code = new_definition
 `rf_subst_code =
    LIf (LEqual (LCar (LVar 0)) (LQuote (LSymbol 0))) (LQuote (LSymbol 0))
     (LIf (LEqual (LCar (LVar 0)) (LQuote (LSymbol 1))) (LQuote (LSymbol 1))
      (LIf (LEqual (LCar (LCar (LVar 0))) (LQuote (LSymbol 5)))
        (LIf (LEqual (LCdr (LCar (LVar 0))) (LCar (LCdr (LVar 0))))
          (LIf (LCdr (LCdr (LVar 0))) (LQuote (LSymbol 0)) (LQuote (LSymbol 1)))
          (LCar (LVar 0)))
        (LCons (LCar (LCar (LVar 0)))
          (LCons
            (LCall 2 (LCons (LCar (LCdr (LCar (LVar 0)))) (LCdr (LVar 0))))
            (LCall 2 (LCons (LCdr (LCdr (LCar (LVar 0)))) (LCdr (LVar 0))))))))`;;

let rf_decider = new_definition
 `rf_decider =
    LLet (LCall 1 (LVar 0))
     (LIf (LEqual (LVar 0) (LQuote LNil)) (LCall 3 (LVar 1))
       (LIf
         (LCall 0 (LCall 2 (LCons (LVar 1) (LCons (LVar 0) (LQuote (LBoolean T))))))
         (LCall 0 (LCall 2 (LCons (LVar 1) (LCons (LVar 0) (LQuote (LBoolean F))))))
         (LQuote (LBoolean F))))`;;

let rf_bodies = new_definition
 `rf_bodies = [rf_decider; rf_pick_code; rf_subst_code; rf_ground]`;;

let rf_solver = new_definition `rf_solver = LProgram rf_bodies`;;

let rf_invariant = new_definition
 `rf_invariant call <=>
   (!q. lisp_returns (call 0 (rf_encode q)) (LBoolean (rf_provable q))) /\
   (!q. lisp_returns (call 1 (rf_encode q)) (rf_pick_value q)) /\
   (!q n x. lisp_returns (call 2 (rf_pack q n x)) (rf_encode (rf_subst q n x))) /\
   (!q. lisp_returns (call 3 (rf_encode q)) (LBoolean (rf_value q (\n. F))))`;;

(* Proof automation only: split the possible results of recursive calls using
   the induction hypothesis. All resulting equations are checked by HOL. *)
let RF_BODY_REWRITES =
 [LISP_RUN_CLAUSES;
  lisp_lookup; lisp_bind; lisp_car; lisp_cdr; lisp_iscons;
  lisp_branch; lisp_returns; LISP_VALUE_DISTINCT; LISP_VALUE_INJ;
  option_DISTINCT; option_INJ; rf_encode; rf_pack; rf_subst;
  rf_pick_value; rf_hasatom; rf_pick; rf_value; ARITH_EQ];;

let RF_ORACLE_CASE_TAC (asl,w as goal) =
  let rules = filter (fun th ->
    let op,args = strip_comb(concl(SPEC_ALL th)) in
    is_const op && fst(dest_const op) = "lisp_returns" && length args = 2)
    (map snd asl) in
  let match_call tm =
    let normalized = PURE_REWRITE_CONV
      (map GSYM (CONJUNCTS rf_encode) @ [GSYM rf_pack]) tm in
    let th = tryfind (fun th -> PART_MATCH lhand th (rhs(concl normalized))) rules in
    CONV_RULE (LAND_CONV (REWR_CONV (SYM normalized))) th in
  let tm = find_term (can match_call) w in
  DISJ_CASES_TAC (REWRITE_RULE[lisp_returns] (match_call tm)) goal;;

let RF_CONTRADICTION_TAC (asl,w as goal) =
  let facts = filter (fun th -> not(is_forall(concl th))) (map snd asl) in
  let contradiction = tryfind (fun th ->
    let others = filter (fun other -> not (equals_thm th other)) facts in
    let reduced = REWRITE_RULE (others @ RF_BODY_REWRITES) th in
    if aconv (concl reduced) `F` then reduced else failwith "consistent") facts in
  CONTR_TAC contradiction goal;;

let rec rf_body_tac depth goal =
 if depth > 20 then failwith ("Lisp proof search depth: " ^ string_of_term(snd goal)) else
 (ASM_REWRITE_TAC RF_BODY_REWRITES THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC RF_BODY_REWRITES THEN
  FIRST [RF_ORACLE_CASE_TAC THEN rf_body_tac (depth + 1);
         COND_CASES_TAC THEN rf_body_tac (depth + 1);
         RF_CONTRADICTION_TAC;
         CONV_TAC TAUT;
         POP_ASSUM_LIST (fun ths -> MESON_TAC
           (filter (fun th -> not(is_forall(concl th))) ths))]) goal;;

let RF_BODY_TAC = rf_body_tac 0;;

let RF_PICK_STEP = prove
 (`!call. rf_invariant call ==>
    !q. lisp_returns (lisp_run rf_pick_code call [rf_encode q]) (rf_pick_value q)`,
  GEN_TAC THEN REWRITE_TAC[rf_invariant] THEN STRIP_TAC THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `q:rf_formula` (cases "rf_formula")) THEN
  REWRITE_TAC[rf_pick_code] THEN RF_BODY_TAC);;

let RF_SUBST_STEP = prove
 (`!call. rf_invariant call ==>
    !q n x. lisp_returns (lisp_run rf_subst_code call [rf_pack q n x])
                         (rf_encode (rf_subst q n x))`,
  GEN_TAC THEN REWRITE_TAC[rf_invariant] THEN STRIP_TAC THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `q:rf_formula` (cases "rf_formula")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[rf_subst_code] THEN RF_BODY_TAC);;

let RF_GROUND_STEP = prove
 (`!call. rf_invariant call ==>
    !q. lisp_returns (lisp_run rf_ground call [rf_encode q])
                     (LBoolean (rf_value q (\n. F)))`,
  GEN_TAC THEN REWRITE_TAC[rf_invariant] THEN STRIP_TAC THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `q:rf_formula` (cases "rf_formula")) THEN
  REWRITE_TAC[rf_ground] THEN RF_BODY_TAC);;

let RF_DECIDER_STEP = prove
 (`!call. rf_invariant call ==>
    !q. lisp_returns (lisp_run rf_decider call [rf_encode q])
                     (LBoolean (rf_provable q))`,
  GEN_TAC THEN REWRITE_TAC[rf_invariant] THEN STRIP_TAC THEN GEN_TAC THEN
  MP_TAC (SPECL [`q:rf_formula`; `rf_pick q`] RF_SPLIT) THEN DISCH_TAC THEN
  ASM_CASES_TAC `rf_hasatom q` THENL
   [ALL_TAC;
    MP_TAC (MATCH_MP (SPEC `q:rf_formula` RF_CLOSED_PROVABLE)
                    (ASSUME `~rf_hasatom q`)) THEN DISCH_TAC] THEN
  REWRITE_TAC[rf_decider] THEN RF_BODY_TAC);;

let RF_SOLVER_EXEC = prove
 (`(!n q. lisp_exec (SUC n) rf_solver 0 q =
           lisp_run rf_decider (lisp_exec n rf_solver) [q]) /\
   (!n q. lisp_exec (SUC n) rf_solver 1 q =
           lisp_run rf_pick_code (lisp_exec n rf_solver) [q]) /\
   (!n q. lisp_exec (SUC n) rf_solver 2 q =
           lisp_run rf_subst_code (lisp_exec n rf_solver) [q]) /\
   (!n q. lisp_exec (SUC n) rf_solver 3 q =
           lisp_run rf_ground (lisp_exec n rf_solver) [q])`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[lisp_exec; rf_solver; LProgram; rf_bodies; lisp_list;
              lisp_functions; lisp_lookup; lisp_bind] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lisp_lookup; lisp_bind; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lisp_lookup; lisp_bind; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lisp_lookup; lisp_bind; FST; SND]);;

let RF_SOLVER_INVARIANT = prove
 (`!n. rf_invariant (lisp_exec n rf_solver)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[rf_invariant; lisp_exec; lisp_returns];
    REWRITE_TAC[rf_invariant; RF_SOLVER_EXEC] THEN
    REPEAT CONJ_TAC THEN
    FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[])
      [RF_DECIDER_STEP; RF_PICK_STEP; RF_SUBST_STEP; RF_GROUND_STEP])]);;

let RF_DECIDER_CORRECT = prove
 (`!n q. lisp_returns (lisp_eval n rf_solver (rf_encode q))
                      (LBoolean (rf_provable q))`,
  REWRITE_TAC[lisp_eval] THEN GEN_TAC THEN
  MATCH_ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE[rf_invariant]
    (SPEC `n:num` RF_SOLVER_INVARIANT))));;

let RF_DECIDER_SOUND = prove
 (`rf_sound rf_solver`,
  REWRITE_TAC[rf_sound] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `q:rf_formula`] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`n:num`; `q:rf_formula`] RF_DECIDER_CORRECT) THEN
  ASM_REWRITE_TAC[lisp_returns; option_DISTINCT; option_INJ; LISP_VALUE_INJ] THEN
  CONV_TAC TAUT);;

let RF_SAT_TAC = RF_DISCHARGE_TAC
  (REWRITE_RULE[rf_solver; rf_bodies; rf_decider; rf_pick_code;
                rf_subst_code; rf_ground] RF_DECIDER_SOUND);;
