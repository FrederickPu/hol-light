(* Propositional proof reflection: theory, characterization axiom, unquoter,
   and trusted registration. No Lisp or solver-specific definitions here. *)

(* ------------------------------------------------------------------------- *)
(* Deep propositional syntax and its axiomatized provability predicate.       *)
(* ------------------------------------------------------------------------- *)

let rf_formula_INDUCT,rf_formula_RECURSION = define_type
 "rf_formula = Truth | Falsity | Atom num
             | Conj rf_formula rf_formula
             | Disj rf_formula rf_formula
             | Implies rf_formula rf_formula";;

let rf_value = new_recursive_definition rf_formula_RECURSION
 `(rf_value Truth v = T) /\ (rf_value Falsity v = F) /\
  (rf_value (Atom n) v = v n) /\
  (rf_value (Conj a b) v = (rf_value a v /\ rf_value b v)) /\
  (rf_value (Disj a b) v = (rf_value a v \/ rf_value b v)) /\
  (rf_value (Implies a b) v = (rf_value a v ==> rf_value b v))`;;

new_constant("rf_provable",`:rf_formula->bool`);;

(* Validity quantifies over ALL valuations, not just one. *)
let RF_PROVABLE_RULES = new_axiom
 `!q. rf_provable q <=> !v:num->bool. rf_value q v`;;

(* ------------------------------------------------------------------------- *)
(* Executable unquotation and the trusted predicate registration.             *)
(* ------------------------------------------------------------------------- *)

let rec rf_unquote quotation =
  let constructor,args = strip_comb quotation in
  match args with
  | [] when aconv constructor `Truth` -> `T`
  | [] when aconv constructor `Falsity` -> `F`
  | [n] when aconv constructor `Atom` ->
      mk_var("rf_atom_" ^ string_of_num(dest_numeral n),bool_ty)
  | [a;b] ->
      let connective =
        if aconv constructor `Conj` then `(/\)`
        else if aconv constructor `Disj` then `(\/)`
        else if aconv constructor `Implies` then `(==>)`
        else failwith "rf_unquote: invalid formula constructor" in
      list_mk_comb(connective,[rf_unquote a; rf_unquote b])
  | _ -> failwith "rf_unquote: expected concrete formula syntax";;

(* The characterization theorem identifies the predicate; rf_unquote is the
   handler PROOF_REFLECT will look up for conclusions using that predicate. *)
reflect_pred RF_PROVABLE_RULES rf_unquote;;
