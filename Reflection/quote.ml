(* Untrusted quotation convenience. No theorem construction here.
   rf_quote_with_env returns syntax plus a simultaneous HOL substitution
   restoring the user's variables after PROOF_REFLECT's canonical naming. *)
needs "Reflection/proof_reflection.ml";;

let rf_quote_with_env tm =
  let atoms = ref [] in
  let rec quote tm =
    if type_of tm <> bool_ty then failwith "rf_quote: expected a proposition"
    else if aconv tm `T` then `Truth`
    else if aconv tm `F` then `Falsity`
    else if is_var tm then
      let rec index n = function
        | [] -> atoms := !atoms @ [tm]; n
        | a::rest -> if aconv a tm then n else index (n + 1) rest in
      mk_comb(`Atom`,mk_small_numeral (index 0 !atoms))
    else
      let op,args = strip_comb tm in
      match args with
      | [a] when aconv op `(~)` -> list_mk_comb(`Implies`,[quote a; `Falsity`])
      | [a;b] when aconv op `(=):bool->bool->bool` ->
          let a = quote a in let b = quote b in
          list_mk_comb(`Conj`,[list_mk_comb(`Implies`,[a;b]);
                              list_mk_comb(`Implies`,[b;a])])
      | [a;b] ->
          let constructor =
            if aconv op `(/\)` then `Conj`
            else if aconv op `(\/)` then `Disj`
            else if aconv op `(==>)` then `Implies`
            else failwith "rf_quote: unsupported propositional connective" in
          (* Sequence quotation so atom numbering follows left-to-right order. *)
          let a = quote a in let b = quote b in
          list_mk_comb(constructor,[a;b])
      | _ -> failwith "rf_quote: expected a propositional formula" in
  let q = quote tm in
  q,List.mapi (fun i a -> a,mk_var("rf_atom_" ^ string_of_int i,bool_ty)) !atoms;;

let rf_quote tm = fst(rf_quote_with_env tm);;

(* HOL's byte-oriented lexer does not recognize Unicode ceilings. Handle an
   outer ceiling pair before lexing; ordinary HOL parsing is unchanged.
   Both `⌈T ==> T⌉` and rf_quote_string "⌈T ==> T⌉" are convenient inputs. *)
let rf_quote_string =
  let ordinary_parse_term = parse_term in
  fun s ->
    let s = String.trim s in
    let n = String.length s in
    if n < 6 || String.sub s 0 3 <> "⌈" ||
       String.sub s (n - 3) 3 <> "⌉" then
      failwith "rf_quote_string: expected outer ceiling delimiters";
    rf_quote (ordinary_parse_term (String.sub s 3 (n - 6)));;

let parse_term =
  let ordinary_parse_term = parse_term in
  fun s ->
    let trimmed = String.trim s in
    if String.length trimmed >= 3 && String.sub trimmed 0 3 = "⌈" then
      rf_quote_string trimmed
    else ordinary_parse_term s;;
