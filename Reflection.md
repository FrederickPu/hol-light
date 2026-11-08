# Reflection: registration and the Lisp example

The kernel provides two independent reflection mechanisms. Users register
their own logical definitions and executable handlers. The example registers
a small Lisp evaluator and a propositional provability predicate, then combines
them into a certificate-free solver.

## Registration

First introduce the relevant datatypes and constants using ordinary HOL
definitions, recursive definitions, or characterization axioms. Then register:

```ocaml
reflect_function eval_definition executable_evaluator;;
reflect_pred provable_definition unquoter;;
```

Both functions take a theorem and an OCaml callback of type `term -> term`.
The theorem must have no hypotheses and contain equations or Boolean
equivalences identifying one constant at a consistent application arity.
Registration extracts that constant from the left-hand side and records its
full HOL type. Duplicate registrations are rejected; polymorphic instances are
registered separately.

### Function reflection

```text
FUNCTION_REFLECT `f arguments`
    1. Look up f's registered handler.
    2. Check the application is closed and has the registered arity.
    3. Pass the whole application to the handler.
    4. Check its result is closed and has the same HOL type.
    5. Return |- f arguments = result.
```

The handler returns an encoded HOL result, not a theorem. Exceptions abort
reflection. For Lisp, results include `SOME value` and `NONE`.

### Proof reflection

Predicate registration currently supports unary predicates. Given
`H |- P q`, `PROOF_REFLECT` looks up `P`, passes **only `q`** to its unquoter,
checks that the result has type `bool`, and returns `H |- unquote(q)`.
The input assumptions are preserved.

### Trust and theory

Both operations construct theorem values inside `Hol` in `fusion.ml`;
registered callbacks return terms and cannot access its private theorem
constructor. There is no hardcoded Lisp or formula interpretation there.
Registered evidence is inspectable through `function_reflections()` and
`predicate_reflections()`, both returning `thm list`.

**Trust:** registering a handler accepts its correspondence with the supplied
theory as trusted, analogously to accepting an axiom. A definition theorem
identifies the operation; it does not prove arbitrary OCaml code implements it.
Registrations extend the trusted base and are recorded separately from
`axioms()`.

Proving a particular program sound inside HOL is separate from justifying its
registered handlers. The demo proves the former and tests the latter; it does
not formally verify the modified kernel or Candle. An incorrect trusted handler
can introduce false theorems despite a true definition being supplied.

## Composing the reflection mechanisms

A program-specific soundness theorem connects a successful execution to the
registered provability predicate. A discharger uses it as follows:

```text
Quote the goal as q and encode q as program input.
FUNCTION_REFLECT proves the execution returned true.
Apply the program's soundness theorem to obtain |- Provable q.
PROOF_REFLECT produces the unquoted proposition.
Restore variable names and check the theorem against the original goal.
```

The demo's `rf_register` and `RF_DISCHARGE_TAC`, in
`Examples/reflection_sat.ml`, implement this composition outside the kernel.
Unlike `reflect_function` and `reflect_pred`, they install
no trusted interpretation: they use a proved soundness theorem and existing
registrations. Ceiling notation is likewise an untrusted quotation convenience,
not a third primitive.

## Proof of concept reflection

**Lisp:** one untyped S-expression datatype represents both code and data.
The direct interpreter supports quotation, local variables, `let`, Boolean
`if`, pair operations, equality, and recursive single-argument functions,
without closures or mutation. It executes concrete programs and inputs;
fuel bounds call depth, and `NONE` denotes exhaustion or an invalid operation.
Its theory, evaluator, and `reflect_function lisp_eval lisp_evaluator`
registration are together in `Reflection/function_reflection.ml`.

**Logic:** the embedded fragment is classical propositional logic with truth,
falsity, indexed Boolean variables, conjunction, disjunction, and implication;
quotation expands negation and equivalence into these connectives. It excludes
quantifiers and general HOL terms. `RF_PROVABLE_RULES` axiomatizes `rf_provable q`
as truth under every Boolean valuation. The registration
`reflect_pred RF_PROVABLE_RULES rf_unquote` connects it to actual HOL
propositions. The theory, axiom, and handler are together in
`Reflection/proof_reflection.ml`; there is no separate proof-object datatype.

## Demo: reflected SAT solver

The demo solver uses `rf_encode` to represent formulas as ordinary Lisp data and
performs exhaustive Boolean case splitting. The evaluator knows nothing about
the data's logical meaning. Acceptance means the goal is valid, equivalently
its negation is unsatisfiable; no per-goal SAT certificate is returned.
`Examples/reflection_sat.ml` proves:

```text
|- rf_sound rf_solver

rf_sound g <=>
  !n q. lisp_eval n g (rf_encode q) = SOME (LBoolean T)
        ==> rf_provable q
```

The proof allows exhaustion and establishes correctness of successful answers,
not termination within a particular budget. For this propositional fragment,
proof reflection is justified by instantiating the universal valuation in
`RF_PROVABLE_RULES` and rewriting. This demo reflects only the propositional
fragment described above; it does not embed the full HOL proof system.

### Running the demo

```ocaml
needs "Examples/reflection_sat.ml";;
`⌈p ==> p⌉`;;  (* Implies (Atom 0) (Atom 0) *)
prove (`p \/ ~p`, RF_SAT_TAC 12);;
prove (`((p ==> q) /\ p) ==> q`, RF_SAT_TAC 18);;
```

Run `#use "Reflection/tests.ml";;` in HOL Light, or
`LINE_EDITOR=env ./hol.sh < Reflection/run_tests.ml` from the repository root.
Successful tests print `REFLECTION_TEST_OK`.

## Related work

[CakeML/hol-reflection][hr] is related work, not an imported component. Its
[quotation code][hr-basic] separates syntax construction from theorem
production; its [interface][hr-interface] carries context and interpretation
evidence such as `sound_update_thm`, `extends_init_thm`, and `models_thm`.
Its [design notes][hr-notes] discuss embedded derivability and reflection with
explicit logical-strength assumptions, not an unconditional API available here.
Source links are pinned to commit `5791eff4565632f3aa5201a749ff319ccda3aa53`.

[hr]: https://github.com/CakeML/hol-reflection
[hr-basic]: https://github.com/CakeML/hol-reflection/blob/5791eff4565632f3aa5201a749ff319ccda3aa53/basicReflectionLib.sml
[hr-interface]: https://github.com/CakeML/hol-reflection/blob/5791eff4565632f3aa5201a749ff319ccda3aa53/reflectionLib.sig
[hr-notes]: https://github.com/CakeML/hol-reflection/blob/5791eff4565632f3aa5201a749ff319ccda3aa53/notes.txt
