(* agents/probes/V4_P06_rocq_backport.v — can Bonak.νSetF's dimension
   discipline be backported to Rocq?  (V4-REPORT.md §8.)

   A Rocq file among the Agda probes: it tests the two mechanisms the
   νSetF tower stands on, against the toolchain the Rocq development's
   patched CI job uses.  Compile with

       coqc -allow-rewrite-rules V4_P06_rocq_backport.v

   on the bonak-patched-rocq switch (Rocq 9.4+alpha).  What compiles
   below is the rewrite half; the guard half is kept as a comment
   because its whole point is that it does NOT compile.

   1. THE GUARD (fatal).  νSetF's termination is a size-change
   argument: frame descends on p, painting on k, layer on the dimension n,
   most sibling edges level, strictness emerging only around composed
   cycles.  Rocq's guard requires every sibling call to descend
   strictly on the CALLER's single {struct} argument, and rejects the
   block's call skeleton on its first edge:

     Fixpoint frame (n p k : nat) {struct p} : nat :=
       match p with
       | 0 => 0
       | S p' => frame n p' (S k) + layer n p' k
       end
     with layer (n p k : nat) {struct n} : nat :=
       match n with
       | 0 => 0
       | S n' => painting n' p k
       end
     with painting (n p k : nat) {struct k} : nat :=
       match k with
       | 0 => n
       | S k' => layer n p k' + painting n (S p) k'
       end.

     Error: Recursive definition of frame is ill-formed.
     Recursive call to layer has principal argument equal to
     "n" instead of "p'".

   No struct assignment fares better (frame -> layer and
   painting -> layer pass an EQUAL dimension), and there is no pragma
   escape.  The standard workarounds forfeit the design: well-founded
   recursion (Equations/Program) unfolds only on closed accessibility
   witnesses, killing the variable-index reductions the fillers-only
   conversion story needs (the r = 0 restriction, the coercion-free
   painting base); and restaging on the dimension is blocked by the
   suc-written UP-references in the coherence statements — re-indexing
   them downward means stating each level over stored data of the
   current stratum, which is the existing Rocq architecture (Deps
   records) re-derived.  The stored-strata Rocq original is the
   guard-imposed normal form of this construction; the fillers-only
   block is the shape only a size-change checker accepts. *)

(* 2. THE REWRITE RULES (portable).  Rocq rewrite rules attach only to
   fresh Symbols, so addition becomes a Symbol carrying its two
   computation clauses plus NatRew's two extra rules.  All three
   prefix-former equations of V4-REPORT §1 then hold by eq_refl at
   variable p and k.  Same trust posture as Agda's NatRew — no
   confluence checker, the one critical pair joins by hand — plus the
   experimental flag, and Nat.add's stdlib support no longer applies
   to [+]. *)

Symbol add : nat -> nat -> nat.
Notation "p [+] k" := (add p k) (at level 50).

Rewrite Rule add_rules :=
| add 0 ?k => ?k
| add (S ?p) ?k => S (add ?p ?k)
| add ?p 0 => ?p
| add ?p (S ?k) => S (add ?p ?k).

Check (fun p : nat => eq_refl : p [+] 0 = p).
Check (fun p k : nat => eq_refl : p [+] S k = S (p [+] k)).
Check (fun p k : nat => eq_refl : S p [+] k = S (p [+] k)).

(* 3. THE WITNESS (trivially portable, and already the house style):
   EqN would be an SProp-valued recursive equality — the mainline's
   LeSProp.v pattern, which Bonak/LeProp.agda mirrors in the other
   direction. *)
