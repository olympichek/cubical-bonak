(* Rocq feasibility probe for the fillers-only dimension discipline.

   The probe tests the termination and rewrite mechanisms with the
   patched Rocq toolchain required by the experimental rewrite rules.
   Compile with

       coqc -allow-rewrite-rules V4_P06_rocq_backport.v

   on the bonak-patched-rocq switch (Rocq 9.4+alpha). What compiles
   below is the rewrite half; the guard half is a comment documenting the
   rejected mutual definition.

   1. THE GUARD. The mutual block has a size-change termination
   argument: frame descends on p, painting on k, layer on the dimension n,
   most sibling edges level, strictness emerging only around composed
   cycles. Rocq's guard requires every sibling call to descend
   strictly on the caller's single {struct} argument, and rejects the
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
   painting -> layer pass an equal dimension), and there is no pragma
   escape. The standard alternatives change its reduction behavior:
   well-founded
   recursion (Equations/Program) unfolds only on closed accessibility
   witnesses, which prevents the variable-index reductions needed by the
   r = 0 restriction and the coercion-free painting base; restaging on
   the dimension is blocked by the suc-written higher-dimensional
   references in the coherence statements; re-indexing
   them downward means stating each level over stored data of the
   current stratum. Thus the guard accepts a stored-strata encoding but
   not this fillers-only mutual block. *)

(* 2. THE REWRITE RULES. Rocq rewrite rules attach only to
   fresh Symbols, so addition becomes a Symbol carrying its two
   computation clauses plus the two extra rules below. All three
   required prefix-former equations then hold by eq_refl at
   variable p and k. There is no confluence check; all
   overlaps join by normalization. This also requires the experimental flag, and
   Nat.add's standard-library support does not apply to [+]. *)

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

(* 3. THE WITNESS. EqN can be an SProp-valued recursive equality, so
   its proofs are definitionally irrelevant. *)
