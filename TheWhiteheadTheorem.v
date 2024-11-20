(* Import standard libraries *)
Require Import Coq.Init.Nat.

(* Define a function to add two natural numbers *)
Definition add_two_numbers (n m : nat) : nat :=
  n + m.

(* Prove a simple property about addition *)
Theorem add_commutative : forall n m : nat, 
  add_two_numbers n m = add_two_numbers m n.
Proof.
  intros n m.
  unfold add_two_numbers.
  apply Nat.add_comm.
Qed.
