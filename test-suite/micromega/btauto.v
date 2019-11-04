Require Import Bool ZArith.
Require Import Lia.

(* Pure boolean reasoning *)

Goal orb true true = true.
Proof.
  intros.
  lia.
Qed.

Goal andb true true = true.
Proof.
  intros.
  lia.
Qed.

Goal orb false true = true.
Proof.
  intros.
  lia.
Qed.

Goal orb false true = andb true true.
Proof.
  intros.
  lia.
Qed.

Goal forall (b:bool), orb b true = true.
Proof.
  intros.
  lia.
Qed.

Goal forall (f: bool -> bool), f true = true -> True.
Proof.
  intros.
  lia.
Qed.


(** Using comparison *)

Goal forall (x:Z), Z.eqb x x = true.
Proof.
  intros.
  lia.
Qed.

Section S.
  Variable T C : bool.
  Variable H : T = true /\ T = C.

Lemma TH :  True.
Proof using .
  intros.
  lia.
Qed.

End S.

Goal forall (x:nat), Nat.eqb x x = true.
Proof.
  intros.
  Fail lia.
Abort.

Require Import ZifyBool.

Goal forall (x:nat), Nat.eqb x x = true.
Proof.
  intro x.
  lia.
Qed.
