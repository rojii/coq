(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria)      2016                             *)
(*                                                                      *)
(************************************************************************)

Require Import RMicromega.
Require Import QMicromega.
Require Import Rdefinitions.
Require Import RingMicromega.
Require Import VarMap.
Require Coq.micromega.Tauto.
Declare ML Module "micromega_plugin".

Ltac rchecker :=
  intros __wit __varmap __ff ;
  exact (RTautoChecker_sound __ff __wit
                             (@eq_refl bool true <: @eq bool (RTautoChecker __ff __wit) true)
                             (@find R 0%R __varmap)).


(** Here, lra stands for linear real arithmetic *)
Ltac lra := unfold Rdiv in * ;   lra_R  rchecker.

(** Here, nra stands for non-linear real arithmetic *)
Ltac nra := unfold Rdiv in * ; xnra  rchecker.

Ltac xpsatz dom d :=
  let tac := lazymatch dom with
  | R =>
    (sos_R rchecker) || (psatz_R d rchecker)
  | _ => fail "Unsupported domain"
 end in tac.

Tactic Notation "psatz" constr(dom) int_or_var(n) := xpsatz dom n.
Tactic Notation "psatz" constr(dom) := xpsatz dom ltac:(-1).


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
