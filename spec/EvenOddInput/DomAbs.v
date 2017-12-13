(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Abstract Domain.  *)

Set Implicit Arguments.

Require Import Morphisms.
Require Import vgtac VocabA Syn DLat DUnit DStr DSum DMap DProd DPow
        DItv UserInputType Zparity.
Require DMem.
Require Import DomBasic DomArrayBlk.

(** ** Value domain *)

Module Val <: LAT := Prod4 Zparity PowLoc ArrayBlk PowProc.

Definition zparity_of_val : Val.t -> Zparity.t := Val.fst.

Lemma zparity_of_val_mor : Proper (Val.eq ==> Zparity.eq) zparity_of_val.
Proof. unfold zparity_of_val. intros v1 v2 Hv. apply Val.fst_mor. apply Hv. Qed.

Definition pow_loc_of_val : Val.t -> PowLoc.t := Val.snd.

Lemma pow_loc_of_val_mor : Proper (Val.eq ==> PowLoc.eq) pow_loc_of_val.
Proof.  unfold pow_loc_of_val. intros v1 v2 Hv. apply Val.snd_mor. apply Hv. Qed.
        
Definition array_of_val : Val.t -> ArrayBlk.t := Val.thrd.

Lemma array_of_val_mor : Proper (Val.eq ==> ArrayBlk.eq) array_of_val.
Proof. unfold array_of_val. intros v1 v2 Hv. apply Val.thrd_mor. apply Hv. Qed.

Definition pow_proc_of_val : Val.t -> PowProc.t := Val.frth.

Lemma pow_proc_of_val_mor : Proper (Val.eq ==> PowProc.eq) pow_proc_of_val.
Proof. unfold pow_proc_of_val. intros v1 v2 Hv. apply Val.frth_mor. apply Hv. Qed.

Definition powProc_of_val := pow_proc_of_val.

Definition val_of_zparity (x : Zparity.t) : Val.t :=
  (x, PowLoc.bot, ArrayBlk.bot, PowProc.bot).

Lemma val_of_zparity_mor : Proper (Zparity.eq ==> Val.eq) val_of_zparity.
Proof. intros i1 i2 Hi.
split; [split; [split|] |]; s
; by auto using Zparity.eq_refl, PowLoc.eq_refl, ArrayBlk.eq_refl, PowProc.eq_refl.
Qed.
  
Definition val_of_pow_loc (x : PowLoc.t) : Val.t :=
  (Zparity.bot, x, ArrayBlk.bot, PowProc.bot).

Lemma val_of_pow_loc_mor : Proper (PowLoc.eq ==> Val.eq) val_of_pow_loc.
intros i1 i2 Hi.
split; [split; [split|] |]; s; by auto using Zparity.eq_refl, PowLoc.eq_refl, ArrayBlk.eq_refl, PowProc.eq_refl.
Qed.

Definition val_of_array (x : ArrayBlk.t) : Val.t :=
  (Zparity.bot, PowLoc.bot, x, PowProc.bot).

Lemma val_of_array_mor : Proper (ArrayBlk.eq ==> Val.eq) val_of_array.
Proof.
 intros i1 i2 Hi.
split; [split; [split|] |]; s
; by auto using Zparity.eq_refl, PowLoc.eq_refl, ArrayBlk.eq_refl, PowProc.eq_refl.
Qed.


Definition val_of_pow_proc (x : PowProc.t) : Val.t :=
  (Zparity.bot, PowLoc.bot, ArrayBlk.bot, x).

Lemma val_of_pow_proc_mor : Proper (PowProc.eq ==> Val.eq) val_of_pow_proc.
Proof.
intros i1 i2 Hi.
split; [split; [split|] |]; s
; by auto using Zparity.eq_refl, PowLoc.eq_refl, ArrayBlk.eq_refl, PowProc.eq_refl.
Qed.

Coercion val_of_zparity : Zparity.t >-> Val.t.
Coercion val_of_pow_loc : PowLoc.t >-> Val.t.
Coercion val_of_array : ArrayBlk.t >-> Val.t.
Coercion val_of_pow_proc : PowProc.t >-> Val.t.

Definition modify_zparity (x : Val.t) (i : Zparity.t) : Val.t :=
  (i, pow_loc_of_val x, array_of_val x, pow_proc_of_val x).

Lemma modify_zparity_mor : Proper (Val.eq ==> Zparity.eq ==> Val.eq) modify_zparity.
Proof. unfold modify_zparity; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[H1 H2] H3] H4] i1 i2 Hi.
split; [split; [split|]|]; assumption.
Qed.

Definition modify_pow_loc (x : Val.t) (l : PowLoc.t) : Val.t :=
  (zparity_of_val x, l, array_of_val x, pow_proc_of_val x).

Lemma modify_pow_loc_mor : Proper (Val.eq ==> PowLoc.eq ==> Val.eq) modify_pow_loc.
Proof. unfold modify_pow_loc; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[H1 H2] H3] H4] i1 i2 Hi.
split; [split; [split|]|]; assumption.
Qed.


Definition modify_array (x : Val.t) (a : ArrayBlk.t) : Val.t :=
  (zparity_of_val x, pow_loc_of_val x, a, pow_proc_of_val x).

Lemma modify_array_mor : Proper (Val.eq ==> ArrayBlk.eq ==> Val.eq) modify_array.
Proof. unfold modify_array; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[H1 H2] H3] H4] i1 i2 Hi.
split; [split; [split|]|]; assumption.
Qed.


Definition modify_pow_proc (x : Val.t) (p : PowProc.t) : Val.t :=
  (zparity_of_val x, pow_loc_of_val x, array_of_val x, p).

Lemma modify_pow_proc_mor : Proper (Val.eq ==> PowProc.eq ==> Val.eq) modify_pow_proc.
Proof. unfold modify_pow_proc; intros [[[x1 y1] z1] a1] [[[x2 y2] z2] a2] [[[H1 H2] H3] H4] i1 i2 Hi.
split; [split; [split|]|]; assumption.
Qed.

