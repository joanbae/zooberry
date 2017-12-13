Set Implicit Arguments.

Require Import Morphisms ZArith.
Require Import hpattern vgtac.
Require Import TStr VocabA DLat.

Module Zparity <: LAT.

Inductive t' := Bot | Top | Even | Odd.
Definition t := t'.


Definition top : t := Top.

Definition bot : t := Bot.

Definition zero : t := Even.

Inductive gamma : Z -> t -> Prop :=
| G_Even : forall z (H: Zeven z), gamma z Even
| G_Odd : forall z (H: Zodd z), gamma z Odd
| G_Top : forall z, gamma z Top.

Definition of_int (i : Z) : t :=
  if Z.even i then Even
  else
    if Z.odd i then Odd
    else Top.

(*correctness의 준말, alpha conversion이 잘 됬는지 알아보는것*)
Lemma cor_of_int : forall z, gamma z (of_int z).
Proof.
  intros. unfold of_int.
  remember (Z.even z) as c; destruct c
  ; [apply G_Even, Zeven_bool_iff; by auto |].
  remember (Z.odd z) as c; destruct c
  ; [apply G_Odd, Zodd_bool_iff; by auto| ].
  apply G_Top.
Qed.

(*
2번쨰 방법
intros. unfold of_int.
remember (Z.even z) as c. destruct c.
{ apply G_Even, Zeven_bool_iff; by auto. }
remember (Z.odd z) as c; destruct c.
{ apply G_Odd, Zodd_bool_iff; by auto. }
{ apply G_Top. }

*)
Inductive le' : t -> t -> Prop :=
| le_bot : forall (x : t), le' Bot x
| le_top : forall (x : t), le' x Top
| le_even : le' Even Even
| le_odd : le' Odd Odd.
Definition le : t -> t -> Prop := le'.

Inductive eq' : t -> t -> Prop :=
| eq_bot : eq' Bot Bot
| eq_top : eq' Top Top
| eq_even : eq' Even Even
| eq_odd : eq' Odd Odd.
Definition eq : t -> t -> Prop := eq'.

Lemma le_refl : forall (x y : t) (Heq : eq x y), le x y.
Proof. 
  intros. inversion Heq.
  - apply le_bot.
  - apply le_top.
  - apply le_even.
  - apply le_odd.
Qed.

Lemma le_antisym :
  forall (x y : t) (le1 : le x y) (le2 : le y x), eq x y.
Proof.

  destruct 1. inversion 1. apply eq_bot.
  inversion 1. apply eq_top.
  inversion 1. apply eq_even.
 intro.  apply eq_odd.
Qed.  

Lemma le_trans :
  forall (x y z : t) (le1 : le x y) (le2 : le y z), le x z.
Proof.
  destruct 1.  inversion 1.
  apply le_bot. apply le_bot.
  apply le_bot. apply le_bot.
  inversion 1.  apply le_top.
  inversion 1.  apply le_top.
  apply le_even.  inversion 1.
  apply le_top. apply le_odd.
Qed.
  
Lemma eq_refl : forall (x : t), eq x x.
Proof. destruct x. apply eq_bot. apply eq_top. apply eq_even. apply eq_odd.
Qed.

Lemma eq_sym : forall (x y : t) (Heq : eq x y), eq y x.
Proof. destruct 1; apply eq_refl. 
Qed.

Lemma eq_trans :
  forall (x y z : t) (eq1 : eq x y) (eq2 : eq y z), eq x z.
Proof. destruct 1; inversion 1; apply eq_refl. 
Qed.

Definition le_dec (x y : t) : {le x y} + {~ le x y}.

  refine (match x, y with
          | Bot, y => left (le_bot y)
          | x, Top => left (le_top x)
          | Even, Even => left le_even
          | Odd, Odd => left le_odd
          | _, _ => right _
        end); inversion 1.
Qed.

(*여기서 eq_dec 이거는 다 도메신상에서 일어나는 것을 가정한다.*)
Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
refine (match x, y with
          | Bot, Bot => left eq_bot
          | Top, Top => left eq_top
          | Even, Even => left eq_even
          | Odd, Odd => left eq_odd
          | _, _ => right _
        end); inversion 1.
Qed.

Local Open Scope sumbool.

Lemma top_prop : forall (x : t), le x top.
Proof. apply le_top. Qed.

Lemma cor_zparity_top : forall z, gamma z top.
Proof. constructor. Qed.

Lemma bot_prop : forall (x : t), le bot x.
Proof. apply le_bot. Qed.

Lemma gamma_monotone : monotone le gamma.
Proof.
  intros v x y. inversion 1; i. inversion Hle.
  apply G_Top.
  apply G_Even. apply H.
  inversion_clear Hle.  apply G_Top.
  apply G_Odd. apply H.
  inversion_clear Hle. apply G_Top.
Qed.

Lemma gamma_mor : Proper (Logic.eq ==> eq ==> Basics.impl) gamma.
Proof.
intros z1 z2 Hz i1 i2 Hi Hleft; subst.
eapply gamma_monotone; [by apply Hleft|by apply le_refl].
Qed.

Lemma non_bot : forall z i (Hz : gamma z i), ~ eq i bot.
Proof.
i. assert (gamma z bot) as Hinv; [|by inversion Hinv].
eapply gamma_mor; [reflexivity|by apply FH|by auto].
Qed.

Definition unknown_binary (x y : t) : t :=
  if eq_dec x Bot ||| eq_dec y Bot then Bot else Top.

Lemma unknown_binary_mor : Proper (eq ==> eq ==> eq) unknown_binary.
Proof.
unfold unknown_binary; intros x1 x2 Hx y1 y2 Hy.
destruct (eq_dec x1 Bot), (eq_dec x2 Bot).
- destruct (eq_dec y1 Bot), (eq_dec y2 Bot).
  + by apply eq_refl.
  + elim f. eapply eq_trans; [|by apply e1]. by apply eq_sym.
  + elim f; eapply eq_trans; [by apply Hy|by auto].
  + by apply eq_refl.
- elim f; eapply eq_trans; [|by apply e]. by apply eq_sym.
- elim f; eapply eq_trans; [by apply Hx|by auto].
- destruct (eq_dec y1 Bot), (eq_dec y2 Bot).
  + by apply eq_refl.
  + elim f1. eapply eq_trans; [|by apply e]. by apply eq_sym.
  + elim f1; eapply eq_trans; [by apply Hy|by auto].
  + by apply eq_refl.
Qed.

Lemma unknown_binary_prop :
  forall z x y (Hx : ~ eq x bot) (Hy : ~ eq y bot), gamma z (unknown_binary x y).
Proof.
i. unfold unknown_binary.
dest_if_dec; [destruct o; tauto|by apply cor_zparity_top].
Qed.

Definition unknown_unary (x : t) : t := if eq_dec x Bot then Bot else top.

Lemma unknown_unary_prop : forall z i (Hi : ~ eq i Bot), gamma z (unknown_unary i).
Proof.
i. unfold unknown_unary.
destruct (eq_dec i Bot); [by auto|by apply cor_zparity_top].
Qed.

Lemma unknown_unary_mor : Proper (eq ==> eq) unknown_unary.
Proof.
unfold unknown_unary; intros x1 x2 Hx.
destruct (eq_dec x1 Bot), (eq_dec x2 Bot).
- by apply eq_refl.
- elim f. apply eq_trans with x1; by auto using eq_sym.
- elim f. apply eq_trans with x2; by auto using eq_sym.
- by apply eq_refl.
Qed.

Definition join (x y : t) : t :=
  match x, y with
    | Bot, a
    | a, Bot => a
    | Even, Even => Even
    | Odd, Odd => Odd
    | Top, _ => Top
    | _, _ => Top
  end.

Lemma join_left : forall (x y : t), le x (join x y).
Proof. intros; destruct x, y; simpl; by constructor. Qed.
(*
  ; constructor

  ; auto using bot_prop, top_prop, le_even, le_odd.

  ; try apply bot_prop
  ; try apply top_prop
  ; try apply le_even
  ; try apply le_odd.
*)

Lemma join_right : forall (x y : t), le y (join x y).
Proof. intros; destruct x, y; simpl; by constructor. Qed.

Lemma join_lub : forall (x y u : t) (Hx : le x u) (Hy : le y u), le (join x y) u.
Proof.
destruct x, y, u; i; simpl; solve [constructor|inversion Hx|inversion Hy].
(*
; first [by constructor|by inversion Hx|by inversion Hy].

; try (by constructor)
; try (by inversion Hx)
; try (by inversion Hy).
*)
Qed.

Definition meet (x y : t) : t :=
  match x, y with
    | Bot, _
    | _, Bot => Bot
    | Even, Even => Even
    | Odd, Odd => Odd
    | Top, Top => Top
    | _, Top => x
    | Top, _ => y
    | _, _ => Bot
  end.

Lemma meet_left : forall (x y : t), le (meet x y) x.
Proof. intros. destruct x, y; simpl; by constructor. Qed.

(*
  ; constructor

  ; auto using bot_prop, top_prop, le_even, le_odd.

  ; try apply bot_prop
  ; try apply top_prop
  ; try apply le_even
  ; try apply le_odd.
*)
  
Lemma meet_right : forall (x y : t), le (meet x y) y.
intros. destruct x, y; by constructor. Qed.

Lemma meet_glb : forall (x y l : t) (Hx : le l x) (Hy : le l y), le l (meet x y).
Proof. destruct x, y, l; i; simpl; solve [constructor| inversion Hx| inversion Hy]. Qed.

Definition widen (x y : t) : t := join x y.

Definition narrow (x y : t) : t := meet x y.

Include JoinMeetProp.

(*Useful Def*)

Definition plus(x y : t) : t :=
  match x, y with
    | Bot, a
    | a, Bot => a
    | Even, Even => Even
    | Odd, Odd => Even
    | Even, Odd => Odd
    | Odd, Even => Odd
    | _, _ => Top
  end.

Definition minus (x y :t) : t :=
  match x, y with
  | Bot, a
  | a, Bot => a
  | Even, Even => Even
  | Odd, Odd => Even
  | Even, Odd => Odd
  | Odd, Even => Odd
  | _, _ => Top
  end.

Definition divide (x y : t) :t :=
  match x, y with
  | Bot, a
  | a, Bot => Bot
  | _, _ => Top
  end.

Definition mod_zparity (x y :t) :t :=
  match x, y with
  | Bot, a
  | a, Bot => Bot
  | Even, Even => Even
  | Even, Odd => Top
  | Odd, Even => Top
  | _, _ => Top
  end.

Definition l_shift_zparity (x y :t) :t := unknown_binary x y.

Lemma l_shift_zparity_mor : Proper (eq ==> eq ==> eq) l_shift_zparity.
Proof. by apply unknown_binary_mor. Qed.

Definition r_shift_zparity (x y :t) :t := unknown_binary x y.

Lemma r_shift_zparity_mor : Proper (eq ==> eq ==> eq) r_shift_zparity.
Proof. by apply unknown_binary_mor. Qed.


Definition lt_zparity (x y :t) :t :=
  match x, y with
  | Bot, a
  | a, Bot => Bot
  | _, _ => Top
  end.


Lemma lt_zparity_mor : Proper (eq ==> eq ==> eq) lt_zparity.
Proof.
unfold lt_zparity; intros x1 x2 Hx y1 y2 Hy.
destruct x1, x2.
- apply eq_bot.
- destruct y2;
 [by apply eq_bot | by apply Hx | by apply Hx | by apply Hx ].
- destruct y2; 
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct Hy;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy| by inversion Hy].
-  destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy|  inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.   
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
  inversion Hx. inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply Hy. apply eq_top. apply eq_top.
Qed.


Definition gt_zparity (x y :t) :t := lt_zparity y x.

Lemma gt_zparity_mor : Proper (eq ==> eq ==> eq) gt_zparity.
Proof. unfold gt_zparity. intros x1 x2 Hx y1 y2 Hy. by apply lt_zparity_mor. Qed.

Definition not_zparity (x : t) : t :=
  if eq_dec x Bot then Bot else top.

Lemma not_zparity_prop1 :
  forall z i (Hz : z <> 0%Z) (Hi : gamma z i), gamma 0 (not_zparity i).
Proof.
i. unfold not_zparity.
destruct (eq_dec i Bot).
inversion e; subst. inversion Hi; subst. by apply G_Top.
Qed.

Lemma not_zparity_prop2 : forall i (Hi : gamma 0 i), gamma 1 (not_zparity i).
Proof.
i. unfold not_zparity.
destruct (eq_dec i Bot).
inversion e; subst. inversion Hi. by apply G_Top.
Qed.

Lemma not_zparity_mor : Proper (eq ==> eq) not_zparity.
Proof.
unfold not_zparity; intros x y Hq.
destruct (eq_dec x Bot), (eq_dec y Bot); try (by apply eq_refl)
; [inversion e; subst; inversion Hq; subst; apply f in e; inversion e
 | inversion e; subst; inversion Hq; subst; apply f in e; inversion e].
Qed.

Definition le_zparity (x y :t) :t :=
  match x, y with
  | Bot, a
  | a, Bot => Bot
  | _, _ => Top
  end.

Lemma le_zparity_mor : Proper (eq ==> eq ==> eq) le_zparity.
Proof.
  unfold le_zparity; intros x1 x2 Hx y1 y2 Hy.
  destruct x1, x2.
  - apply eq_bot.
  - destruct y2;
 [by apply eq_bot | by apply Hx | by apply Hx | by apply Hx ].
- destruct y2; 
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct Hy;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy| by inversion Hy].
-  destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy|  inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.   
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
  inversion Hx. inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply Hy. apply eq_top. apply eq_top.  
Qed.

Definition ge_zparity (x y :t) :t := le_zparity y x.

Lemma ge_zparity_mor : Proper (eq ==> eq ==> eq) ge_zparity.
Proof. unfold ge_zparity. intros x1 x2 Hx y1 y2 Hy. by apply le_zparity_mor. Qed.

Definition eq_zparity (x y :t ) :t :=
  match x, y with
  | Bot, a
  | a, Bot => Bot
  | _, _ => Top
  end.

Lemma eq_zparity_mor : Proper (eq ==> eq ==> eq) eq_zparity.
Proof. unfold eq_zparity; intros x1 x2 Hx y1 y2 Hy.
  destruct x1, x2.
  - apply eq_bot.
  - destruct y2;
 [by apply eq_bot | by apply Hx | by apply Hx | by apply Hx ].
- destruct y2; 
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct Hy;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy| by inversion Hy].
-  destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy|  inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.   
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
  inversion Hx. inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply Hy. apply eq_top. apply eq_top.  
Qed.


Definition ne_zparity (x y :t ) :t :=
  match x, y with
  | Bot, a
  | a, Bot => Bot
  | _, _ => Top
  end.

Lemma ne_zparity_mor : Proper (eq ==> eq ==> eq) ne_zparity.
Proof.
unfold ne_zparity; intros x1 x2 Hx y1 y2 Hy.
  destruct x1, x2.
  - apply eq_bot.
  - destruct y2;
 [by apply eq_bot | by apply Hx | by apply Hx | by apply Hx ].
- destruct y2; 
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct Hy;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy| by inversion Hy].
-  destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy|  inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.   
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
  inversion Hx. inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply Hy. apply eq_top. apply eq_top.  
Qed.

  
Definition b_and_zparity (x y : t) : t := unknown_binary x y.

Lemma b_and_zparity_mor : Proper (eq ==> eq ==> eq) b_and_zparity.
Proof. by apply unknown_binary_mor. Qed.

Definition b_xor_zparity (x y : t) : t := unknown_binary x y.

Lemma b_xor_zparity_mor : Proper (eq ==> eq ==> eq) b_xor_zparity.
Proof. by apply unknown_binary_mor. Qed.

Definition b_or_zparity (x y : t) : t := unknown_binary x y.

Lemma b_or_zparity_mor : Proper (eq ==> eq ==> eq) b_or_zparity.
Proof. by apply unknown_binary_mor. Qed.

Definition b_not_zparity (x : t) : t := unknown_unary x.

Lemma b_not_zparity_mor : Proper (eq ==> eq) b_not_zparity.
Proof. by apply unknown_unary_mor. Qed.

Definition and_zparity (x y : t) : t :=
  match x, y with
  | Bot, a
  | a, Bot => Bot
  | _, _ => Top
  end.

Lemma and_zparity_mor : Proper (eq ==> eq ==> eq) and_zparity.
Proof.
  unfold and_zparity; intros x1 x2 Hx y1 y2 Hy.
  destruct x1, x2.
  - apply eq_bot.
  - destruct y2;
 [by apply eq_bot | by apply Hx | by apply Hx | by apply Hx ].
- destruct y2; 
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct Hy;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy| by inversion Hy].
-  destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy|  inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.   
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
  inversion Hx. inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply Hy. apply eq_top. apply eq_top.  
Qed.

Definition or_zparity (x y : t) : t :=
  match x, y with
  | Bot, a
  | a, Bot => Bot
  | _, _ => Top
  end.

Lemma or_zparity_mor : Proper (eq ==> eq ==> eq) or_zparity.
Proof.
unfold or_zparity; intros x1 x2 Hx y1 y2 Hy.
  destruct x1, x2.
  - apply eq_bot.
  - destruct y2;
 [by apply eq_bot | by apply Hx | by apply Hx | by apply Hx ].
- destruct y2; 
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct Hy;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1;
    [inversion Hx | inversion Hx | inversion Hx| inversion Hx].
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy| by inversion Hy].
-  destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy|  inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx.
   inversion Hx.
   inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
   inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| by inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply eq_top.
 apply eq_top.   
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 inversion Hx. inversion Hx. inversion Hx.
- destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
  inversion Hx. inversion Hx. inversion Hx.
-destruct y1, y2;
  [ apply Hy | by inversion Hy| by inversion Hy| by inversion Hy|
      by inversion Hy| inversion Hy| by inversion Hy| by inversion Hy|
        by inversion Hy| by inversion Hy | inversion Hy | by inversion Hy|
          by inversion Hy|by inversion Hy|by inversion Hy|  inversion Hy].
 apply Hy. apply eq_top. apply eq_top.  
Qed.

Lemma plus_mor : Proper (eq ==> eq ==> eq) plus.
Proof.
  unfold Proper, respectful.
  inversion_clear 1.
(* 
the tactics below is same as (unfold Proper, respectful. inversion_clear 1)
intros x y H.
inversion H.
clear H. *)
  - intros. inversion H.
    * s. by apply eq_bot.
    * s. by apply eq_top.
    * s. by apply eq_even.
    * s. by apply eq_odd.
  - intros. inversion H.
    * s; by apply eq_top.
    * s. by apply eq_top.
    * s. by apply eq_top.
    * s. by apply eq_top.
  - intros. inversion H.
    * s. by apply eq_even.
    * s. by apply eq_top.
    * s. by apply eq_even.
    * s. by apply eq_odd.
  - intros. inversion H.
    * s. by apply eq_odd.
    * s. by apply eq_top. 
    * s. by apply eq_odd.
    * s. by apply eq_even.
Qed.

Lemma cor_plus :
  forall z1 z2 i1 i2 (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma (z1 + z2) (plus i1 i2).
Proof.
i. unfold plus.
destruct i1, i2;
  try (by apply G_Top); try (by apply G_Bot) ;try (by inversion Hz1)
  ;try (by inversion Hz2); try inversion Hz1; try inversion Hz2
  ;constructor; try (by apply Zeven_plus_Zeven); try (by apply Zodd_plus_Zodd)
  ;try (by apply Zeven_plus_Zodd);try (by apply Zodd_plus_Zeven).
Qed.

Lemma plus_non_bot :
  forall (i j : t) (Hi : ~ eq i bot) (Hj : ~ eq j bot), ~ eq (plus i j) bot.
Proof. destruct i, j;
         [ inversion 3; apply Hi; apply eq_bot
         | inversion 3 | inversion 3| inversion 3
         | inversion 3| inversion 3| inversion 3
         | inversion 3| inversion 3| inversion 3
         | inversion 3| inversion 3| inversion 3
         | inversion 3| inversion 3| inversion 3].
Qed.

Lemma minus_mor : Proper (eq ==> eq ==> eq) minus.
Proof.
unfold Proper, respectful.
inversion_clear 1; inversion_clear 1;
  [ s; by apply eq_bot | s; by apply eq_top | s; by apply eq_even
    | s; by apply eq_odd |s; by apply eq_top | s; by apply eq_top
    | s; by apply eq_top |s; by apply eq_top | s; by apply eq_even
    | s; by apply eq_top |s; by apply eq_even | s; by apply eq_odd
    | s; by apply eq_odd |s; by apply eq_top | s; by apply eq_odd
    | s; by apply eq_even ].
Qed.

Lemma Zeven_minus_Zeven: forall a b : Z, Zeven a -> Zeven b -> Zeven (a - b).
Proof.
  i. rewrite <- Z.add_opp_r.
  apply Zeven_plus_Zeven; [by auto|].
  assert (-b = -1 * b) % Z as Hminusb; [omega|rewrite Hminusb].
  by apply Zeven_mult_Zeven_r.
Qed.

(*  i.
rewrite <- Z.add_opp_r.
apply Zeven_plus_Zeven; [by auto|].
assert (-b = -1 * b)%Z as Hminusb; [omega|rewrite Hminusb].
by apply Zeven_mult_Zeven_r.
Qed.
Z
even_mult_Zeven_l: forall a b : Z, Zeven a -> Zeven (a * b)
Zeven_mult_Zeven_r: forall a b : Z, Zeven b -> Zeven (a * b)


a + (-b)

Z.add_opp_r: forall n m : Z, (n + - m)%Z = (n - m)%Z

Zeven_plus_Zeven: forall a b : Z, Zeven a -> Zeven b -> Zeven (a + b)

*)

Lemma Zeven_minus_Zodd: forall a b : Z, Zeven a -> Zodd b -> Zodd (a - b).
Proof.
  i. rewrite <- Z.add_opp_r.
  apply Zeven_plus_Zodd; [by auto|].
  assert (-b = -1 * b) % Z as Hminusb; [omega | rewrite Hminusb].
  apply Zodd_mult_Zodd; [ apply Zodd_bool_iff; reflexivity| by auto].
Qed.

Lemma Zodd_minus_Zeven: forall a b : Z, Zodd a -> Zeven b -> Zodd (a - b).
Proof.
  i. rewrite <- Z.add_opp_r.
  apply Zodd_plus_Zeven; [by auto|].
 assert (-b = -1 * b) % Z as Hminusb; [omega | rewrite Hminusb].
 apply Zeven_mult_Zeven_r; apply H0.
Qed.

Lemma Zodd_minus_Zodd: forall a b : Z, Zodd a -> Zodd b -> Zeven (a - b).
Proof.
  i. rewrite <- Z.add_opp_r.
  apply Zodd_plus_Zodd; [by auto|].
  assert (-b = -1 * b) % Z as Hminusb; [omega | rewrite Hminusb].
  apply Zodd_mult_Zodd; [by auto| by auto].
Qed.

Lemma cor_minus :
  forall z1 z2 i1 i2 (Hz1 : gamma z1 i1) (Hz2 : gamma z2 i2),
    gamma (z1 - z2) (minus i1 i2).
Proof.
   i. unfold minus.
  destruct i1, i2; try (by apply G_Top)
  ; try (by inversion Hz1); try (by inversion Hz2)
  ; inversion_clear Hz1 as [z1' Hz1'|z1' Hz1'|]
  ; inversion_clear Hz2 as [z2' Hz2'|z2' Hz2'|]
  ; subst; constructor.
  - by apply Zeven_minus_Zeven.
  - by apply Zeven_minus_Zodd.
  - by apply Zodd_minus_Zeven.
  - by apply Zodd_minus_Zodd.
    
Qed.

Lemma minus_non_bot :
  forall (i j : t) (Hi : ~ eq i bot) (Hj : ~ eq j bot), ~ eq (minus i j) bot.
Proof. destruct i, j;
         [ inversion 3; apply Hi; apply eq_bot
         | inversion 3 | inversion 3| inversion 3
         | inversion 3| inversion 3| inversion 3
         | inversion 3| inversion 3| inversion 3
         | inversion 3| inversion 3| inversion 3
         | inversion 3| inversion 3| inversion 3].
Qed.

Lemma divide_prop :
  forall z1 z2 x1 x2 (H1: gamma z1 x1) (H2: gamma z2 x2),
    gamma (c_div z1 z2)%Z (divide x1 x2).
Proof.
  inversion_clear 1; inversion_clear 1; unfold divide;
    try (by apply G_Top).
Qed.

Lemma divide_mor : Proper (eq ==> eq ==> eq) divide.
Proof.
  inversion_clear 1; inversion_clear 1;
    [  by apply eq_refl | by apply eq_refl | by apply eq_refl
      | by apply eq_refl | by apply eq_refl | by apply eq_refl
      | by apply eq_refl | by apply eq_refl | by apply eq_refl
      | by apply eq_refl| by apply eq_refl| by apply eq_refl
      | by apply eq_refl| by apply eq_refl| by apply eq_refl
      | by apply eq_refl].
Qed.

Definition times (x y :t) :t :=
  match x, y with
  | Bot, a
  | a, Bot => Bot
  | Even, Even => Even
  | Odd, Odd => Odd
  | Even, Odd => Even
  | Odd, Even => Even
  | _, _ => Top
  end.

Lemma times_mor : Proper (eq ==> eq ==> eq) times.
Proof.
  inversion_clear 1; inversion_clear 1;
     [  by apply eq_refl | by apply eq_refl | by apply eq_refl
      | by apply eq_refl | by apply eq_refl | by apply eq_refl
      | by apply eq_refl | by apply eq_refl | by apply eq_refl
      | by apply eq_refl| by apply eq_refl| by apply eq_refl
      | by apply eq_refl| by apply eq_refl| by apply eq_refl
      | by apply eq_refl].

Qed.

Lemma times_prop_even_even:
  forall z1 z2 (H1: Zeven z1) (H2: Zeven z2), Zeven (z1 * z2).
Proof.
  i. by apply Zeven_mult_Zeven_l. Qed.

Lemma times_prop_odd_even:
  forall z1 z2 (H1: Zodd z1) (H2: Zeven z2), Zeven (z1 * z2).
Proof.
i. by apply Zeven_mult_Zeven_r. Qed.

Lemma times_prop_even_odd:
  forall z1 z2 (H1: Zeven z1) (H2: Zodd z2), Zeven (z1 * z2).
Proof.
i. by apply Zeven_mult_Zeven_l. Qed.

Lemma times_prop_odd_odd:
  forall z1 z2 (H1: Zodd z1) (H2: Zodd z2), Zodd (z1 * z2).
Proof.
i. by apply Zodd_mult_Zodd. Qed.

Lemma times_prop :
  forall z1 z2 x1 x2 (H1: gamma z1 x1) (H2: gamma z2 x2),
    gamma (z1 * z2)%Z (times x1 x2).
Proof. 
  inversion_clear 1; inversion_clear 1; subst; s;
    try (by apply G_Top); try (by apply G_Even); try (by apply G_Odd).
  - apply G_Even. by apply times_prop_even_even.
  - apply G_Even. by apply times_prop_even_odd.
  - apply G_Even. by apply times_prop_odd_even. 
  - apply G_Odd. by apply times_prop_odd_odd.
Qed.    

Lemma mod_zparity_mor : Proper (eq ==> eq ==> eq) mod_zparity.
Proof. unfold Proper, respectful.
       intros. inversion_clear H. inversion_clear H0.
       s. by apply eq_bot.
       s. by apply eq_bot.
       s. by apply eq_bot.
       s. by apply eq_bot.
       inversion_clear H0.
       s. by apply eq_bot.
       s. by apply eq_top.
       s. by apply eq_top.
       s. by apply eq_top.
       inversion_clear H0.
       s. by apply eq_bot.
       s. by apply eq_top.
       s. by apply eq_even.
       s. by apply eq_top.

       inversion_clear H0.
       s. by apply eq_bot.
       s. by apply eq_top.
       s. by apply eq_top.
       s. by apply eq_top.
Qed.
End Zparity.
