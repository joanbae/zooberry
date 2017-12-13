(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
(** * Eval semantics of expression.  *)

Set Implicit Arguments.

Require Import String ZArith Morphisms.
Require Import Monad hpattern vgtac VocabA Syn DLat DPow UserInputType.
Require Import Zparity DomBasic DomArrayBlk DomAbs DomMem SemMem.

Local Open Scope Z.
Local Open Scope sumbool.

Definition eval_const cst :=
  match cst with
    | CInt64 (Some z)
    | CChr z =>
      match Zeven_dec z with
      | left _ => val_of_zparity Zparity.Even
      | right _ => val_of_zparity Zparity.Odd
      end
    | _ => val_of_zparity Zparity.top
  end.

Definition eval_uop (u : unop) (v : Val.t) : Val.t :=
  if Val.eq_dec v Val.bot then Val.bot else
    match u with
    | Neg => Zparity.minus Zparity.Even (zparity_of_val v)
    | BNot => Zparity.b_not_zparity (zparity_of_val v)
    | LNot => Zparity.not_zparity (zparity_of_val v)
    end.

Lemma eval_uop_mor (u : unop) : Proper (Val.eq ==> Val.eq) (eval_uop u).
Proof.
  unfold eval_uop. intros v1 v2 Hv.
  destruct (Val.eq_dec v1 Val.bot), (Val.eq_dec v2 Val.bot).
  - by apply Val.eq_refl.
  - elim f. eapply Val.eq_trans; [| by apply e].
    apply Val.eq_sym. apply Hv.
  - elim f; eapply Val.eq_trans; [by apply Hv| assumption].
  - destruct u; apply val_of_zparity_mor.
    + apply Zparity.minus_mor; [by apply Zparity.eq_refl | by apply Hv].
    + apply Zparity.b_not_zparity_mor. by apply Hv.
    + apply Zparity.not_zparity_mor; by apply Hv.
Qed.

Definition is_array_loc x :=
  match x with
    | Loc.Inl (VarAllocsite.Inr _, _) => true
    | _ => false
  end.

Lemma is_array_loc_mor : Proper (Loc.eq ==> eq) is_array_loc.
Proof. unfold is_array_loc; intros x1 x2 Hx.
destruct x1, x2; [|by inversion Hx|by inversion Hx|by auto].
destruct a, a0. destruct t, t1.
- by auto.
- inversion Hx; destruct Heq as [Heq _]; by inversion Heq.
- inversion Hx; destruct Heq as [Heq _]; by inversion Heq.
- by auto.
Qed.

Definition array_loc_of_val v :=
  PowLoc.filter is_array_loc (pow_loc_of_val v).

Lemma array_loc_of_val_mor : Proper (Val.eq ==> Val.eq) array_loc_of_val.
Proof. unfold array_loc_of_val; intros v1 v2 Hv.
apply val_of_pow_loc_mor.
apply PowLoc.SS.SF.filter_equal; [by apply is_array_loc_mor|by apply Hv].
Qed.

Definition eval_bop b v1 v2 : Val.t :=
  match b with
  | PlusA => Zparity.plus (zparity_of_val v1) (zparity_of_val v2)
  | PlusPI | IndexPI =>
    Val.join
      (array_loc_of_val v1)
      (ArrayBlk.plus_offset (array_of_val v1) (zparity_of_val v2))
  | MinusA => Zparity.minus (zparity_of_val v1) (zparity_of_val v2)
  | MinusPI =>
    Val.join
      (array_loc_of_val v1)
      (ArrayBlk.minus_offset (array_of_val v1) (zparity_of_val v2))
  | MinusPP => Zparity.top
  | Mult => Zparity.times (zparity_of_val v1) (zparity_of_val v2)
  | Div => Zparity.divide (zparity_of_val v1) (zparity_of_val v2)
  | Mod => Zparity.mod_zparity (zparity_of_val v1) (zparity_of_val v2)
  | Shiftlt => Zparity.l_shift_zparity (zparity_of_val v1) (zparity_of_val v2)
  | Shiftrt => Zparity.r_shift_zparity (zparity_of_val v1) (zparity_of_val v2)
  | Lt => Zparity.lt_zparity (zparity_of_val v1) (zparity_of_val v2)
  | Gt => Zparity.gt_zparity (zparity_of_val v1) (zparity_of_val v2)
  | Le => Zparity.le_zparity (zparity_of_val v1) (zparity_of_val v2)
  | Ge => Zparity.ge_zparity (zparity_of_val v1) (zparity_of_val v2)
  | Eq => Zparity.eq_zparity (zparity_of_val v1) (zparity_of_val v2)
  | Ne => Zparity.ne_zparity (zparity_of_val v1) (zparity_of_val v2)
  | BAnd => Zparity.b_and_zparity (zparity_of_val v1) (zparity_of_val v2)
  | BXor => Zparity.b_xor_zparity (zparity_of_val v1) (zparity_of_val v2)
  | BOr => Zparity.b_or_zparity (zparity_of_val v1) (zparity_of_val v2)
  | LAnd => Zparity.and_zparity (zparity_of_val v1) (zparity_of_val v2)
  | LOr => Zparity.or_zparity (zparity_of_val v1) (zparity_of_val v2)
  end.

Lemma eval_bop_mor (b : binop) :
  Proper (Val.eq ==> Val.eq ==> Val.eq) (eval_bop b).
Proof.
  unfold eval_bop. intros v1 v2 Hv w1 w2 Hw; destruct b.
  - apply val_of_zparity_mor. apply Zparity.plus_mor; [by apply Hv|by apply Hw].
  - apply Val.join_eq.
  + by apply array_loc_of_val_mor.
  + apply val_of_array_mor.
    apply ArrayBlk.plus_offset_mor; [by apply Hv|by apply Hw].
- apply Val.join_eq.
  + by apply array_loc_of_val_mor.
  + apply val_of_array_mor.
    apply ArrayBlk.plus_offset_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor.
  apply Zparity.minus_mor; [by apply Hv|by apply Hw].
- apply Val.join_eq.
  + by apply array_loc_of_val_mor.
  + apply val_of_array_mor.
    apply ArrayBlk.minus_offset_mor; [by apply Hv|by apply Hw].
- by apply Val.eq_refl.
- split; [split; [split|] |].
  + s. apply Zparity.times_mor; [by apply Hv|by apply Hw].
  + s. by apply PowLoc.eq_refl.
  + s. by apply ArrayBlk.eq_refl.
  + s. by apply PowProc.eq_refl.
- split; [split; [split|] |].
  + s. apply Zparity.divide_mor; [by apply Hv|by apply Hw].
  + s. by apply PowLoc.eq_refl.
  + s. by apply ArrayBlk.eq_refl.
  + s. by apply PowProc.eq_refl.
- apply val_of_zparity_mor. apply Zparity.mod_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.l_shift_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.r_shift_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.lt_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.gt_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.le_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.ge_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.eq_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.ne_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.b_and_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.b_xor_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.b_or_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.and_zparity_mor; [by apply Hv|by apply Hw].
- apply val_of_zparity_mor. apply Zparity.or_zparity_mor; [by apply Hv|by apply Hw].
Qed.

Definition eval_string (s : string) : Val.t := Zparity.top.

Definition eval_string_loc (s : string) (a : Allocsite.t) (lvs : PowLoc.t)
           : Val.t := Zparity.top.

Definition deref_of_val v :=
  PowLoc.join (pow_loc_of_val v) (ArrayBlk.pow_loc_of_array (array_of_val v)).

Lemma deref_of_val_mor : Proper (Val.eq ==> PowLoc.eq) deref_of_val.
Proof.
unfold deref_of_val; intros v1 v2 Hv.
apply PowLoc.join_eq.
- by apply pow_loc_of_val_mor.
- apply ArrayBlk.pow_loc_of_array_mor. by apply array_of_val_mor.
Qed.

Module Make (Import M : Monad) (MB : MemBasic M).

Module Import SemMem := SemMem.Make M MB.

Definition eval_var node x (is_global : bool) :=
  if is_global then loc_of_var (var_of_gvar x) else
    loc_of_var (var_of_lvar (InterNode.get_pid node, x)).

Fixpoint eval (mode : update_mode) (node : InterNode.t)
         (e : exp) (m : Mem.t) : M.m Val.t :=
  match e with
  | Const c _ => ret (eval_const c)
  | Lval l _ =>
    do lv <- eval_lv mode node l m ;
    mem_lookup lv m
  | SizeOf t_opt _ =>
    let t_itv := match t_opt with
                   | None => Zparity.top
                   | Some t => Zparity.of_int t
                 end in
    ret (t_itv : Val.t)
  | SizeOfE e_opt _ =>
    let e_itv := match e_opt with
                   | None => Zparity.top
                   | Some e => Zparity.of_int e
                 end in
    ret (e_itv : Val.t)
  | SizeOfStr s _ =>
    let i := Z_of_nat (S (String.length s)) in
    ret (Zparity.of_int i : Val.t)
  | AlignOf t _ => ret (Zparity.of_int t : Val.t)
  | AlignOfE _ _ => ret (Zparity.top : Val.t)
  | UnOp u e _ =>
    do v <- eval mode node e m ;
    ret (eval_uop u v)
  | BinOp b e1 e2 _ =>
    do v1 <- (eval mode node e1 m) ;
    do v2 <- (eval mode node e2 m) ;
    ret (eval_bop b v1 v2)
  | Question e1 e2 e3 _ =>
    do v1 <- (eval mode node e1 m) ;
    let i1 : Zparity.t := zparity_of_val v1 in
    if Zparity.eq_dec i1 Zparity.bot then ret Val.bot else
      do v2 <- eval mode node e2 m ;
      do v3 <- eval mode node e3 m ;
      ret (Val.join v2 v3)
  | CastE new_stride_opt e _ =>
    match new_stride_opt with
    | None => eval mode node e m
    | Some new_stride =>
      do v <- eval mode node e m ;
      let array_v := ArrayBlk.cast_array_int new_stride (array_of_val v) in
      ret (modify_array v array_v)
    end
  | AddrOf l _ =>
    do lv <- eval_lv mode node l m ;
    ret (val_of_pow_loc lv)
  | StartOf l _ =>
    do lv <- eval_lv mode node l m ;
    ret (val_of_pow_loc lv)
  end

with eval_lv (mode : update_mode) (node : InterNode.t)
             (lv : lval) (m : Mem.t) : M.m PowLoc.t :=
  match lv with
  | lval_intro lhost' ofs _ =>
    do v <-
      match lhost' with
      | VarLhost vi is_global =>
        let x := eval_var node vi is_global in
        ret ((PowLoc.singleton x) : Val.t)
      | MemLhost e => eval mode node e m
      end ;
    resolve_offset mode node v ofs m
  end

with resolve_offset (mode : update_mode) (node : InterNode.t)
                    (v : Val.t) (os : offset) (m : Mem.t)
: M.m PowLoc.t :=
  match os with
  | NoOffset => ret (deref_of_val v)
  | FOffset f os' =>
    resolve_offset mode node
      (PowLoc.join
         (pow_loc_append_field (pow_loc_of_val v) f)
         (ArrayBlk.pow_loc_of_struct_w_field (array_of_val v) f))
      os' m
  | IOffset e os' =>
    do idx <- eval mode node e m ;
    do v' <- mem_lookup (deref_of_val v) m ;
    let v' :=
        modify_array
          v'
          (ArrayBlk.plus_offset (array_of_val v') (zparity_of_val idx))
    in
    resolve_offset mode node v' os' m
  end.

Fixpoint eval_list (mode : update_mode) (node : InterNode.t)
         (es : list exp) (m : Mem.t) : M.m (list Val.t) :=
  match es with
    | nil => ret nil
    | e :: tl =>
      do v <- eval mode node e m;
      do tl' <- eval_list mode node tl m;
      ret (v :: tl')
  end.

Definition eval_alloc' (node : InterNode.t) (sz_v : Val.t) : Val.t := Zparity.top.
Definition eval_alloc (mode : update_mode) (node : InterNode.t) (a : alloc) (mem : Mem.t)
: M.m Val.t :=
  match a with
  | Array e =>
    do sz_v <- eval mode node e mem ;
    ret (eval_alloc' node sz_v)
  end.
  
End Make.

Local Close Scope sumbool.
Local Close Scope Z.
