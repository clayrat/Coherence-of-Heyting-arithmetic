(**************************************************************************)
(*              Coherence of first-order Heyting arithmetic               *)
(*                                                                        *)
(*                         © 2011 Stéphane Glondu                         *)
(*                         © 2013 Pierre Letouzey                         *)
(*   modified by Alice Rixte, Farzad JafarRahmani, and Younesse Kaddar    *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*   it under the terms of the CeCILL free software license, version 2.   *)
(**************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq.

Section Imply.

Lemma imply_pair a b c d :
  a ==> c -> b ==> d -> a && b ==> c && d.
Proof. by case: a=>//= ->. Qed.

End Imply.

Section Cmp.

Variant cmp_val := LT | EQ | GT.

Definition cmp (x y : nat) : cmp_val :=
  if x < y then LT else if x == y then EQ else GT.

Lemma cmpxx x : cmp x x = EQ.
Proof. by rewrite /cmp eqxx ltnn. Qed.

Variant cmp_spec (x y : nat) : cmp_val -> cmp_val -> bool -> bool -> bool -> bool -> Set :=
  | CmpLt of x < y : cmp_spec x y LT GT true  false false false
  | CmpEq of x = y : cmp_spec x y EQ EQ false true  true  false
  | CmpGt of x > y : cmp_spec x y GT LT false false false true.

Lemma cmpE (x y : nat) : cmp_spec x y (cmp x y) (cmp y x) (x < y) (x == y) (y == x) (y < x).
Proof. by rewrite /cmp; case: ltngtP=>H; constructor. Qed.

Lemma cmp2l x y z : cmp (z + x) (z + y) = cmp x y.
Proof. by rewrite /cmp ltn_add2l eqn_add2l. Qed.

End Cmp.

(*
(* Tactics *)

(* First, tell the "auto" tactic to use the "lia" solver. *)

Hint Extern 8 (_ = _ :> nat) => lia.
Hint Extern 8 (_ <= _) => lia.
Hint Extern 8 (_ < _) => lia.
Hint Extern 8 (_ <> _ :> nat) => lia.
Hint Extern 8 (~ (_ <= _)) => lia.
Hint Extern 8 (~ (_ < _)) => lia.
Hint Extern 12 => exfalso; lia.

(* Destructing the <=? and ?= (in)equality tests, useful when proving facts
   about "if ... then ... else" code. *)

Ltac break := match goal with
 | |- context [ ?x <=? ?y ] => destruct (Nat.leb_spec x y)
 | |- context [ ?x ?= ?y ] => destruct (Nat.compare_spec x y)
end.
*)

(* Terms : first-order terms over the Peano signature 0 S + *.
   The variable are represented as De Bruijn indices. *)

Inductive term : Type :=
  | Tvar of nat
  | Tzero
  | Tsucc of term
  | Tplus of term & term
  | Tmult of term & term.

Fixpoint eqterm (t1 t2 : term) : bool :=
  match t1, t2 with
  | Tvar n1, Tvar n2 => n1 == n2
  | Tzero, Tzero => true
  | Tsucc t1, Tsucc t2 => eqterm t1 t2
  | Tplus t1 u1, Tplus t2 u2 => eqterm t1 t2 && eqterm u1 u2
  | Tmult t1 u1, Tmult t2 u2 => eqterm t1 t2 && eqterm u1 u2
  | _, _ => false
  end.

Lemma eqtermP : Equality.axiom eqterm.
Proof.
elim=>[n1||t1 IH1|t1 IHt u1 IHu|t1 IHt u1 IHu]; case=>[n2||t2|t2 u2|t2 u2] /=;
try by constructor.
- by apply: (iffP idP)=>[/eqP->|[->]].
- by apply: (iffP (IH1 t2))=>[->|[]].
- by apply: (iffP andP)=>[[/IHt->/IHu->]|[<-<-]] //; split; [apply/IHt | apply/IHu].
by apply: (iffP andP)=>[[/IHt->/IHu->]|[<-<-]] //; split; [apply/IHt | apply/IHu].
Qed.

Canonical term_eqMixin := EqMixin eqtermP.
Canonical term_eqType := Eval hnf in EqType term term_eqMixin.

(*Hint Extern 10 (Tvar _ = Tvar _) => f_equal.*)

(* Term lifting: add n to all variables of t which are >= k *)

Fixpoint tlift (n : nat) (t : term) (k : nat) : term :=
  match t with
  | Tvar i => Tvar (if k <= i then n+i else i)
  | Tzero => Tzero
  | Tsucc u => Tsucc (tlift n u k)
  | Tplus u v => Tplus (tlift n u k) (tlift n v k)
  | Tmult u v => Tmult (tlift n u k) (tlift n v k)
  end.

Lemma tlift_1 t n n' k k' :
  k <= k' <= k + n ->
  tlift n' (tlift n t k) k' = tlift (n' + n) t k.
Proof.
case/andP=>Hk1 Hk2; elim: t=>//=; first 1 last.
- by move=>t ->.
- by move=>t1 -> t2 ->.
- by move=>t1 -> t2 ->.
move=>m; case/boolP: (k <= m)=>Hkm.
- case: ifP; first by rewrite addnA.
  move/negbT; rewrite -ltnNge.
  rewrite -(leq_add2r n) in Hkm.
  by move: (leq_trans Hk2 Hkm); rewrite addnC leqNgt => /[swap]->.
rewrite -ltnNge in Hkm.
by move: (leq_trans Hkm Hk1); rewrite ltnNge=>/negbTE->.
Qed.

Lemma tlift_2 t n n' k k' :
  k' <= k ->
  tlift n' (tlift n t k) k' = tlift n (tlift n' t k') (n' + k).
Proof.
move=>Hk; elim: t=>//=; first 1 last.
- by move=>t ->.
- by move=>t1 -> t2 ->.
- by move=>t1 -> t2 ->.
move=>m; case/boolP: (k <= m)=>Hkm.
- move: (leq_trans Hk Hkm)=>Hkm'; rewrite Hkm' leq_add2l Hkm.
  move: (leq_add Hkm' (leq0n n)); rewrite addn0 addnC=>->.
  by rewrite addnCA.
case: ifP=>[|_].
- by rewrite leq_add2l (negbTE Hkm).
rewrite -ltnNge in Hkm; move/(ltn_addl n'): Hkm.
by rewrite ltnNge=>/negbTE->.
Qed.

(* Term substitution: replace variable x by (tlift x t' 0) in t *)

Fixpoint tsubst (x : nat) (t' t : term) : term :=
  match t with
    | Tvar i =>
      match cmp x i with
        | EQ => tlift x t' 0
        | LT => Tvar i.-1
        | GT => Tvar i
      end
    | Tzero => Tzero
    | Tsucc u => Tsucc (tsubst x t' u)
    | Tplus u v => Tplus (tsubst x t' u) (tsubst x t' v)
    | Tmult u v => Tmult (tsubst x t' u) (tsubst x t' v)
  end.

Lemma tsubst_1 t x t' n k :
  k <= x <= k + n ->
  tsubst x t' (tlift n.+1 t k) = tlift n t k.
Proof.
case/andP=>Hx1 Hx2; elim: t=>//=; first 1 last.
- by move=>t ->.
- by move=>t1 -> t2 ->.
- by move=>t1 -> t2 ->.
move=>m; case/boolP: (k <= m)=>Hkm.
- rewrite -(leq_add2r n) in Hkm; move: (leq_trans Hx2 Hkm).
  rewrite addnC addSn /=; case: cmpE=>//.
  - by rewrite ltnNge=>/[swap]; rewrite -ltnS=>/ltnW->.
  by move=><-; rewrite ltnn.
rewrite -ltnNge in Hkm; move: (leq_trans Hkm Hx1).
by case: cmpE.
Qed.

Lemma tsubst_2 t x t' n k :
  k <= x ->
  tlift n (tsubst x t' t) k = tsubst (n + x) t' (tlift n t k).
Proof.
move=>Hx; elim: t=>//=; first 1 last.
- by move=>t ->.
- by move=>t1 -> t2 ->.
- by move=>t1 -> t2 ->.
move=>m; case/boolP: (k <= m)=>Hkm.
- rewrite cmp2l; case: cmpE=>/= Hmx.
  - by rewrite Hkm.
  - by apply: tlift_1; rewrite add0n.
  move: (leq_ltn_trans Hx Hmx)=>{}Hkm.
  rewrite -ltnS (ltn_predK Hkm) Hkm -!subn1 addnBA //.
  by rewrite -ltn_predL (ltn_predK Hkm).
rewrite -ltnNge in Hkm; move: (leq_trans Hkm Hx).
case: cmpE=>//= Hmx _; rewrite leqNgt Hkm /=.
case: cmpE=>//.
- by move: Hmx =>/[swap] ->; rewrite ltnNge leq_addl.
by move=>Hxm; move: (ltn_trans Hxm Hmx); rewrite ltnNge leq_addl.
Qed.

(*Hint Resolve tsubst_1 tsubst_2.*)

Lemma tsubst_3 t x t' n k :
  tlift n (tsubst x t' t) (x + k) =
  tsubst x (tlift n t' k) (tlift n t (x + k.+1)).
Proof.
elim: t=>//=; first 1 last.
- by move=>t ->.
- by move=>t1 -> t2 ->.
- by move=>t1 -> t2 ->.
move=>m; case/boolP: (x + k.+1 <= m)=>Hxm.
- move: (contra (@ltn_addl m x k.+1)); rewrite addnC -leqNgt Hxm => /(_ erefl).
  case: cmpE=>//= Hxm1 _.
  - rewrite -ltnS (ltn_predK Hxm1) -ltnS -addnS ltnS Hxm.
    case: cmpE.
    - by move=>Hxm0; move: (ltn_trans Hxm0 Hxm1); rewrite ltnNge leq_addl.
    - by move: Hxm1 =>/[swap] <-; rewrite ltnNge leq_addl.
    move=>Hnm; rewrite -!subn1 addnBA //.
    by rewrite -ltn_predL (ltn_predK Hxm1).
  by move: Hxm; rewrite Hxm1 leqNgt addnS ltnS leq_addr.
rewrite -ltnNge addnS ltnS in Hxm.
case: cmpE=>/= Hmx.
- by rewrite leqNgt (ltn_addr k Hmx).
- by rewrite -tlift_2.
by rewrite leqNgt (ltn_predK Hmx) Hxm.
Qed.

Lemma tsubst_4 t x t' y u' :
  tsubst (x + y) u' (tsubst x t' t) =
  tsubst x (tsubst y u' t') (tsubst (x + y.+1) u' t).
Proof.
elim: t=>//=; first 1 last.
- by move=>t ->.
- by move=>t1 -> t2 ->.
- by move=>t1 -> t2 ->.
move=>m; rewrite addnS; case: cmpE=>Hmx /=; case: cmpE=>Hmxy /=.
- case: cmpE=>/=.
  - by move=>_; case: cmpE Hmx.
  - by move: Hmxy=>/[swap]->; rewrite ltnNge leqnSn.
  by move/ltn_trans=>/(_ _ Hmxy); rewrite ltnNge leqnSn.
- by move: Hmx; rewrite Hmxy ltnNge leq_addr.
- by move: (ltn_trans Hmxy Hmx); rewrite ltnNge leq_addr.
- by rewrite Hmx cmpxx tsubst_2.
- move: Hmxy; rewrite -addnS Hmx -{1}(addn0 x) => /eqP.
  by rewrite eqn_add2l.
- by move: Hmxy; rewrite -addnS Hmx ltnNge leq_addr.
- move: Hmxy; rewrite (ltn_predK Hmx)=>Hmxy.
  case: cmpE=>/=.
  - by move=>_; case: cmpE Hmx.
  - by move: Hmxy=>/[swap]->; rewrite ltnn.
  by move/leq_trans=>/(_ _ Hmxy); rewrite ltnNge leqnSn.
- move/eqP: Hmxy; rewrite -(eqn_add2r 1) !addn1 (ltn_predK Hmx) =>/eqP->/=.
  by rewrite cmpxx tsubst_1 //= add0n leq_addr.
move: Hmxy; rewrite -(ltn_add2r 1) !addn1 (ltn_predK Hmx).
case: cmpE=>//= Hxmy _; case: cmpE=>//.
- by rewrite (ltn_predK Hmx) leqNgt Hmx.
move/eqP; rewrite -(eqn_add2r 1) !addn1 (ltn_predK Hmx) =>/eqP Em.
by move: Hxmy; rewrite {1}Em ltnS ltnNge leq_addr.
Qed.

(* Terms where all variables are < n *)

Fixpoint cterm (n : nat) (t : term) : bool :=
  match t with
  | Tvar i => i < n
  | Tzero => true
  | Tsucc u => cterm n u
  | Tplus u v => cterm n u && cterm n v
  | Tmult u v => cterm n u && cterm n v
  end.

Lemma cterm_1 t : {homo cterm^~ t : m n / m <= n >-> m ==> n}.
Proof.
move=>m n Hmn; elim: t=>//=.
- move=>k; apply/implyP=>Hk.
  by apply/leq_trans/Hmn.
- by move=>t Ht u Hu; apply: imply_pair.
by move=>t Ht u Hu; apply: imply_pair.
Qed.

Lemma cterm_2 n t k : cterm n t -> tlift k t n = t.
Proof.
elim: t=>//=.
- by move=>m Ht; rewrite leqNgt Ht.
- by move=>t IHt Ht; rewrite IHt.
- by move=>t IHt u IHu /andP [Ht Hu]; rewrite IHt // IHu.
by move=>t IHt u IHu /andP [Ht Hu]; rewrite IHt // IHu.
Qed.

Lemma cterm_3 n t t' j : n <= j -> cterm n t -> tsubst j t' t = t.
Proof.
move=>Hnj Ht.
move: (cterm_2 _ _ j Ht)=>{2}<-.
move: (cterm_2 _ _ j.+1 Ht)=>{1}<-.
by apply: tsubst_1; rewrite Hnj /= leq_addl.
Qed.

Lemma cterm_4 n t t' :
  cterm n.+1 t -> cterm 0 t' ->
  cterm n (tsubst n t' t).
Proof.
move=>/[swap] H'; elim: t=>//=.
- move=>m; rewrite ltnS leqNgt; case: cmpE=>//= {m}_ _.
  elim: t' H'=>//=.
  - move=>t IHt u IHu /andP [Ht Hu].
    by rewrite IHt //= IHu.
  move=>t IHt u IHu /andP [Ht Hu].
  by rewrite IHt //= IHu.
- move=>t IHt u IHu /andP [Ht Hu].
  by rewrite IHt //= IHu.
move=>t IHt u IHu /andP [Ht Hu].
by rewrite IHt //= IHu.
Qed.

(*
Inductive cterm n : term -> Prop :=
  | cterm_var i : i < n -> cterm n (Tvar i)
  | cterm_zero : cterm n Tzero
  | cterm_succ u : cterm n u -> cterm n (Tsucc u)
  | cterm_plus u v : cterm n u -> cterm n v -> cterm n (Tplus u v)
  | cterm_mult u v : cterm n u -> cterm n v -> cterm n (Tmult u v).

(*Hint Constructors cterm.*)

Lemma cterm_1 n n' t : n <= n' -> cterm n t -> cterm n' t.
Proof.
move=>Hn; elim: t.
- move=>m Ht; case: {-1}_ / Ht (erefl (Tvar m))=>// i Hi _.
  by apply/cterm_var/leq_trans/Hn.
- move=>Ht; case: {-1}_ / Ht (erefl Tzero)=>// _.
  by apply: cterm_zero.
- move=>t IHt Ht; case: {-1}_ / Ht (erefl (Tsucc t))=>// u Hu [Eu].
  rewrite -{u}Eu in Hu *.
  by apply/cterm_succ/IHt.
- move=>t IHt u IHu Ht; case: {-1}_ / Ht (erefl (Tplus t u))=>// v w Hv Hw [Ev Ew].
  rewrite -{v}Ev in Hv *; rewrite -{w}Ew in Hw *.
  by apply: cterm_plus; [apply: IHt| apply: IHu].
move=>t IHt u IHu Ht; case: {-1}_ / Ht (erefl (Tmult t u))=>// v w Hv Hw [Ev Ew].
rewrite -{v}Ev in Hv *; rewrite -{w}Ew in Hw *.
by apply: cterm_mult; [apply: IHt| apply: IHu].
Qed.

Lemma cterm_2 n t k : cterm n t -> tlift k t n = t.
Proof.
elim: t=>//=.
- move=>m Ht; case: {-1}_ / Ht (erefl (Tvar m))=>// i Hi [{m}->].
  by rewrite leqNgt Hi.
- move=>t IHt Ht; case: {-1}_ / Ht (erefl (Tsucc t))=>// u Hu [Eu].
  rewrite -{u}Eu in Hu *.
  by rewrite IHt.
- move=>t IHt u IHu Ht; case: {-1}_ / Ht (erefl (Tplus t u))=>// v w Hv Hw [Ev Ew].
  rewrite -{v}Ev in Hv *; rewrite -{w}Ew in Hw *.
  by rewrite IHt // IHu.
move=>t IHt u IHu Ht; case: {-1}_ / Ht (erefl (Tmult t u))=>// v w Hv Hw [Ev Ew].
rewrite -{v}Ev in Hv *; rewrite -{w}Ew in Hw *.
by rewrite IHt // IHu.
Qed.

Lemma cterm_3 n t t' j : n <= j -> cterm n t -> tsubst j t' t = t.
Proof.
move=>Hnj Ht.
move: (cterm_2 _ _ j Ht)=>{2}<-.
move: (cterm_2 _ _ j.+1 Ht)=>{1}<-.
by apply: tsubst_1; rewrite Hnj /= leq_addl.
Qed.

Lemma cterm_4 n t t' :
  cterm n.+1 t -> cterm 0 t' ->
  cterm n (tsubst n t' t).
Proof.
move=>/[swap] H'; elim: t=>/=.
- move=>m Ht; case: {-1}_ / Ht (erefl (Tvar m))=>// i Hi [{m}->].
  move: Hi; rewrite ltnS leqNgt; case: cmpE=>//= Hi _.
  - by apply: cterm_var.
  elim: {i Hi}t' H'=>/=.
  - by move=>m Ht; case: {-1}_ / Ht (erefl (Tvar m)).
  - by move=>_; apply: cterm_zero.
  - move=>t IHt Ht; case: {-1}_ / Ht (erefl (Tsucc t))=>// u Hu [Eu].
    rewrite -{u}Eu in Hu.
    by apply/cterm_succ/IHt.
  - move=>t IHt u IHu Ht; case: {-1}_ / Ht (erefl (Tplus t u))=>// v w Hv Hw [Ev Ew].
    rewrite -{v}Ev in Hv; rewrite -{w}Ew in Hw.
    by apply/cterm_plus; [apply: IHt | apply: IHu].
  move=>t IHt u IHu Ht; case: {-1}_ / Ht (erefl (Tmult t u))=>// v w Hv Hw [Ev Ew].
  rewrite -{v}Ev in Hv; rewrite -{w}Ew in Hw.
  by apply/cterm_mult; [apply: IHt | apply: IHu].
- by move=>_; apply: cterm_zero.
- move=>t IHt Ht; case: {-1}_ / Ht (erefl (Tsucc t))=>// u Hu [Eu].
  rewrite -{u}Eu in Hu.
  by apply/cterm_succ/IHt.
- move=>t IHt u IHu Ht; case: {-1}_ / Ht (erefl (Tplus t u))=>// v w Hv Hw [Ev Ew].
  rewrite -{v}Ev in Hv; rewrite -{w}Ew in Hw.
  by apply/cterm_plus; [apply: IHt | apply: IHu].
move=>t IHt u IHu Ht; case: {-1}_ / Ht (erefl (Tmult t u))=>// v w Hv Hw [Ev Ew].
rewrite -{v}Ev in Hv; rewrite -{w}Ew in Hw.
by apply/cterm_mult; [apply: IHt | apply: IHu].
Qed.
*)
(* Formulas of Heyting Arithmetic. *)

Inductive formula : Type :=
  | Fequal of term & term
  | Ffalse
  | Fand of formula & formula
  | For of formula & formula
  | Fimplies of formula & formula
  | Fexists of formula
  | Fforall of formula.

Fixpoint eqformula (f1 f2 : formula) : bool :=
  match f1, f2 with
  | Fequal t1 u1, Fequal t2 u2 => (t1 == t2) && (u1 == u2)
  | Ffalse, Ffalse => true
  | Fand f1 g1, Fand f2 g2 => eqformula f1 f2 && eqformula g1 g2
  | For f1 g1, For f2 g2 => eqformula f1 f2 && eqformula g1 g2
  | Fimplies f1 g1, Fimplies f2 g2 => eqformula f1 f2 && eqformula g1 g2
  | Fexists f1, Fexists f2 => eqformula f1 f2
  | Fforall f1, Fforall f2 => eqformula f1 f2
  | _, _ => false
  end.

Lemma eqformulaP : Equality.axiom eqformula.
Proof.
elim=>[t1 u1||f1 IHf g1 IHg|f1 IHf g1 IHg|f1 IHf g1 IHg|f1 IHf|f1 IHf];
case=>[t2 u2||f2 g2|f2 g2|f2 g2|f2|f2] /=;
try by constructor.
- by apply: (iffP andP)=>[[/eqP->/eqP->]|[->->]].
- by apply: (iffP andP)=>[[/IHf->/IHg->]|[<-<-]] //; split; [apply/IHf | apply/IHg].
- by apply: (iffP andP)=>[[/IHf->/IHg->]|[<-<-]] //; split; [apply/IHf | apply/IHg].
- by apply: (iffP andP)=>[[/IHf->/IHg->]|[<-<-]] //; split; [apply/IHf | apply/IHg].
- by apply: (iffP (IHf f2))=>[->|[->]].
by apply: (iffP (IHf f2))=>[->|[->]].
Qed.

Canonical formula_eqMixin := EqMixin eqformulaP.
Canonical formula_eqType := Eval hnf in EqType formula formula_eqMixin.




(*
Delimit Scope pa_scope with pa.
Bind Scope pa_scope with term.
Bind Scope pa_scope with formula.
Arguments Tsucc _%pa.
Arguments Tplus _%pa _%pa.
Arguments Tmult _%pa _%pa.
Arguments Fequal _%pa _%pa.
Arguments Fand _%pa _%pa.
Arguments For _%pa _%pa.
Arguments Fimplies _%pa _%pa.
Arguments Fexists _%pa.
Arguments Fforall _%pa.
*)

(* Formula lifting: add n to all variables of t which are >= k *)

Fixpoint flift (n : nat) (f : formula) (k : nat) : formula :=
  match f with
  | Fequal u v => Fequal (tlift n u k) (tlift n v k)
  | Ffalse => Ffalse
  | Fand g h => Fand (flift n g k) (flift n h k)
  | For g h => For (flift n g k) (flift n h k)
  | Fimplies g h => Fimplies (flift n g k) (flift n h k)
  | Fexists g => Fexists (flift n g k.+1)
  | Fforall g => Fforall (flift n g k.+1)
  end.

(* Add Lift *)
Lemma flift_add f n n' k k' :
  k <= k' <= k + n ->
  flift n' (flift n f k) k' = flift (n' + n) f k.
Proof.
elim: f k k'=>//=.
- by move=>u v k k' Hk; rewrite !tlift_1.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg k k' Hl; rewrite IHg.
by move=>g IHg k k' Hl; rewrite IHg.
Qed.

(* Commute Lift *)
Lemma flift_commute f n n' k k' :
  k' <= k ->
  flift n' (flift n f k) k' = flift n (flift n' f k') (n' + k).
Proof.
elim: f k k'=>//=.
- by move=>u v k k' Hk; rewrite tlift_2 // (tlift_2 v).
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg k k' Hl; rewrite IHg // addnS.
by move=>g IHg k k' Hl; rewrite IHg // addnS.
Qed.

(* Formula substitution: replace variable x by (tlift x t' 0) in A *)

Fixpoint fsubst (x : nat) (t' : term) (f : formula) :=
  match f with
  | Fequal u v => Fequal (tsubst x t' u) (tsubst x t' v)
  | Ffalse => Ffalse
  | Fand g h => Fand (fsubst x t' g) (fsubst x t' h)
  | For g h => For (fsubst x t' g) (fsubst x t' h)
  | Fimplies g h => Fimplies (fsubst x t' g) (fsubst x t' h)
  | Fexists g => Fexists (fsubst x.+1 t' g)
  | Fforall g => Fforall (fsubst x.+1 t' g)
  end.

(* Subst too low *)
Lemma subst_below f x t' n k :
  k <= x <= k + n ->
  fsubst x t' (flift n.+1 f k) = flift n f k.
Proof.
elim: f k x=>//=.
- by move=>u v k x Hk; rewrite !tsubst_1.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg k k' Hl; rewrite IHg.
by move=>g IHg k k' Hl; rewrite IHg.
Qed.

(* Lift in Subst <-> Subst in Lift *)
Lemma flift_fsubst_commute f x t' n k :
  k <= x ->
  flift n (fsubst x t' f) k = fsubst (n + x) t' (flift n f k).
Proof.
elim: f k x=>//=.
- by move=>u v k k' Hk; rewrite tsubst_2 // (tsubst_2 v).
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg h IHh k k' Hk; rewrite IHg // IHh.
- by move=>g IHg k k' Hl; rewrite IHg // addnS.
by move=>g IHg k k' Hl; rewrite IHg // addnS.
Qed.

(* Commute "Double Lift" and Subst *)
Lemma dble_flift_fsubst_commute f x t' n k :
  flift n (fsubst x t' f) (x + k) =
  fsubst x (tlift n t' k) (flift n f (x + k.+1)).
Proof.
elim: f x=>//=.
- by move=>u v x; rewrite !tsubst_3.
- by move=>g IHg h IHh x; rewrite IHg IHh.
- by move=>g IHg h IHh x; rewrite IHg IHh.
- by move=>g IHg h IHh x; rewrite IHg IHh.
- by move=>u IHu x; rewrite IHu addSn.
by move=>u IHu x; rewrite IHu addSn.
Qed.

(* Add Subst *)
Lemma fsubst_add f x t' y u' :
  fsubst (x + y) u' (fsubst x t' f) =
  fsubst x (tsubst y u' t') (fsubst (x + y.+1) u' f).
Proof.
elim: f x=>//=.
- by move=>u v x; rewrite !tsubst_4.
- by move=>g IHg h IHh x; rewrite IHg IHh.
- by move=>g IHg h IHh x; rewrite IHg IHh.
- by move=>g IHg h IHh x; rewrite IHg IHh.
- by move=>u IHu x; rewrite -!addSn IHu.
by move=>u IHu x; rewrite -!addSn IHu.
Qed.

(* Formulas where all variables are < n *)

Fixpoint cformula (n : nat) (f : formula) : bool :=
  match f with
  | Fequal u v => cterm n u && cterm n v
  | Ffalse => true
  | Fand g h => cformula n g && cformula n h
  | For g h => cformula n g && cformula n h
  | Fimplies g h => cformula n g && cformula n h
  | Fexists g => cformula n.+1 g
  | Fforall g => cformula n.+1 g
  end.

(*
Inductive cformula n : formula -> Prop :=
  | cformula_equal u v :
      cterm n u -> cterm n v -> cformula n (Fequal u v)
  | cformula_false : cformula n Ffalse
  | cformula_and g h :
      cformula n g -> cformula n h -> cformula n (Fand g h)
  | cformula_or g h :
      cformula n g -> cformula n h -> cformula n (For g h)
  | cformula_implies g h :
      cformula n g -> cformula n h -> cformula n (Fimplies g h)
  | cformula_exists g :
      cformula n.+1 g -> cformula n (Fexists g)
  | cformula_forall g :
      cformula n.+1 g -> cformula n (Fforall g).

(*Hint Constructors cformula.*)

Inductive subterm t : formula -> Prop :=
  | subterm_equal t' : subterm t (Fequal t t')
  | subterm_and g h t' :
      subterm t g -> subterm t' h -> subterm t (Fand g h)
  | subterm_or g h t' :
      subterm t g -> subterm t' h -> subterm t (For g h)
  | subterm_implies g h t' :
      subterm t g -> cformula t' h -> subterm t (Fimplies g h)
  | subterm_exists g :
      subterm t g -> subterm t (Fexists g)
  | subterm_forall g :
      subterm t g -> subterm t (Fforall g).

(*Hint Constructors subterm.*)
*)

(* Monotonous cformula *)
Lemma cformula_monotonous f : {homo cformula^~ f : m n / m <= n >-> m ==> n}.
Proof.
elim: f=>//=.
- by move=>t u m n Hmn; apply: imply_pair; apply: cterm_1.
- by move=>t IHt u IHu m n Hmn; apply: imply_pair; [apply: IHt | apply: IHu].
- by move=>t IHt u IHu m n Hmn; apply: imply_pair; [apply: IHt | apply: IHu].
- by move=>t IHt u IHu m n Hmn; apply: imply_pair; [apply: IHt | apply: IHu].
- by move=>g IHg m n Hmn; apply: IHg; rewrite ltnS.
by move=>g IHg m n Hmn; apply: IHg; rewrite ltnS.
Qed.

(* Lift above *)
Lemma lift_above n f k : cformula n f -> flift k f n = f.
Proof.
elim: f n=>//=.
- by move=>t u n /andP [Ht Hu]; rewrite !cterm_2.
- by move=>t IHt u IHu n /andP [Ht Hu]; rewrite IHt // IHu.
- by move=>t IHt u IHu n /andP [Ht Hu]; rewrite IHt // IHu.
- by move=>t IHt u IHu n /andP [Ht Hu]; rewrite IHt // IHu.
- by move=>t IHt n Ht; rewrite IHt.
by move=>t IHt n Ht; rewrite IHt.
Qed.

(* Subst above *)
Lemma subst_above n f t' j :
  n <= j -> cformula n f -> fsubst j t' f = f.
Proof.
elim: f n j=>//=.
- by move=>t u n j Hnj /andP [Ht Hu]; rewrite !(cterm_3 n).
- by move=>t IHt u IHu n j Hnj /andP [Ht Hu]; rewrite (IHt n) // (IHu n).
- by move=>t IHt u IHu n j Hnj /andP [Ht Hu]; rewrite (IHt n) // (IHu n).
- by move=>t IHt u IHu n j Hnj /andP [Ht Hu]; rewrite (IHt n) // (IHu n).
- by move=>t IHt n j Hnj Ht; rewrite (IHt n.+1).
by move=>t IHt n j Hnj Ht; rewrite (IHt n.+1).
Qed.

(* Subst closed term *)
Lemma subst_closed_term n f t' :
  cformula n.+1 f -> cterm 0 t' ->
  cformula n (fsubst n t' f).
Proof.
elim: f n=>//=.
- by move=>t u n /andP [Ht Hu] H'; apply/andP; split; apply: cterm_4.
- by move=>t IHt u IHu n /andP [Ht Hu] H'; rewrite IHt // IHu.
- by move=>t IHt u IHu n /andP [Ht Hu] H'; rewrite IHt // IHu.
- by move=>t IHt u IHu n /andP [Ht Hu] H'; rewrite IHt // IHu.
- by move=>t IHt n Ht H'; rewrite IHt.
by move=>t IHt n Ht H'; rewrite IHt.
Qed.

(* Notations *)

Reserved Notation "# n" (at level 2).

Notation "A /\ B" := (Fand A B) : pa_scope.
Notation "A \/ B" := (For A B) : pa_scope.
Notation "A ==> B" := (Fimplies A B) : pa_scope.
Notation "x = y" := (Fequal x y) : pa_scope.
Notation "x + y" := (Tplus x y) : pa_scope.
Notation "x * y" := (Tmult x y) : pa_scope.
Notation "# n" := (Tvar n) (at level 2) : pa_scope.

Open Scope pa_scope.

(* Contexts (or environments), represented as list of formulas. *)

Definition context := seq formula.

(* Lifting an context *)

Definition clift n g k := map (fun f => flift n f k) g.

(* Rules of (intuitionistic) Natural Deduction.

   This predicate is denoted with the symbol ":-", which
   is easier to type than "⊢".
   After this symbol, Coq expect a formula, hence uses the formula
   notations, for instance /\ is Fand instead of Coq own conjunction).
*)

Reserved Notation "g :- A" (at level 87, no associativity).

Inductive rule : context -> formula -> Prop :=
  | Rax g a : a \in g -> g :- a
  | Rfalse_e g a : g :- Ffalse -> g :- a
  | Rand_i g b c : g :- b -> g :- c -> g :- b /\ c
  | Rand_e1 g b c : g :- b /\ c -> g :- b
  | Rand_e2 g b c : g :- b /\ c -> g :- c
  | Ror_i1 g b c : g :- b -> g :- b \/ c
  | Ror_i2 g b c : g :- c -> g :- b \/ c
  | Ror_e g a b c : g :- b \/ c -> (b::g) :- a -> (c::g) :- a -> g :- a
  | Rimpl_i g b c : (b::g) :- c -> g :- b ==> c
  | Rimpl_e g b c : g :- b ==> c -> g :- b -> g :- c
  | Rforall_i g b : (clift 1 g 0) :- b -> g :- (Fforall b)
  | Rforall_e g b t : g :- (Fforall b) -> g :- (fsubst 0 t b)
  | Rexists_i g b t : g :- (fsubst 0 t b) -> g :- (Fexists b)
  | Rexists_e g a b : g :- (Fexists b) -> (b::clift 1 g 0) :- (flift 1 a 0) -> g :- a

where "g :- A" := (rule g A).

(* Auxiliary connectives and admissible rules *)

(* TODO: define the following formulas *)
Definition Ftrue := Ffalse ==> Ffalse.
Definition Fnot A := A ==> Ffalse.
Definition Fiff A B := ((A ==> B) /\ (B ==> A)).

Notation "~ A" := (Fnot A) : pa_scope.
Notation "A <==> B" := (Fiff A B) (at level 4) : pa_scope.

(* n repeated forall *)
Fixpoint nFforall n f :=
  if n is m.+1 then Fforall (nFforall m f) else f.

Lemma Rtrue_i g : g :- Ftrue.
Proof.
rewrite /Ftrue; apply/Rimpl_i/Rax.
by rewrite inE eqxx.
Qed.

Lemma Rnot_i g a : (a::g) :- Ffalse -> g :- ~a.
Proof.
by rewrite /Fnot; apply: Rimpl_i.
Qed.

Lemma Rnot_e g a : g :- a -> g :- ~ a -> g :- Ffalse.
Proof.
rewrite /Fnot=>H1 H2.
by apply/Rimpl_e/H1.
Qed.

Lemma Riff_i g a b :
  (a::g) :- b -> (b::g) :- a -> g :- a <==> b.
Proof.
rewrite /Fiff => Hab Hba.
by apply: Rand_i; apply: Rimpl_i.
Qed.

Lemma nFforall_1 n x t a :
  fsubst x t (nFforall n a) = nFforall n (fsubst (n + x) t a).
Proof.
elim: n=>[|n IH] /= in x *; first by rewrite add0n.
by rewrite (IH x.+1) addnS addSn.
Qed.

(* Peano axioms *)

Inductive PeanoAx : formula -> Prop :=
  | pa_refl : PeanoAx (nFforall 1 (#0 = #0))
  | pa_sym : PeanoAx (nFforall 2 ((#1 = #0) ==> (#0 = #1)))
  | pa_trans : PeanoAx (nFforall 3 (#2 = #1 /\ (#1 = #0) ==> (#2 = #0)))
  | pa_compat_s : PeanoAx (nFforall 2 ((#1 = #0) ==> (Tsucc #1 = Tsucc #0)))
  | pa_compat_plus_l : PeanoAx (nFforall 3 ((#2 = #1) ==> (#2 + #0 = #1 + #0)))
  | pa_compat_plus_r : PeanoAx (nFforall 3 ((#1 = #0) ==> (#2 + #1 = #2 + #0)))
  | pa_compat_mult_l : PeanoAx (nFforall 3 ((#2 = #1) ==> (#2 * #0 = #1 * #0)))
  | pa_compat_mult_r : PeanoAx (nFforall 3 ((#1 = #0) ==> (#2 * #1 = #2 * #0)))
  | pa_plus_O : PeanoAx (nFforall 1 (Tzero + #0 = #0))
  | pa_plus_S : PeanoAx (nFforall 2 (Tsucc #1 + #0 = Tsucc (#1 + #0)))
  | pa_mult_O : PeanoAx (nFforall 1 (Tzero * #0 = Tzero))
  | pa_mult_S : PeanoAx (nFforall 2 (Tsucc #1 * #0 = (#1 * #0) + #0))
  | pa_inj : PeanoAx (nFforall 2 ((Tsucc #1 = Tsucc #0) ==> (#1 = #0)))
  | pa_discr : PeanoAx (nFforall 1 (~ Tzero = Tsucc #0))
  | pa_ind a n : cformula n.+1 a ->
    PeanoAx ((nFforall n (fsubst 0 Tzero a /\
                         Fforall (a ==> fsubst 0 (Tsucc #0) (flift 1 a 1))) ==> Fforall a
                        )).

(* Definition of theorems over Heyting Arithmetic.

   NB: we should normally restrict theorems to closed terms only,
   but this doesn't really matter here, since we'll only prove that
   False isn't a theorem. *)

Definition Thm T : Prop :=
  exists2 axioms, {in axioms, forall a, PeanoAx a} & (axioms :- T).

(* Example of theorem *)

Lemma HA_n_Sn : Thm (Fforall (~ #0 = Tsucc #0)).
Proof.
set Gamma := [:: (nFforall 0 (
                      fsubst 0 Tzero (~ #0 = Tsucc #0) /\
                      Fforall ((~ #0 = Tsucc #0)
                               ==> fsubst 0 (Tsucc #0) (flift 1 (~ #0 = Tsucc #0) 1)))
                               ==> Fforall (~ #0 = Tsucc #0))
                ; nFforall 2 ((Tsucc #1 = Tsucc #0) ==> (#1 = #0))
                ; nFforall 1 (~ (Tzero = Tsucc #0))].
exists Gamma.
- (* (forall A, In A axioms -> PeanoAx A) *)
  rewrite /Gamma =>a; rewrite !inE; case/or3P=>/eqP=>{a}->.
  - by apply: pa_ind.
  - by apply: pa_inj.
  by apply: pa_discr.
(* (axioms:-T) *)
(* hyp is to make the proof terms more readable. This is just implication
elimination in the induction principle*)
set hyp := nFforall 0 (fsubst 0 Tzero (~ #0 = Tsucc #0) /\
                       Fforall ((~ #0 = Tsucc #0)
                                  ==> fsubst 0 (Tsucc #0)
                                             (flift 1 (~ #0 = Tsucc #0) 1))).
apply: (Rimpl_e _ hyp); rewrite /hyp /Gamma.
- by apply: Rax; rewrite !inE eqxx.
apply: Rand_i=>/=.
- rewrite (_ : ((Tzero = Tsucc Tzero) ==> Ffalse) = (fsubst 0 Tzero (~ Tzero = Tsucc #0))) //.
  by apply/Rforall_e/Rax; rewrite !inE eqxx orbT.
apply: Rforall_i=>/=; apply/Rimpl_i/Rimpl_i/(Rimpl_e _ (# 0 = Tsucc # 0)).
- by apply: Rax; rewrite !inE eqxx.
apply: (Rimpl_e _ (Tsucc # 0 = Tsucc (Tsucc # 0))).
- rewrite (_ : ((Tsucc # 0 = Tsucc (Tsucc # 0)) ==> (# 0 = Tsucc # 0))
             = (fsubst 0 (Tsucc #0) ((Tsucc #1 = Tsucc #0) ==> (# 1 = # 0)))) //.
  apply: Rforall_e.
  rewrite (_ : ((Fforall ((Tsucc # 1 = Tsucc # 0) ==> (# 1 = # 0)))
             = fsubst 0 #0 (Fforall ((Tsucc # 1 = Tsucc # 0) ==> (# 1 = # 0))))) //.
  apply: Rforall_e.
  by apply: Rax; rewrite !inE eqxx.
by apply: Rax; rewrite !inE eqxx.
Qed.

(* Interpretation of terms, using a valuation for variables *)

Definition valuation := seq nat.

Fixpoint tinterp (v : valuation) (t : term) : nat :=
  match t with
    | Tvar j => nth 0 v j
    | Tzero => 0
    | Tsucc t => (tinterp v t).+1
    | Tplus t t' => tinterp v t + tinterp v t'
    | Tmult t t' => tinterp v t * tinterp v t'
  end.

Lemma tinterp_1 t v0 v1 v2 :
  tinterp (v0++v1++v2) (tlift (size v1) t (size v0)) =
  tinterp (v0++v2) t.
Proof.
elim: t=>//=; first 1 last.
- by move=>t ->.
- by move=>t -> u ->.
- by move=>t -> u ->.
move=>n; rewrite !nth_cat.
case: (leqP (size v0) n)=>[H|->] //.
move: (leq_add (leq0n (size v1)) H).
rewrite ltnNge add0n=>-> /=.
by rewrite ltnNge -addnBA // leq_addr /= addnC -addnBA // subnn addn0.
Qed.

Lemma tinterp_2 t' t v1 v2 :
  tinterp (v1 ++ v2) (tsubst (size v1) t' t) =
  tinterp (v1 ++ tinterp v2 t' :: v2) t.
Proof.
elim: t=>//=; first 1 last.
- by move=>t ->.
- by move=>t -> u ->.
- by move=>t -> u ->.
move=>n; rewrite nth_cat; case: cmpE=>/= Hs.
- rewrite nth_cat ltnNge -ltnS (ltn_predK Hs) Hs /=.
  rewrite -subn_gt0 in Hs.
  by rewrite -predn_sub -{2}(ltn_predK Hs).
- by move: (tinterp_1 t' [::] v1 v2); rewrite Hs subnn.
by rewrite nth_cat Hs.
Qed.

(* Interpretation of formulas *)

Fixpoint finterp v a : Prop :=
  match a with
    | Fequal t t' => tinterp v t = tinterp v t'
    | Ffalse => False
    | Fand b c => finterp v b /\ finterp v c
    | For b c => finterp v b \/ finterp v c
    | Fimplies b c => finterp v b -> finterp v c
    | Fexists b => exists n, finterp (n::v) b
    | Fforall b => forall n, finterp (n::v) b
  end.

Lemma finterp_1 : forall A v0 v1 v2,
  finterp (v0 ++ v1 ++ v2) (flift (length v1) A (length v0)) <->
  finterp (v0 ++ v2) A.
Proof.
  intros. revert v0 v1 v2. induction A;  intros.
  - simpl. split;intros.
    + simpl in H. repeat(rewrite tinterp_1 in H). assumption.
    + repeat (rewrite tinterp_1). assumption.
  - auto. simpl. split;auto.
  - split; intro; destruct H; apply (IHA1 v0 v1 v2) in H;
    split ; try apply (IHA2 v0 v1 v2) in H0 ; assumption.
  - split ; intro; destruct H.
    +left. simpl in H. apply (IHA1 v0 v1 v2) in H. assumption.
    +right. apply (IHA2 v0 v1 v2) in H. assumption.
    +left. simpl in H. apply (IHA1 v0 v1 v2) in H. assumption.
    +right. apply (IHA2 v0 v1 v2) in H. assumption.

  - split;intro; simpl in H; simpl; intro; apply (IHA1 v0 v1 v2) in H0;
    apply H in H0; apply (IHA2 v0 v1 v2) in H0; assumption.

  - split; intro; simpl; simpl in H; destruct H; exists x; rewrite app_comm_cons;
    apply (IHA (x::v0)v1 v2); assumption.
  -split; intro; simpl;simpl in H; intro; rewrite app_comm_cons;
   apply (IHA (n::v0)v1 v2); apply H.

Qed.

Lemma finterp_2 : forall t' A v1 v2,
  finterp (v1 ++ v2) (fsubst (length v1) t' A) <->
  finterp (v1 ++ (tinterp v2 t') :: v2) A.
Proof.
  intros; revert v1 v2; induction A; intros;
  simpl; split; intuition;
  repeat rewrite <- tinterp_2; auto;
  repeat rewrite tinterp_2; auto;
  try apply (@IHA1 v1 v2) in H0; intuition;
  try apply (@IHA2 v1 v2) in H1; intuition;
  try apply (@IHA2 v1 v2) in H0; intuition;
  try (destruct H; exists x; rewrite app_comm_cons; apply (@IHA (x::v1) v2)); auto;
  try (apply (@IHA (n::v1) v2); rewrite <- app_comm_cons); intuition.
Qed.

(* Interpretation of contexts *)

Definition cinterp v g := forall A, In A g -> finterp v A.

(* Soundess of deduction rules *)

Lemma f_to_c : forall v A g , finterp v A ->  cinterp v g -> cinterp v (A :: g).
Proof.
  intros. unfold cinterp in *. intros.
  simpl in H1. destruct H1; try rewrite <- H1; auto.
Qed.




(*this lemma is useful for cinterp_1 and soundness_rules*)
Lemma soundness_misc : forall g A m n, In A (clift m g n) ->
                                        exists B, A = flift m B n /\ In B g.
Proof.
  intros. induction g; simpl in H; try contradiction.
  simpl in H. destruct H.
  - exists a. split; try simpl; auto.
           - assert (exists B : formula, A = flift m B n /\ In B g). auto.
             destruct H0 as [B H0]. exists B. destruct H0.
             split;try apply in_cons; auto.
Qed.


(*added by Alice*)
(*I hope this is true*)
Lemma cinterp_1 : forall g v0 v1 v2,
                    cinterp (v0 ++ v2) g ->
                    cinterp (v0 ++ v1 ++ v2) (clift (length v1) g (length v0)) .

Proof.
  intro. induction g.
  - intros. simpl. unfold cinterp. intros. simpl in H0. contradiction.
  -  unfold cinterp.  simpl. intros. destruct H0.
     + rewrite <- H0. apply finterp_1. apply H. auto.
     + assert (exists B, A = flift (length v1) B (length v0)/\ In B g).
       apply soundness_misc. auto.
       destruct H1 as [B H1]. destruct H1. rewrite H1. apply finterp_1.
       apply H. auto.
Qed.


Lemma finterp_misc_0  : forall v t B,  finterp v (fsubst 0 t B) ->
                                     (exists n, finterp (n::v) B).
Proof.
  intros.  exists (tinterp v t). assert (finterp(nil ++ (tinterp v t) :: v) B).
  apply finterp_2. simpl. auto. simpl in H0. auto.
Qed.


Lemma finterp_misc_1 : forall v t B ,  (forall n, finterp (n::v) B)
                                       -> finterp v (fsubst 0 t B).
Proof.
  intros.  assert (finterp(nil ++  v) (fsubst 0 t B));
    try apply finterp_2; simpl; auto.
Qed.

Lemma finterp_misc_2 :  forall v A,
  (exists n, (finterp (n :: v) (flift 1 A 0))) ->
  finterp v A.
Proof.
  intros.
   destruct H as [n H].
    assert (finterp ((nil : list nat) ++ (n :: nil) ++ v)
                    (flift (length (n :: nil)) A (length (nil : list nat))) <->
            finterp ((nil : list nat) ++ v) A).
  - apply finterp_1.
  - simpl in H0. apply H0. auto.
Qed.


Lemma finterp_misc_3 :  forall n v A,
                          finterp v A ->
                          (finterp (n :: v) (flift 1 A 0)).
Proof.
  intros. assert (finterp ((nil : list nat) ++ (n :: nil) ++ v)
                          (flift (length (n :: nil)) A
                                 (length (nil : list nat))) <->
                  finterp ((nil : list nat) ++ v) A).
  - apply finterp_1.
  - simpl in H0. apply H0. auto.
Qed.


(*Particular case of cinterp1*)
Lemma cinterp_forall : forall g n v , cinterp v g ->
                                      cinterp (n :: v) (clift 1 g 0).
Proof.

  intros. assert (cinterp ( nil ++(n::nil) ++ v)
                          (clift (length (n::nil))  g (length (nil:list nat)))).
  - apply (cinterp_1  g nil (n::nil) v). simpl. auto.
  - simpl in H0. auto.
Qed.



Lemma soundness_rules : forall g A, g:-A ->
  forall v, cinterp v g -> finterp v A.
Proof.
  (*intros. apply yeswecan with g. auto.*)
  intro;intro;intro.  induction H.
  - intros. apply H0. auto.
  - intros. cut False. auto. simpl in IHrule. apply IHrule with v. auto.
  - simpl. split; auto.
  - simpl in IHrule. apply IHrule.
  - simpl in IHrule. apply IHrule.
  - simpl. left. auto.
  - simpl. right. auto.
  - intros. simpl in IHrule1. assert (finterp v B \/ finterp v C); auto.
    destruct H3.
    + apply IHrule2. apply f_to_c; auto.
    + apply IHrule3. apply f_to_c; auto.
  - simpl. intros. apply IHrule. apply f_to_c; auto.
  - simpl in IHrule1. auto.
  - simpl. intros. apply IHrule. apply cinterp_forall. auto.
  - intros. simpl in IHrule. simpl.
    apply finterp_misc_1 .  auto.
  - intros. simpl. apply finterp_misc_0 with t . auto.
  - intros. unfold cinterp in IHrule2. simpl in *. apply finterp_misc_2.
    assert (exists n, finterp (n::v) B). auto.
    destruct H2. exists x.
    apply IHrule2 . intros. destruct H3.
    + rewrite <- H3. auto.
    + assert (exists C, A0 = flift 1 C 0 /\ In C g). apply soundness_misc. auto.
      destruct H4 as [C H4]. destruct H4.
      assert (finterp v C). auto. rewrite H4.
      apply finterp_misc_3. auto.
Qed.


(* n-times repeated Tsucc *)
Fixpoint nTsucc n :=
  match n with
    | 0 => (fun t => t)
    | S m => (fun t => Tsucc (nTsucc m t))
  end.


Lemma tinterp_nTsucc : forall n v, tinterp v (nTsucc n Tzero) = n.
Proof.
  induction n; simpl; auto; try apply f_equal.
Qed.

Lemma nTsucc_eq_n : forall A n v, finterp (n::v) A <->
  finterp v (fsubst 0 (nTsucc n Tzero) A).
Proof.
  intros; destruct n; split; intro; simpl;
  try apply finterp_2 with (v1 := nil);
  try apply finterp_2 with (v1 := nil) in H; auto; simpl.
  rewrite <- (@tinterp_nTsucc n v) in H; auto.
  rewrite (@tinterp_nTsucc (S n) v) in H; simpl; auto.
Qed.

Lemma destruct_list_end : forall n (v1: list nat), length v1 = S n
  -> exists n0 v0, length v0 = n /\ v1 = v0 ++ n0::nil.
Proof.
  intros.
  assert (v1 <> nil).
  intuition; rewrite <- length_zero_iff_nil in H0; auto.
  apply (@exists_last nat v1) in H0; destruct H0; destruct s.
  exists x0; exists x; split; auto.
  assert (S n = length x + 1).
  rewrite <- H; rewrite e; apply app_length.
  auto.
Qed.

Lemma finterp_nFforall : forall A n v2, finterp v2 (nFforall n A)
  <-> forall v1, length v1 = n -> finterp (v1 ++ v2) A.
Proof.
  induction n; split; intros; simpl; simpl in H.
  - apply length_zero_iff_nil in H0; try now rewrite H0.
  - now apply H with (v1 := nil).
  - apply (destruct_list_end n v1) in H0.
    destruct H0; destruct H0; destruct H0.
    rewrite H1; rewrite <- app_assoc.
    apply IHn with (v2 := (x :: nil) ++ v2); auto;
    simpl; apply H.
  - intro. apply IHn; intros.
    assert (v1 ++ n0 :: v2 = (v1 ++ (n0 :: nil)) ++ v2).
    rewrite <- app_assoc; now simpl.
    rewrite H1; apply H; rewrite app_length; simpl; auto.
Qed.

Lemma nTsucc_at_n0 : forall A n n0 v, finterp (n0::v) (nFforall n A)
  <-> finterp v (nFforall n (fsubst n (nTsucc n0 Tzero) A)).
Proof.
  split; intro;
  try rewrite -> (finterp_nFforall A n (n0::v)) in H;
  try rewrite -> (finterp_nFforall (fsubst n (nTsucc n0 Tzero) A) n v);
  try rewrite -> (finterp_nFforall A n (n0::v));
  try rewrite -> (finterp_nFforall (fsubst n (nTsucc n0 Tzero) A) n v) in H;
  intros; assert (finterp_subst := (finterp_2 (nTsucc n0 Tzero) A v1 v));
  rewrite H0 in finterp_subst; rewrite tinterp_nTsucc in finterp_subst;
  try (rewrite finterp_subst; now apply H).
  try (rewrite <- finterp_subst; now apply H).
Qed.

(*
Lemma tlift_unit: forall t n, tlift 0 t n = t.
Proof.
  induction t; intros;
  repeat (simpl; auto; break);
  simpl; try f_equal;
  try apply IHt; try apply IHt1; try apply IHt2.
Qed.
*)

Notation flift_add := flift_1.
Notation flift_commute := flift_2.
Notation subst_below := fsubst_1.
Notation flift_fsubst_commute := fsubst_2.
Notation dble_flift_fsubst_commute := fsubst_3.
Notation fsubst_add := fsubst_4.
Notation cformula_monotonous := cformula_1.
Notation lift_above := cformula_2.
Notation subst_above := cformula_3.
Notation subst_closed_term := cformula_4.
Notation finterp_lift := finterp_1.
Notation finterp_subst := finterp_2.

Lemma soundness_axioms : forall A, PeanoAx A -> forall v, finterp v A.
Proof.
  intros; induction H; simpl; auto.
  generalize dependent A; induction n.
  - simpl; intros; inversion H0.
    assert (forall n : nat,
    finterp (n :: v) A ->
    finterp ((S n) :: v) A).
    + intros; apply H2 in H3.
      apply finterp_subst with (v1 := nil) in H3.
      simpl in H3; apply finterp_lift with (v0 := S n0 :: nil) (v1 := n0 :: nil) (v2 := v) in H3.
      simpl in H3. auto.
    + apply nat_ind with (n:= n) in H3; auto.
      apply finterp_subst with (v1 := nil) in H1; now simpl in H1.
  - intros; simpl; intro.
    assert (cformula (S n) (fsubst (S n) (nTsucc n0 Tzero) A)).
    + apply subst_closed_term with (n := S n); auto.
      induction n0; auto; simpl; now constructor.
    + apply IHn in H0; rewrite nTsucc_at_n0; simpl.
      assert (fsub_add := fsubst_add A 0 Tzero n (nTsucc n0 Tzero)).
      simpl in fsub_add.
      rewrite <- fsub_add in H0.
      assert (fsub_lift := flift_fsubst_commute A (S n) (nTsucc n0 Tzero) 1 1).
      simpl in fsub_lift.
      rewrite fsub_lift in H0.
      assert (fsub_sub := fsubst_add (flift 1 A 1) 0 (Tsucc # 0) (S n) (nTsucc n0 Tzero)).
      simpl in fsub_sub.
      rewrite <- fsub_sub in H0.
      auto; destruct n. auto.
Qed.




Theorem soundness : forall A, Thm A -> forall v, finterp v A.
Proof.
  intro; intro. repeat (destruct H). intro. apply soundness_rules with x. auto.
  unfold cinterp. intros. apply soundness_axioms. auto.
Qed.

Theorem coherence : ~Thm Ffalse.
Proof.
  intro.
  assert (finterp nil  Ffalse).
  apply soundness; auto.
  simpl in H0; auto.
Qed.

