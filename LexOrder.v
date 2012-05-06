(** Implementation of a functor for lexicographic
    decidable orders *)

Require Import Relations.
Require Import DecOrder MoreDecOrder.

Module Lexico (D1 : DEC_ORDER) (D2 : DEC_ORDER) <: DEC_ORDER 
                                                   with Definition A := (D1.A * D2.A)%type.
  Open Scope type_scope.
  Module M1 := More_Dec_Orders D1.
  Module M2 := More_Dec_Orders D2.

  Definition A := D1.A * D2.A.

 Definition le (a b:A) : Prop :=
   let (a1, a2) := a in
   let (b1, b2) := b in D1.lt a1 b1 \/ a1 = b1 /\ D2.le a2 b2.
 
 Definition lt (a b:A) : Prop :=
   let (a1, a2) := a in
   let (b1, b2) := b in D1.lt a1 b1 \/ a1 = b1 /\ D2.lt a2 b2.


 Theorem ordered : order A le.
 Proof.
  split.
  unfold reflexive in |- *; intros.
  unfold le in |- *; case x. 
  right.
  split; [ trivial | apply M2.le_refl; auto ].
  unfold le, transitive in |- *. 
  simple destruct x; simple destruct y; simple destruct z. 
  simple destruct 1; intro H1.
  simple destruct 1.
  left.
  eapply M1.lt_trans.
  eexact H1.
  assumption.
  simple destruct 1.
  simple destruct 1.
  auto.
  simple destruct 1.
  intro. 
  case H1; intros e H3; rewrite e; auto.
  case H1; intros e H3; rewrite e; auto.
  simple destruct 1.
  simple destruct 1.
  right.
  split; try auto. 
  eapply M2.le_trans; eauto.
  unfold antisymmetric, A, le in |- *.
  simple destruct x; simple destruct y.
  simple destruct 1; simple destruct 2.
  intro.
  absurd (D1.lt a1 a1).   
  apply M1.lt_irreflexive. 
  eapply M1.lt_trans; eauto.
  simple destruct 1; intros e H3.
  rewrite e in H0.
  case (M1.lt_irreflexive a H0).
  case H0; intros e H3.
  rewrite e; intro H2.
  case (M1.lt_irreflexive a1 H2).
  simple destruct 1; intros e H3; rewrite e.  
  case (M2.le_antisym a2 a0).
  auto.
  case H0; auto.
  auto.
 Qed.

 Theorem lt_le_weak : forall a b:A, lt a b -> le a b.
 Proof.
  unfold A, lt, le in |- *; intros a b; case a; case b. 
  simple destruct 1; intros; auto.
  right; case H0; split; auto.
  apply D2.lt_le_weak; trivial.   
 Qed.


 Theorem lt_diff : forall a b:A, lt a b -> a <> b.
 Proof.
  unfold A, lt, le in |- *; intros a b; case a; case b. 
  simple destruct 1.
  intro H0; red in |- *; injection 1.
  intros e1 e2; rewrite e2 in H0.
  case (M1.lt_irreflexive a0 H0).
  simple destruct 1.
  simple destruct 1.   
  intro H2; red in |- *; injection 1.
  intro e; rewrite e in H2; case (M2.lt_irreflexive _ H2).
 Qed.

 Theorem le_lt_or_eq : forall a b:A, le a b -> lt a b \/ a = b.
 Proof.
  unfold A, lt, le in |- *; intros a b; case a; case b. 
  simple destruct 1; auto.
  simple destruct 1.
  simple destruct 1.
  intro H2; case (D2.le_lt_or_eq _ _ H2).
  auto.
  simple destruct 1. 
  auto. 
 Qed.


 Definition lt_eq_lt_dec : forall a b:A, {lt a b} + {a = b} + {lt b a}.
  Proof.
   unfold A, lt in |- *; intros.
   case a; case b.
   intros a0 a1 a2 a3.  
   case (D1.lt_eq_lt_dec a0 a2).
   simple destruct 1.
   right.
   auto.
   simple destruct 1.
   case (D2.lt_eq_lt_dec a1 a3).
   simple destruct 1.
   right.
   auto.
   simple destruct 1.
   left; right; trivial.
   left; left; auto.
   left.
   left; auto.
  Defined.
End Lexico.