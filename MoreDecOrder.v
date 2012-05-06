(** Extending a simple specification of a decidable order *)

Require Import Relations DecOrder.

Module Type MORE_DEC_ORDERS.
  Parameter A : Type.
  Parameter le : A -> A -> Prop.
  Parameter lt : A -> A -> Prop.

  Axiom le_trans : transitive A le.
  Axiom le_refl : reflexive A le.
  Axiom le_antisym : antisymmetric A le.

  Axiom lt_irreflexive : forall a : A, ~ lt a a.
  Axiom lt_trans : transitive A lt.
  Axiom lt_not_le : forall a b : A, lt a b -> ~ le b a.
  Axiom le_not_lt : forall a b : A, le a b -> ~ lt b a.
  Axiom lt_intro : forall a b : A, le a b -> a <> b -> lt a b.

  Parameter le_lt_dec : forall a b : A, {le a b} + {lt b a}.
  Parameter le_lt_eq_dec : forall a b : A, le a b -> {lt a b} + {a = b}.

End MORE_DEC_ORDERS.

(** Simple functor to map an DEC_ORDER to MORE_DEC_ORDERS *)

Module More_Dec_Orders (P : DEC_ORDER) : MORE_DEC_ORDERS 
                                         with Definition A := P.A
                                         with Definition le := P.le
                                         with Definition lt := P.lt.
  Definition A := P.A.
  Definition le := P.le.
  Definition lt := P.lt.

  Ltac p := destruct P.ordered ; assumption.

  Theorem le_trans : transitive A le.
  Proof. p. Qed.

  Theorem le_refl : reflexive A le.
  Proof. p. Qed.

  Theorem le_antisym : antisymmetric A le.
  Proof. p. Qed.

  Theorem lt_intro : forall a b : A, le a b -> a <> b -> lt a b.
  Proof.
    intros a b H diff ; destruct (P.le_lt_or_eq a b H) ; tauto.
  Qed.
  
  Theorem lt_irreflexive : forall a : A, ~lt a a.
  Proof.
    intros a H ; destruct (P.lt_diff _ _ H) ; trivial.
  Qed.

  Theorem lt_not_le : forall a b : A, lt a b -> ~ le b a.
  Proof.
      intros a b H H0.
      absurd (a = b).
      apply P.lt_diff; trivial.
      apply le_antisym; auto; apply P.lt_le_weak; assumption.
  Qed.

  Theorem le_not_lt : forall a b : A, le a b -> ~ lt b a.
  Proof.
    intros a b H H0 ; apply (lt_not_le b a) ; auto.
  Qed.

  Theorem lt_trans : transitive A lt.
  Proof.    
   unfold A, transitive in |- *.
   intros x y z H H0.
   apply (lt_intro x z).
   apply le_trans with y; apply P.lt_le_weak; assumption.
   intro e; rewrite e in H.
   absurd (y = z).
   intro e'; rewrite e' in H. 
   apply (lt_irreflexive _ H). 
   apply le_antisym; apply P.lt_le_weak; trivial.
  Qed.

  Definition le_lt_dec : forall a b:A, {le a b} + {lt b a}.
   intros a b; case (P.lt_eq_lt_dec a b).
   intro d; case d; auto.  
   left; apply P.lt_le_weak; trivial. 
   simple induction 1; left; apply le_refl.
   right; trivial.
  Defined.

  Definition le_lt_eq_dec : forall a b:A, le a b -> {lt a b} + {a = b}.
   intros a b H.
   destruct (P.lt_eq_lt_dec a b).
   trivial. 
   destruct (le_not_lt a b H) ; auto.
  Defined.
End More_Dec_Orders.