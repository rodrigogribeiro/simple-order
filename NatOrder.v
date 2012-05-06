(** Finally we can implement the lexicographic order
    over natural numbers *)

Require Import Relations Arith_base.
Require Import DecOrder MoreDecOrder LexOrder.

Module NatOrder : DEC_ORDER 
                  with Definition A := nat
                  with Definition le := Peano.le
                  with Definition lt := Peano.lt.

  Definition A := nat.
  Definition le := Peano.le.
  Definition lt := Peano.lt.

  Theorem ordered : order A le.
  Proof.
    split ; unfold A, le, reflexive, transitive, antisymmetric ; eauto with arith.
  Qed.

  Theorem lt_le_weak : forall a b : A, lt a b -> le a b.
  Proof.
    unfold A ; exact lt_le_weak.
  Qed.

 Theorem lt_diff : forall a b:A, lt a b -> a <> b.
  Proof.
   unfold A, lt, le in |- *; intros a b H e. 
   rewrite e in H.
   case (lt_irrefl b H).
  Qed.

  Theorem le_lt_or_eq : forall a b:A, le a b -> lt a b \/ a = b.
  Proof.
   unfold A, le, lt in |- *.  
   exact le_lt_or_eq.
  Qed.
  
  Definition lt_eq_lt_dec : forall a b:A, {lt a b} + {a = b} + {lt b a} :=
    lt_eq_lt_dec.
End NatOrder.

(** Simple module definition for the lexicographic order over pairs of nat *)

Module NatNat := Lexico NatOrder NatOrder.