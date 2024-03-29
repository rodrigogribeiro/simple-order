(** A very simple example for a decidable order theory
    on coq proof assistant. 

    All code is from Castéran & Bertot Coq'Art's Book (with
    some small modifications).

    First, a specification of a theory of decidable orders
    as a module type signature. *)

Require Import Relations.

Module Type DEC_ORDER.
   Parameter A : Type.
   Parameter le : A -> A -> Prop.
   Parameter lt : A -> A -> Prop.

   Axiom ordered : order A le.
   Axiom lt_le_weak : forall a b : A, lt a b -> le a b.
   Axiom lt_diff : forall a b : A, lt a b -> a <> b.
   Axiom le_lt_or_eq : forall a b : A, le a b -> lt a b \/ a = b.

   Parameter lt_eq_lt_dec : 
      forall a b : A, {lt a b} + {a = b} + {lt b a}.
End DEC_ORDER.

