Require Import List.
Import ListNotations.

Axiom listupdate : forall {A}, list A -> nat -> A -> list A.

Definition elem {A} (a : A) (l : list A) (n : nat) :=
    nth_error l n = Some a.

Axiom elemEmpty : forall {A} (a : A) n, elem a [] n -> False.

Lemma listupdate_com :
    forall A (T : list A) i s j s',
    i <> j ->
    listupdate (listupdate T i s) j s' = listupdate (listupdate T j s') i s.
Admitted.

Lemma listupdate_others : 
    forall A (x : A) T i s j,
    i <> j ->
    elem x (listupdate T i s) j <->  elem x T j.
Admitted.