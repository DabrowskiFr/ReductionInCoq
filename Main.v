Require Import List.
Require Import Coq.Program.Equality.
Require Import Misc Basic.

Import ListNotations.

Open Scope type_scope.

(** Simple notations *)

Definition initial {A} (l :list A) : option A := nth_error l (length l - 1).
Definition final {A} (l : list A) : option A := nth_error l 0.
Definition source {A B C} (t : A * B * C ) := match t with (s, _, _) => s end.
Definition target {A B C} (t : A * B * C) := match t with (_, _, s) => s end.

(** * Definitions *)

Module Reduction (M : Basic).

Import M.

(** ** Syntax *)

Declare Custom Entry stmt.
Declare Scope stmt_scope.

Inductive stmt : Set :=
|   Term : stmt
|   Store : var -> expr -> stmt 
|   Read :  var -> glob -> stmt
|   Write : var -> glob -> stmt 
|   Seq : stmt -> stmt -> stmt
|   If : bexpr -> stmt -> stmt -> stmt
|   While : bexpr -> stmt -> stmt
|   Enter : stmt
|   Exit : stmt.

Notation "'while' x 'do' y 'end'" :=
         (While x y)
            (in custom stmt at level 89, x at level 99, y at level 99) : com_scope.


(** A program is a list of statements, one per thread *)

Definition program := list stmt.

(** ** Semantics *)

(** An event is either 
    - a memory event [Sh]
    - an acquire event [En]
    - a release event [Ex]
    - a internal event *)

Inductive action := Sh | En | Ex | τ.

Definition event := nat * action.

(** A thread state is a pair [(s, ρ)] where [s] is a statement and [σ] is 
    its local memory. A global state, of type [state], is a tuple [(T, (σ, μ))] 
    where [T] is a list of thread states, [σ] is the shared memory and [μ] 
    records the position of the thread executing its critical section if exists.
    We introduce a few notation to improve readability *)

Definition thread := stmt * store.

Definition state := list thread * heap * option nat.

Definition threads (s : state) := match s with (l, σ, μ) => l end.

Definition memory (s : state) := match s with (l, σ, μ) => σ end.

Definition mutex (s : state) := match s with (l, σ, μ) => μ end.

(** The individual behavior of threads is described by the relation [step] *)

(** [step i ((s,ρ), (σ, μ), a, (s',ρ'), (σ', μ'))] means that thread i moves from 
    local state [(s, ρ), (σ, μ)] to state [(s', ρ'), (σ', μ')] performing an action [a].
*)

Reserved Notation "A — C → B" (at level 80, no associativity). 

(* Definition Tr := A * E * A*)

Inductive step : (thread * heap * option nat) ->  event ->
                    (thread * heap * option nat) -> Prop :=
|   stepStore : forall x e ρ σ μ i n, eval e ρ = n -> 
        ((Store x e, ρ), σ, μ) —(i, τ)→ ((Term, update ρ x n), σ, μ)
|   stepRead : forall x Y ρ σ μ i,
        ((Read x Y, ρ), σ, μ) —(i, Sh)→ ((Term, update ρ x (read σ Y)), σ, μ)
|   stepWrite : forall x Y ρ σ μ i,
        ((Write x Y, ρ), σ, μ) —(i, Sh)→ ((Term, ρ), write σ Y (load ρ x), μ)
|   stepTerm : forall s ρ σ μ i,
        ((Seq Term s, ρ), σ, μ) —(i, τ)→ ((s, ρ), σ, μ)
|   stepIf1 : forall b s1 s2 ρ σ μ i,
        let s := if evalb b ρ then s1 else s2 in  
            ((If b s1 s2, ρ), σ, μ) —(i, τ)→ ((s, ρ), σ, μ)
|   stepWhile : forall b s ρ σ μ i,
        let s' := if evalb b ρ then Seq s (While b s) else Term in
            ((While b s, ρ), σ, μ) —(i, τ)→ ((s', ρ), σ, μ)
|   stepEnter : forall ρ σ i,
        ((Enter, ρ), σ, None) —(i, En)→ ((Term, ρ), σ, Some i)
|   stepExit : forall ρ σ i,
        ((Exit, ρ), σ, Some i) —(i, Ex)→ ((Term, ρ), σ, None)
where "A — C → B" := (step A C B).

(** The global behavior is defined by the relation [transition] 
    [transition (st1, (i,a), st2)] means that the system evolves from
    state [st1] to state [st2] by performing an individual step on 
    thread [i] with action [a]. We use the usual notion of context to reduce
    under sequences. *)

Inductive ctx : Set := CEmpty : ctx | CSeq : ctx -> stmt -> ctx.

Fixpoint mkstmt (c : ctx) (s : stmt) : stmt :=
    match c with CEmpty => s | CSeq c s' => Seq (mkstmt c s) s' end. 

Notation "C ⟨ S ⟩" := (mkstmt C S) (at level 81).

Reserved Notation "A ⇒ C ⇒ B" (at level 80, no associativity). 

Definition Tr (A B : Set) := A * B * A.

Inductive transition : Tr state event -> Prop :=
    transition_ : forall T1 σ1 μ1 i a c s' ρ' σ2 μ2, 
    (exists ρ s, elem (c ⟨ s ⟩, ρ) T1 i 
                    /\ ((s, ρ), σ1, μ1) —(i,a)→ ((s', ρ'), σ2, μ2)) ->
    transition ((T1, σ1, μ1), (i,a), (listupdate T1 i (c ⟨ s' ⟩, ρ'), σ2, μ2))
    where "A ⇒ C ⇒ B" := (transition A C B).
(* 
Definition transition (t : state * (nat * action) * state) : Prop:=
    match t with ((T1,(σ1, μ1)), (i, a), (T2, (σ2, μ2))) =>
        exists c s ρ s' ρ', elem (c ⟨ s ⟩, ρ) T1 i  
        /\ T2 = listupdate T1 i (c ⟨ s' ⟩, ρ')
        /\ step i ((s, ρ), (σ1, μ1)) a ((s', ρ'), (σ2, μ2))
    end.
*)
(* st1, st2 -> (T, σ, μ )?*)
(* Definition transition (t : state * (nat * action) * state) : Prop:=
    match t with (st1, (i, a), st2) =>
        exists c s ρ s' ρ', elem (c ⟨ s ⟩, ρ) (fst st1) i  
        /\ fst st2 = listupdate (fst st1) i (c ⟨ s' ⟩, ρ')
        /\ step i ((s, ρ), snd st1) a ((s', ρ'), snd st2)
    end.
*)
(** Finally, a (partial) execution of a program p is simply a sequence
    of transition such that 
    - the first state is the initial state of the program and
    - the source of each transition is the target of its predecessor (if exists) *)

Definition init (p : program) : state :=
    (map (fun s => (s, store_init)) p, heap_init, None).

Definition path := list (Tr state event).

Inductive execution (p : program) : path -> Prop :=
|   execution_empty : execution p []
|   execution_single : 
        forall t, transition t -> source t = init p -> execution p [t]
|   execution_next : 
        forall t' t e, execution p (t :: e) -> transition t' -> 
                        target t = source t' -> execution p (t' :: t :: e).


(*Lemma execution_prefix_closed : forall p t e, execution p (t :: e) -> execution p e.
Admitted.*)

(** *   Movers *)
(**     - An action [a] is a left mover in [p], if every transition labelled 
        by [a] left commutes with any transition performed by another thread
        - An action [a] is a left mover, if every transition labelled by [a] left 
        commutes with any transition performed by another thread *)

Definition leftMover (p : program) (a : action) :=
    forall st1 i st2 j b st3 e, i <> j -> 
        execution p ((st2, (i, a), st3) :: (st1, (j, b), st2) :: e) -> 
        exists st2',
        execution p ((st2', (j, b), st3) :: (st1, (i, a), st2') :: e ).

Definition rightMover (p : program) (a : action) :=
    forall st1 i st2 j b st3 e, i <> j -> 
        execution p ((st2, (j, b), st3) :: (st1, (i, a), st2) :: e) -> 
        exists st2',
        execution p ((st2', (i, a), st3) :: (st1, (j, b), st2') :: e ).

Definition valid (t : Tr state event) : Prop :=
    match t with ((T, σ, μ), (i, a), st) => a = Sh -> μ = Some i end.
                
Definition wellbehaved (p : program) :=
    forall e t, execution p e ->  In t e -> valid t.
        
(** *** Results *)

Lemma leftMoverTau : forall p, leftMover p τ.
Proof.
    intros p [[T1 σ1] μ1] i [[T2 σ2] μ2] j b [[T3 σ3] μ3] e HNEq HExec.
    pose (st1 := (T1, σ1, μ1)).
    pose (st2 := (T2, σ2, μ2)).
    pose (st3 := (T3, σ3, μ3)).
    inversion HExec as [ | | ? ? ? HExec2 Hti Hb Hc] ; subst.
    assert (transition (st1, (j, b), st2)) as Htj
        by now inversion HExec2 as [ | ? Hd He | ? ? ? HExec3 Hd He Hf].
    inversion Hti as [? ? ? ? ? ci si' ρi' ? ? [ρi [si [Hc Hd]]]]; subst.
    inversion Htj as [? ? ? ? ? cj sj' ρj' ? ? [ρj [sj [He Hf]]]]; subst.
    pose (st2' := (listupdate T1 i (mkstmt ci si', ρi'), σ1, μ1)).
    assert (σ3 = σ2 /\ μ3 = μ2) as [? ?] by (inversion Hd; auto); subst.
    assert (transition (st1, (i, τ), st2')).
    {
        constructor.
        exists ρi, si; simpl. 
        split.
        +   apply listupdate_others with j (cj ⟨ sj' ⟩, ρj'); congruence.
        +   inversion Hd; subst; constructor.
            reflexivity.
    }
    assert (transition (st2', (j,b), st3)).
    {
        unfold st2', st3.
        rewrite listupdate_com by auto.
        constructor.
        exists ρj, sj; simpl. 
        split; [apply listupdate_others; auto | assumption].
    }
    exists st2'.
    constructor 3.
    -   inversion HExec2; now constructor.
    -   assumption.
    -   reflexivity.
Qed.

Lemma rightMoverTau : forall p, rightMover p τ.
Proof.
    intros p [[T1 σ1] μ1] i [[T2 σ2] μ2] j b [[T3 σ3] μ3] e HNEq HExec.
    pose (st1 := (T1, σ1, μ1)).
    pose (st2 := (T2, σ2, μ2)).
    pose (st3 := (T3, σ3, μ3)).
    inversion HExec as [ | | ? ? ? HExec2 Htj Hb Hc] ; subst.
    assert (transition (st1, (i, τ), st2)) as Hti
        by now inversion HExec2 as [ | ? Hd He | ? ? ? HExec3 Hd He Hf].
    inversion Hti as [? ? ? ? ? ci si' ρi' ? ? [ρi [si [Hc Hd]]]]; subst.
    inversion Htj as [? ? ? ? ? cj sj' ρj' ? ? [ρj [sj [He Hf]]]]; subst.
    pose (st2' := (listupdate T1 j (mkstmt cj sj', ρj'), σ3, μ3)).
    assert (σ2 = σ1 /\ μ2 = μ1) as [? ?] by (inversion Hd; auto); subst.
    assert (transition (st1, (j, b), st2')).
    {
        constructor.
        exists ρj, sj; simpl.
        split; [eapply listupdate_others; eauto | assumption].
    }
    assert (transition (st2', (i,τ), st3)).
    {
        unfold st2', st3.
        rewrite listupdate_com by auto.
        constructor.
        exists ρi, si; simpl. 
        split; [apply listupdate_others; auto | ].
        inversion Hd; subst; constructor. 
        reflexivity.
    }
    exists st2'.
    constructor 3.
    - inversion HExec2 as [ | ? Hi Hj| ]; now constructor.
    - assumption.  
    - reflexivity.
Qed.

Lemma rightMoverEnter : forall p, rightMover p En.
Proof.  
    intros p [[T1 σ1] μ1] i [[T2 σ2] μ2] j b [[T3 σ3] μ3] e HNEq HExec.
    pose (st1 := (T1, σ1, μ1)).
    pose (st2 := (T2, σ2, μ2)).
    pose (st3 := (T3, σ3, μ3)).
    inversion HExec as [ | | ? ? ? HExec2 Htj Hb Hc] ; subst.
    assert (transition (st1, (i, En), st2)) as Hti
        by now inversion HExec2 as [ | ? Hd He | ? ? ? HExec3 Hd He Hf].
    inversion Hti as [? ? ? ? ? ci si' ρi' ? ? [ρi [si [Hc Hd]]]]; subst.
    inversion Htj as [? ? ? ? ? cj sj' ρj' ? ? [ρj [sj [He Hf]]]]; subst.
    pose (st2' := (listupdate T1 j (mkstmt cj sj', ρj'), σ3, @None nat)).
    assert (μ1 = None /\ σ1 = σ2 /\ μ2 = Some i) as [? [? ?]]
        by (inversion Hd; auto); subst.
    assert (transition (st1, (j, b), st2')).
    {
        constructor.
        exists ρj, sj; simpl.
        split; [eapply listupdate_others; eauto | ].
        destruct b.
        *   inversion Hf; subst; constructor.
        *   assert (Some i = None) by inversion Hf; discriminate.
        *   contradict HNEq.
            inversion Hf; subst; reflexivity.
        *   inversion Hf; subst; constructor.
            reflexivity.
    }
    assert (transition (st2', (i, En), st3)).
    {
        unfold st2', st3.
        rewrite listupdate_com by auto.
        constructor.
        exists ρi, si; simpl. 
        split.
        +   apply listupdate_others; auto.
        +  
            assert (μ3 = Some i).
            {   destruct b.
                *   inversion Hf; subst; reflexivity.      
                *   exfalso; now auto.  
                *   contradict HNEq.
                    inversion Hf; subst;reflexivity.
                *   inversion Hf; subst; reflexivity.
            }
            subst.
            inversion Hd; subst.
            apply stepEnter.
    }
    exists st2'.
    constructor 3.
    - inversion HExec2 as [ | ? Hi Hj| ]; now constructor.
    - assumption.
    - reflexivity. 
Qed.

Lemma leftMoverExit : forall p, leftMover p Ex.
Proof.  
    intros p [[T1 σ1] μ1] i [[T2 σ2] μ2] j b [[T3 σ3] μ3] e HNEq HExec.
    pose (st1 := (T1, σ1, μ1)).
    pose (st2 := (T2, σ2, μ2)).
    pose (st3 := (T3, σ3, μ3)).
    inversion HExec as [ | | ? ? ? HExec2 Hti Hb Hc] ; subst.
    assert (transition (st1, (j, b), st2)) as Htj
        by now inversion HExec2 as [ | ? Hd He | ? ? ? HExec3 Hd He Hf].
    inversion Hti as [? ? ? ? ? ci si' ρi' ? ? [ρi [si [Hc Hd]]]]; subst.
    inversion Htj as [? ? ? ? ? cj sj' ρj' ? ? [ρj [sj [He Hf]]]]; subst.
    pose (st2' := (listupdate T1 i (mkstmt ci si', ρi'), σ1, @None nat)).
    assert (μ2 = Some i /\ σ2 = σ3 /\ μ3 = None ) as [? [? ?]]
        by (inversion Hd; auto); subst.
    assert (transition (st1, (i, Ex), st2')).
    {
        constructor.
        exists ρi, si; simpl.
        split; [eapply listupdate_others; eauto | ].
        destruct b.
        *   replace μ1 with (Some i) in * by now inversion Hf.
            inversion Hd; subst; constructor.
        *   contradict HNEq.
            inversion Hf; subst; reflexivity.
        *   assert (Some i = None) by inversion Hf; discriminate.
        *   inversion Hf; subst; assumption.
    }
    assert (transition (st2', (j,b), st3)).
    {
        unfold st2', st3.
        rewrite listupdate_com by auto.
        constructor.
        exists ρj, sj; simpl.
        split; [now apply listupdate_others | ].
        destruct b.
        +   inversion Hf; subst; constructor.
        +   contradict HNEq.
            inversion Hf; subst; reflexivity.
        +   assert (Some i = None) by inversion Hf.
            discriminate.
        +   replace σ1 with σ3 by now (inversion Hf; subst).
            inversion Hf; subst; constructor.
            reflexivity.
    }
    exists st2'.
    constructor 3.
    - inversion HExec2 as [ | ? Hi Hj| ]; now constructor.
    - assumption.
    - reflexivity.
Qed.

Lemma leftMoverSh : forall p, wellbehaved p -> leftMover p Sh.
Proof.
    intros p Hwell [[T1 σ1] μ1] i [[T2 σ2] μ2] j b [[T3 σ3] μ3] e HNEq HExec.
    pose (st1 := (T1, σ1, μ1)).
    pose (st2 := (T2, σ2, μ2)).
    pose (st3 := (T3, σ3, μ3)).
    inversion HExec as [ | | ? ? ? HExec2 Hti Hb Hc] ; subst.
    assert (transition (st1, (j, b), st2)) as Htj
        by now inversion HExec2 as [ | ? Hd He | ? ? ? HExec3 Hd He Hf].
    inversion Hti as [? ? ? ? ? ci si' ρi' ? ? [ρi [si [Hc Hd]]]]; subst.
    inversion Htj as [? ? ? ? ? cj sj' ρj' ? ? [ρj [sj [He Hf]]]]; subst.
    pose (st2' := (listupdate T1 i (mkstmt ci si', ρi'), σ3, μ3)).
    assert (valid (st1, (j, b), st2))
        by apply (Hwell _ _ HExec (in_cons _ _ (_ :: _) (in_eq _ _))).
    assert (valid (st2, (i, Sh), st3))
        by apply (Hwell _ _ HExec (in_eq _ _)).
    assert (μ2 = Some i /\ μ3 = Some i) as [? ?] by (inversion Hd; subst; auto); subst.
    assert (transition (st1, (i, Sh), st2')).
    {
        constructor.
        exists ρi, si; simpl.
        split; [eapply listupdate_others; eauto | ].
        destruct b.
        *   contradict HNEq.
            assert (μ1 = Some j) by now apply H.
            replace μ1 with (Some i) in * by now inversion Hf.
            congruence.
        *   contradict HNEq.   
            inversion Hf; subst; congruence.
        *   exfalso.
            inversion Hf; subst; discriminate.
        *   inversion Hf; subst; assumption. 
    }
    assert (transition (st2', (j, b), st3)).
    {
        unfold st2', st3.
        rewrite listupdate_com by auto.   
        constructor.
        exists ρj, sj; simpl.
        split; [now apply listupdate_others | ].
        destruct b.
        +   contradict HNEq.
            assert (μ1 = Some j) by auto; subst.
            inversion Hf; subst; reflexivity.
        +   contradict HNEq.
            inversion Hf; subst; reflexivity. 
        +   assert (Some i = None) by (inversion Hf; auto).
            discriminate.
        +   replace σ1 with σ2 by now (inversion Hf; subst).
            inversion Hf; subst; constructor.
            reflexivity.
    }   
    exists st2'.
    constructor 3.
    - inversion HExec2 as [ | ? Hi Hj| ]; now constructor.
    - assumption.
    - reflexivity.
Qed.

Lemma rightMoverSh : forall p, wellbehaved p -> rightMover p Sh.
Proof.
    intros p Hwell [[T1 σ1] μ1] i [[T2 σ2] μ2] j b [[T3 σ3] μ3] e HNEq HExec.
    pose (st1 := (T1, σ1, μ1)). 
    pose (st2 := (T2, σ2, μ2)).
    pose (st3 := (T3, σ3, μ3)).
    inversion HExec as [ | | ? ? ? HExec2 Htj Hb Hc] ; subst.
    assert (transition (st1, (i, Sh), st2)) as Hti
        by now inversion HExec2 as [ | ? Hd He | ? ? ? HExec3 Hd He Hf].
    inversion Hti as [? ? ? ? ? ci si' ρi' ? ? [ρi [si [Hc Hd]]]]; subst.
    inversion Htj as [? ? ? ? ? cj sj' ρj' ? ? [ρj [sj [He Hf]]]]; subst.
    pose (st2' := (listupdate T1 j (mkstmt cj sj', ρj'), σ1, μ3)).
    assert (valid (st1, (i, Sh), st2))
        by apply (Hwell _ _ HExec (in_cons _ _ (_ :: _) (in_eq _ _))).
    assert (valid (st2, (j, b), (st3)))
        by apply (Hwell _ _ HExec (in_eq _ _)).
    assert (μ1 = μ2) as ? by (inversion Hd; auto); subst.
    assert (transition (st1, (j, b), st2')).
    {
        constructor.
        exists ρj, sj; simpl.
        split; [eapply listupdate_others; eauto | ].
        unfold st1, st2 in H.
        assert (μ2 = Some i) by now apply H.
        destruct b.
        *   contradict HNEq.
            assert (μ2 = Some j) by auto.
            congruence.
        *   exfalso.
            assert (μ2 = None) by now inversion Hf.
            congruence.
        *   exfalso.
            assert (μ2 = Some j) by now inversion Hf.
            congruence.
        *   inversion Hf; subst;constructor.    
            reflexivity.
    }
    assert (transition (st2', (i, Sh), st3)).
    {
        unfold st2', st3.
        rewrite listupdate_com by auto.   
        constructor.
        exists ρi, si; simpl.
        split; [apply listupdate_others; auto | ].
        assert (μ2 = Some i) by now apply H.
        destruct b.
        +   contradict HNEq.
            assert (μ2 = Some j) by auto; subst.
            congruence.
        +   exfalso.
            assert (μ2 = None) by now inversion Hf.
            congruence.
        +   exfalso.
            assert (μ2 = Some j) by now inversion Hf.
            congruence.
        +   replace σ3 with σ2 by now (inversion Hf; subst).
            inversion Hd; subst; constructor.
    }   
    exists st2'.
    constructor 3.
    - inversion HExec2 as [ | ? Hi Hj| ]; now constructor.
    - assumption.
    - reflexivity.
Qed.        

(** * Atomicity *)

Definition atomic (e : path) :=
    forall k i a st1 st2, elem (st1, (i, a), st2) e k -> mutex st1 = Some i.

Theorem atomicity : forall (p : program), 
    wellbehaved p -> forall e, execution p e -> 
        exists e', execution p e' /\ atomic e' /\ final e' = final e.
Admitted.

End Reduction.


(*

Lemma initial_prop {A} (e e' : A) l l' : initial (e::l) = initial (e'::l').
Admitted.

Definition atomic (e : list (state * (nat * action) * state)) :=
    forall k T σ i j a T' σ' μ, 
    elem ((T, (σ, Some i)), (j, a), (T', (σ', μ))) e k -> i = j.

Lemma atomic_empty : atomic [].
Proof.
    intros k T σ i j a T' σ' μ H.
    apply elemEmpty in H.
    elim H.
Qed.

Lemma atomic_single : forall t, atomic [t].
Admitted.

Lemma execution_prefix : forall {t e}, execution (t::e) -> execution e.
Admitted.

Lemma wellbehaved_prefix : forall {t e}, wellbehaved (t::e) -> wellbehaved e.
Admitted.


(* execution [t] *)
Lemma execution_empty : execution [].
Proof.
    split; intros.
    -   elim (elemEmpty _ _ H).
    -   elim (elemEmpty _ _ H).
Qed.

Lemma execution_single : forall t, transition t -> execution [t].
Proof.  
    intros.
    split; intros.
    -   destruct k.
        +   unfold elem in H0; simpl in H0.
            injection H0; intros; subst. 
            assumption.
        +   unfold elem in H0; simpl in H0.
            destruct k; discriminate.
    -   unfold elem in H0; simpl in H0.
        destruct k; discriminate.
Qed.

(* definition inductive de l'exécution, necessite de définir le neme element (non, predicat) *)

Lemma execution_transition : 
    forall t' t e, 
    target t = source t' ->
    execution (t :: e) -> transition t' -> execution (t' :: t :: e).
Proof.
    intros t' t e HEq He Ht.
    split; intros.
    -   destruct k.
        +   unfold elem in H; simpl in H.
            injection H; intros; subst.
            assumption.
        +   unfold elem in H; simpl in H.
            destruct He.
            eapply H0; eauto.
    -   destruct k.
        unfold elem in H; simpl in H.
        unfold elem in H0; simpl in H0.
        injection H; injection H0; intros; subst.
        assumption.
        unfold elem in H; simpl in H.
        unfold elem in H0.
        destruct He.
        eapply H2.
        apply H.
        apply H0.
Qed.
                
Lemma atomic_same : forall st1 i a st2 b st3 e, 
(* execution + transition *)
    atomic ((st1, (i, a), st2) :: e) -> atomic ((st2, (i, b), st3) :: (st1, (i, a), st2) :: e).
Proof.
    intros [T1 [σ1 μ1]] i a [T2 [σ2 μ2]] b [T3 [σ3 μ3]] e Ha.
    unfold atomic in *.
    intros.
    destruct k.
    -   destruct μ2.
        +   unfold elem in H; simpl in H.
            injection H; intros; subst; clear H.
            assert (μ1 = None \/ μ1 = Some i0).
            {
                destruct a.
                destruct μ1. (*destruct a to know i0*)
                -   right.
                    f_equal.
                    generalize (Ha 0 T1 σ1 n j a T σ (Some i0) (refl_equal _)); intro Hb.
                    (* i0 *)
            }
            destruct μ1.
            * admit.
            * 

            generalize (Ha 0 T1 σ1 n i a T2 σ2 μ2 (refl_equal _)); intro Hb.
        +   unfold elem in H; simpl in H.
            injection H; intros; subst.
            discriminate.
    - 
    -   destruct μ1.
        + admit.
        +
        generalize (Ha 0 T1 σ1 n i a T2 σ2 μ2 (refl_equal _)); intro Hb.
            subst.
            unfold elem in H; simpl in H.
            injection H; intros; subst.
        injection H0; intros; subst; clear H0.
        assert (\mu1 = Some j).
        generalize (H 0 T1 σ1 i0 j a T σ (Some i0)); intro.
        
        generalize (H 0 T σ i0 j a T σ (Some i0)); intro.
        unfold elem in H1; simpl in H1.
        apply H1.
        repeat f_equal.
    -   unfold elem in H0; simpl in H0.
        apply H in H0.
        assumption. 
Qed.
        unfold elem in H0; simpl in H0.
        injection H0; intros; subst.
        destruct st1 as [T0 [σ0 μ0]].
        generalize (H 0 T0 σ0 j a T σ (Some i0)).
    destruct k.
    -   generalize 

    Lemma reduction : forall e, execution e -> wellbehaved e -> 
    exists e', execution e' /\
        initial e = initial e' /\ final e = final e' /\ atomic e'.
Proof.
    induction e as [ | t' e]. (* pas sur la sous liste, sur la taille *)
    -   intros.
        exists [].
        intuition.
        apply atomic_empty.
    -   intros.
        destruct e as [ | t e].
        +   exists [t'].
            intuition.
            apply atomic_single.
        + destruct (IHe (execution_prefix H) (wellbehaved_prefix H0)) 
            as [e' [Ha [Hb [Hc Hd]]]].
            unfold final in Hc.
            simpl in Hc.
            destruct e' as [ | t'' e']; [ discriminate |].
            injection Hc; intro; subst; clear Hc.
            assert (initial e = initial e') by admit; clear Hb.
            destruct t'' as [[st1 [i a]] st2].
            destruct t' as [[st2' [j b]] st3].
            assert (st2 = st2').
            {
                destruct H.
                apply (H2 0 _ _ (refl_equal _) (refl_equal _)).
            }
            replace st2' with st2 in * by auto.

            destruct a.
            *   generalize (rightMoverSh _ H H0); intro.
                unfold rightMover in H3.

        +   assert (e = []) by admit; subst.
            exists [t].
            intuition.
            apply atomic_single.
        +   destruct t' as [[[T [σ μ]] [i a]] [T' [σ' μ']]].
            *   destruct a.
                unfold final in Hc.
                simpl in Hc.


        
                *) 
(* Amélioration de la définition de transition pour ne pas avoir
    à prouver une égalité par refl_equal à chaque fois *)