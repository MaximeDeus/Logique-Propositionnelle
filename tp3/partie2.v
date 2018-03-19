Definition faux := forall (P : Prop), P.
Definition non (A : Prop) := forall (P : Prop), ((A -> faux) -> P) -> P.
Definition et (A B : Prop) := forall (P : Prop), (A -> B -> P) -> P.
Definition ou (A B : Prop) := forall (P : Prop), ((A -> P) -> (B -> P) -> P).
Definition existe (A : Type) (P : A -> Prop) := forall (Q : Prop), (forall a, P a -> Q) -> Q.
Definition egal (A : Type) (a a' : A) := forall (P : A -> Prop), P a -> P a'.

Lemma bottom_e (A : Prop) : faux -> A.
Proof.
intro faux.
apply faux.
Qed.

Lemma non_intro (A : Prop) : (A -> faux) -> non A.
Proof.
intro aImplyFaux.
intro a.
intro aImplyFauxImplyA.
now apply aImplyFauxImplyA.
Qed.



Lemma non_elim (A : Prop) : A -> non A -> faux.
Proof.
intro a.
intro nonA.
apply nonA.
intro aImplyFaux.
intro faux.
apply aImplyFaux.
exact a.
Qed.

Lemma et_intro (A B : Prop) : A -> B -> et A B.
Proof.
intro a.
intro b.
intro et.
intro aImplyBImplyEt.
apply aImplyBImplyEt.
  + exact a.
  + exact b.
Qed.

Lemma et_elim_g (A B : Prop) : et A B -> A.
Proof.
intro etAB.
apply etAB.
intro a.
intro b.
exact a.
Qed.

Lemma et_elim_d (A B : Prop) : et A B -> B.
Proof.
intro etAB.
apply etAB.
intro a.
intro b.
exact b.
Qed.

Lemma ou_intro_g (A B : Prop) : A -> ou A B.
Proof.
intro a.
intro prop.
intro aProp.
intro bProp.
now apply aProp.
Qed.

Lemma ou_intro_d (A B : Prop) : B -> ou A B.
Proof.
intro b.
intro prop.
intro aProp.
intro bProp.
now apply bProp.
Qed.

Lemma ou_elim (A B C : Prop) : ou A B -> (A -> C) -> (B -> C) -> C.
Proof.
intro l.
apply l.
Qed.

Lemma existe_intro (A : Type) (P : A -> Prop) : forall x : A, P x -> existe A P.
Proof.
intro x.
intro px.
intro p.
intro forAllPaImplyaImplyp.
apply (forAllPaImplyaImplyp x).
apply px.
Qed.


Lemma existe_elim (A : Type) (P : A -> Prop) (Q : Prop) : existe A P -> (forall x : A, P x -> Q) -> Q.
Proof.
intro existAP.
intro forAllxPxImplyQ.
apply existAP.
now apply forAllxPxImplyQ.
Qed.

Lemma faux_false : faux <-> False.
Proof.
split.
  + intro faux.
    apply faux.
  + intro false.
    intro faux.
    destruct false.
Qed.

Lemma non_not (A : Prop) : non A <-> ~A.
Proof.
split.
  + intro nonA.
    intro a.
    apply nonA.
    intro aImplyFaux.
    apply aImplyFaux.
    exact a.
  + intro nonA.
    intro nonAProp.
    intro aImplyFauxImplynonAProp.
    now apply aImplyFauxImplynonAProp.

Qed.

Lemma et_and (A B : Prop) : et A B <-> A /\ B.
Proof.
split.
  + intro etAB.
    apply etAB.
    now apply etAB. 
  + intro andAB.
    destruct andAB as [a b].
    intro etAB.
    intro aImplyBImplyEtAB.
    now apply aImplyBImplyEtAB.
Qed.

Lemma ou_or (A B : Prop) : ou A B <-> A \/ B.
Proof.
split.
  + intro ouAB.
    apply ouAB.
    -  intro a.
       left.
       exact a.
    -  intro b.
       right.
       exact b.
  + intro aOuB.
    destruct aOuB as [a|b].
    - intro aProp.
      intro aImplyaProp.
      intro bImplyaProp.
      apply aImplyaProp.
      exact a.
    - intro bProp.
      intro aImplyProp.
      intro bImplyaProp.
      apply bImplyaProp.
      exact b.
Qed.

Lemma existe_exists (A : Type) (P : A -> Prop) : existe A P <-> exists a, P a.
Proof.
Qed.

Lemma egal_eq (A : Type) (a a' : A) : egal _ a a' <-> a = a'.
Proof.
split.
  + intro egalAa'.
    apply egalAa'.
    reflexivity.
  + intro aEgalA'.
    rewrite aEgalA'.
    intro AImplyProp.
    intro AImplyPropA.
    apply AImplyPropA.
Qed.
