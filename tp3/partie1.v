Lemma hilbertS (A B C : Prop) :  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
intro a.
intro b.
intro c.
apply a. 
  + exact c.
  + apply b.
    exact c.

Qed.

Print hilbertS.

Definition hilbertS' (A B C : Prop) :  (A -> B -> C) -> (A -> B) -> A -> C :=
fun a b c =>  a c (b c).

Print hilbertS'.

Lemma q2 (A B : Prop) :  A -> (B -> A).
Proof.
intros a ab.
exact a.
Qed.

Lemma q3 (A B : Prop) :  A -> (~A -> B).
Proof.
intro a.
intro nota.
destruct nota.
exact a.
Qed.

Lemma q4 (A B C : Prop) :  (A -> B) -> ((B -> C) -> (A -> C)).
Proof.
intro ab.
intro bc.
intro a.
apply bc.
apply ab.
exact a.
Qed.

Lemma q5 (A B : Prop) :  (A -> B) -> (~B -> ~A).
Proof.
intro ab.
intro notb.
intro nota.
apply notb.
apply ab.
exact nota.
Qed.

Require Import Classical.

Lemma tiersexclus (A : Prop) : A \/ ~A.
Proof.
apply NNPP.
intro aornota.
apply aornota.
right.
intro nota.
apply aornota.
left.
exact nota.

Qed.

Lemma bottom_c (A : Prop) : (~A -> False) -> A.
Proof.
intro not_a.
apply NNPP.
exact not_a.
Qed.


Lemma q8 (A B : Prop) : (~B -> ~A) -> (A -> B).
Proof.
intros ba a.
apply bottom_c.
intro not_b.
apply ba.
  + exact not_b.
  + exact a.
Qed.

Lemma q9 (A : Prop) : ~~A <-> A.
Proof.
split.
  - apply bottom_c.
  - intro a.
    intro notA.
    apply notA.
    exact a.
Qed.

Lemma q10 (A : Prop) :  (A /\ ~A) <-> False.
Proof.
split.
  + intro aAndNotA.
    apply aAndNotA.
    destruct aAndNotA as [a b].
    exact a.
  + intro false.
    split.
    - apply NNPP.
      intro a.
      exact false.
    - intro a.
      exact false.
Qed.


Lemma q11 (A B : Prop) :  (A \/ B) <-> ~(~A /\ ~B).
Proof.
split.
    + intro a_or_b.
      intro a_and_b.
      destruct a_and_b as [a b].
      destruct a_or_b as [a1 | b1].
      apply a.
      exact a1.
      apply b.
      exact b1.
    + intro not_a_and_b.
      left.
      apply bottom_c.
      intro na.
      apply not_a_and_b.
      split.
      exact na. (* pas teminé
Qed. 
*)

Lemma q12 (A : Prop) :  ~A <-> (A -> False).
Proof.
split.
  - intro not_a.
    intro a.
    apply not_a.
    exact a.
  - intro bot_a.
    intro not_a.
    apply bot_a.
    exact not_a.
Qed.

Lemma q13 (A B : Prop) :  (A <-> B) <-> (A -> B) /\ (B -> A).
Proof.
split.
   - intro a_eq_b.
     split.
         + intro a.
           apply a_eq_b.
           exact a.
         + intro b.
           apply a_eq_b.
           exact b.
   - intro abba.
     split.
         + intro a.
           apply abba.
           exact a.
         + intro b.
           apply abba.
           exact b.
Qed.




Lemma q14 (A B C : Prop) :  (A /\ B -> C) <-> (A -> B -> C).
Proof.
split.
  + intro aAndBImplyC.
    intros a b.
    apply aAndBImplyC.
    split.
    - exact a.
    - exact b.
  + intro aImplyBImplyC.
    intro aAndB.
    now apply aImplyBImplyC.
Qed.

Lemma q15 (A B C : Prop) :  (C -> A)\/ (C -> B) <-> (C -> A \/ B).
Proof.
split.
  + intro CImplyAorCImplyB.
    intro c.
    destruct CImplyAorCImplyB as [a|b].
    - left.
      now apply a.
    - right.
      now apply b.
  + right.
    intro c.
    apply bottom_c.
    intro notB.
    apply notB.
Qed.

Lemma q16 (X : Type) (A B : X -> Prop) : ((forall x, A x) \/ (forall x, B x)) -> forall x, A x \/ B x.
Proof.
intro fAOrfB.
intro fafB'.
destruct fAOrfB as [fA|fB].
  + left.
    apply fA.
  + right.
    apply fB.
Qed.

Lemma q17 (X : Type) (A B : X -> Prop) : (exists x, A x /\ B x) -> ((exists x, A x) /\ (exists x, B x)).
Proof.
intro existsAxAndBx.
destruct existsAxAndBx as [x axbx].
destruct axbx as [ax bx].
exists.

  + exists x.
    exact ax.
  + exists x.
    exact bx.
Qed.

Lemma q18 (A B : Prop) : ~ (A /\ B) -> (~ A \/ ~ B).
Proof.
intro AandB.
apply bottom_c.
intro notNotaAndNotb.
apply notNotaAndNotb.
left.
intro a.
apply notNotaAndNotb.
right.
intro b.
apply AandB.
split.
  +exact a.
  +exact b.
Qed.

Lemma q19 (X : Type) : forall (x1 x2 : X), x1 = x2 -> x2 = x1.
Proof.
intros x1 x2 l.
rewrite l.
reflexivity.
Qed.

Lemma q20 (X : Type) : forall (x1 x2 x3 : X), x1 = x2 /\ x2 = x3 -> x1 = x3.
Proof.
intros x1 x2 x3 l.
destruct l as [ll lr].
rewrite ll.
rewrite lr.
reflexivity.
Qed.

