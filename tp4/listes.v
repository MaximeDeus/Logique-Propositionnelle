Inductive liste : Type :=
 | nil : liste
 | C : nat -> liste -> liste.

(* longueur *)

(* concat *)

Theorem long (l m : liste) : longueur(concat l m) = longueur l + longueur m.

(* ajoutqueue *)

Theorem lgajout (x : nat) (l : liste) : longueur(ajoutqueue x l) = 1 + longueur l.