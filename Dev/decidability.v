Require Export Containers.SetInterface.

(*****************************************************************************)
(** Point & decidability **)

Notation "s [==] t" := (s === t) (at level 70, no associativity).

Section s_Decidability.

Class ObjectPoint := {
Point : Set
}.

Class EqDecidability `(U : Set) := {
eq_dec_u : forall A B : U, {A [==] B} + {~ A [==] B}
}.

Class EqDecidabilityL (L : Set) := {
eq_dec_l : forall A B : L, {A = B} + {~ A = B}
}.

Class EqDecidabilityP (L : Set) (P : L -> L -> Prop) := {
eq_dec_p : forall A B : L, {P A B} + {~ (P A B)}
}.

End s_Decidability.


