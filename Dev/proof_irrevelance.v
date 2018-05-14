(*****************************************************************************)
(** Proof irrevelance **)

Section s_PI.

Class ProofIrrevelance := {
proof_irr : forall A : Prop, forall p q:A, p=q 
}.

End s_PI.

