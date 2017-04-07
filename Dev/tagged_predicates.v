Require Export ProjectiveGeometry.Dev.sets_of_points.

Section s_Tagged_predicates.

Context `{MR : MatroidRk}.

Definition rk_tagged A := rk A.

Lemma rk_rk_tagged : forall A , rk A = rk_tagged A.
Proof.
trivial.
Qed.

Lemma rk_tagged_rk : forall A , rk_tagged A = rk A.
Proof.
trivial.
Qed.

End s_Tagged_predicates.