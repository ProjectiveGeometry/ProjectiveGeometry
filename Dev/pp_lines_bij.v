Require Export ProjectiveGeometry.Dev.pp_decidability.
Require Export ProjectiveGeometry.Dev.proof_irrevelance.


Section s_ProjectivePlane'LinesBijection.

Context `{PP : ProjectivePlane'}.
Context `{PI : ProofIrrevelance}.

Definition inj (A B:Type)(f:A->B) : Prop :=
forall x y:A, f x = f y -> x = y.

Definition surj (A B:Type)(f:A->B) : Prop :=
forall y:B, exists x: A, y = f x.

Definition bij (A B:Type)(f:A->B) : Prop := inj A B f /\ surj A B f.

Definition line_as_set_of_points (l:Line) := { x : Point | Incid x l}.

Arguments bij [ A B ].

Theorem line_set_of_points :
forall l1 l2:Line, exists f : (line_as_set_of_points l1) -> (line_as_set_of_points l2), bij f.
Proof.
intros l1 l2. 
elim (outsider l1 l2).
intros newP (HnewPl1,HnewPl2).
(* explicit construction of f *)
pose (f :=  (fun (ls1:line_as_set_of_points l1) => let (A1, HA1) := ls1 in 
         let (delta', Hdelta') := a1_exist A1 newP in 
           match Hdelta' with
             | conj H1delta' H2delta' => let (A2,HA2) := (a2_exist delta' l2) in 
               match HA2 with
                 | conj HA2delta' HA2l2 => exist (fun x : Point => Incid x l2) A2 HA2l2
               end
           end)).
exists f.
split.
(* one-to-one *)
unfold inj.
intros ls1 ls1'; case ls1; case ls1'.
intros A1 HA1 B1 HB1; simpl.
elim (a1_exist B1 newP).
intros d (HdB1, HdnewP).
elim (a2_exist d l2).
intros B2 (HdB2,HB2l2).

elim (a1_exist A1 newP).
intros d' (HA1d',HnewPd').
elim (a2_exist d' l2).
intros A2 (HA2d',HA2l2).
intros H.
inversion H.
subst B2.
assert (A1=B1).
assert (d=d').
assert (HA2newP:(A2<>newP)).
intros HA2newP.
subst A2.
apply HnewPl2.
assumption.
apply (a1_unique A2 newP d d' HA2newP); assumption.
subst d'.
assert (Hl1d:(l1<>d)).
intros Hl1d.
subst l1.
apply HnewPl1.
assumption.
apply (a2_unique l1 d A1 B1 Hl1d); assumption.
subst A1.
rewrite (proof_irr _ HA1 HB1).
reflexivity.

(* onto *)
unfold surj.
intros ls2; case ls2.
intros A2 HA2.
elim (a1_exist A2 newP).
intros d (HA2d,HnewPd).
elim (a2_exist l1 d).
intros A1 (HA1l1,HA1d).
exists (exist (fun (A:Point) => (Incid A l1)) A1 HA1l1).
simpl.
elim (a1_exist A1 newP).
intros d' (HA1d',HnewPd').
elim (a2_exist d' l2).
intros B2 (HA2d', HA1l2).
assert (A2=B2).
assert (d=d').
assert (HA1newP:(A1<>newP)).
intros HA1newP.
subst A1.
apply HnewPl1.
assumption.
apply (a1_unique A1 newP d d' HA1newP); assumption.
subst d'.
assert (Hl2d:(l2<>d)).
intros Hl2d.
subst l2.
apply HnewPl2.
assumption.
apply (a2_unique l2 d A2 B2 Hl2d); assumption.
subst A2.
rewrite (proof_irr _ HA2 HA1l2).
reflexivity.
Qed.

End s_ProjectivePlane'LinesBijection.