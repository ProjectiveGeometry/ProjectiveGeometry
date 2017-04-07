Require Export ProjectiveGeometry.Dev.psoh_equiv_cop.

(*****************************************************************************)
(** Coplanar with all **)


Section s_psohEquivCopWA_1.

Context `{PPS : PreProjectiveSpace}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.
Context `{EL : EqDecidabilityL Line}.
Context `{ELI : EqDecidabilityP Line Intersect}.

(*** Definition flatten ***)
Fixpoint flatten A (l : list (list A)) : list A := 
match l with
|nil => nil
|a :: r => app a (flatten A r)
end.

(*** Definition all_triples ***)
Fixpoint all_triples (l : list Point) : list (Point * Point * Point) := 
match l with 
| nil => nil
| a :: reste =>  flatten _ (List.map (fun y:Point => (map_monotonic (fun x:Point => (a,x,y)) reste)) reste) ++ all_triples reste
end.

(*** Definition coplanar_with_all ***)
Fixpoint coplanar_with_all a l :=
match l with
| nil => true
| (b,c,d)::reste => if coplanar a b c d then coplanar_with_all a reste else false
end. 

Functional Scheme c_all_ind2 := Induction for coplanar_with_all Sort Prop.

(*** Definition fst3 ***)
Definition fst3 (p : Point * Point * Point) := 
match p with 
| ( x, y, z) => x
end.

(*** Definition snd3 ***)
Definition snd3 (p : Point * Point * Point) := 
match p with 
| ( x, y, z) => y
end.

(*** Definition thd3 ***)
Definition thd3 (p : Point * Point * Point) := 
match p with 
| ( x, y, z) => z
end.

(*** Definition eq3 ***)
Definition eq3 X Y := (fst3 X)[==](fst3 Y) /\ (snd3 X)[==](snd3 Y) /\ (thd3 X)[==](thd3 Y)
\/ (fst3 X)[==](fst3 Y) /\ (snd3 X)[==](thd3 Y) /\ (thd3 X)[==](snd3 Y)
\/ (fst3 X)[==](snd3 Y) /\ (snd3 X)[==](fst3 Y) /\ (thd3 X)[==](thd3 Y)
\/ (fst3 X)[==](snd3 Y) /\ (snd3 X)[==](thd3 Y) /\ (thd3 X)[==](fst3 Y)
\/ (fst3 X)[==](thd3 Y) /\ (snd3 X)[==](fst3 Y) /\ (thd3 X)[==](snd3 Y)
\/ (fst3 X)[==](thd3 Y) /\ (snd3 X)[==](snd3 Y) /\ (thd3 X)[==](fst3 Y).

End s_psohEquivCopWA_1.


Ltac destruct_all := match goal with [|- forall w: Point*Point*Point, ?M] => 
  let w:= fresh in intros w; let x:=fresh "x" in let y:=fresh "y" in let z:= fresh "z" in destruct w as [[x y] z]  end.


Section s_psohEquivCopWA_2.

Context `{PPS : PreProjectiveSpace}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.
Context `{EL : EqDecidabilityL Line}.
Context `{ELI : EqDecidabilityP Line Intersect}.

Lemma eq3_dec : forall X Y, {eq3 X Y}+{~eq3 X Y}.
Proof.
repeat destruct_all.
destruct (eq_dec_u x x0); destruct (eq_dec_u y y0); destruct (eq_dec_u z z0); 
  destruct (eq_dec_u x y0); destruct (eq_dec_u y z0); destruct (eq_dec_u z x0);
    destruct (eq_dec_u x z0); destruct (eq_dec_u y x0); destruct (eq_dec_u z y0); 
unfold eq3; simpl; try solve [intuition].
Qed.

Lemma inclA_concat_cop : forall l m,  inclA eq3 l (l++m).
Proof.
induction l.
simpl; unfold inclA; intros.
inversion H.
intros; simpl.
unfold inclA; intros.
destruct (eq3_dec x a).
apply InA_cons_hd; assumption.
inversion H.
subst.
apply False_ind; solve [intuition].
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma inclA_concat2_cop : forall   l m,  inclA eq3 m (l++m).
Proof.
induction l.
simpl; unfold inclA; solve [trivial].
intros; simpl.
unfold inclA; intros.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma all_triples_lemma : forall a l, inclA eq3 (all_triples l) (all_triples (a::l)).
Proof.
induction l.
unfold inclA; simpl; solve [trivial].
unfold inclA; simpl; intros.
apply InA_cons_tl.
apply inclA_concat2_cop.
assumption.
Qed.

Lemma coplanar_cons : forall x a l, coplanar_with_all a (x::l) = true -> coplanar_with_all a l = true.
Proof.
intros.
destruct x. simpl in *.
destruct p.
destruct (coplanar a p p1 p0).
assumption.
inversion H.
Qed.

Lemma coplanar_app : forall a l m, coplanar_with_all a l = true -> coplanar_with_all a m = true -> 
coplanar_with_all a (l++m) = true.
Proof.
induction l.
simpl.
solve [trivial].
simpl; intros.
destruct a0.
destruct p.
destruct (coplanar a p p1 p0).
apply IHl; assumption.
inversion H.
Qed.

Lemma cop_inA_all : forall a b c d m, coplanar a b c d = false -> InA eq3 (b,c,d) m -> coplanar_with_all a m = true -> False.
Proof.
intros a b c d m; elim m using c_all_ind2.
intros; subst.
inversion H0.
intros; subst.
destruct (eq3_dec (b,c,d) (b0,c0,d0)).
eapply H.
eassumption.
destruct e.
destruct H3 as [f g]. destruct g as [s t].
rewrite <- f in e2.
rewrite <- s in e2.
rewrite <- t in e2.
simpl in e2.
rewrite e2 in H0.
inversion H0.
destruct H3.
destruct H3 as [f g]. destruct g as [s t].
rewrite <- f in e2.
rewrite <- s in e2.
rewrite <- t in e2.
simpl in e2.
rewrite cop_exchange2 in e2.
rewrite e2 in H0.
inversion H0.
destruct H3.
destruct H3 as [f g]. destruct g as [s t].
rewrite <- f in e2.
rewrite <- s in e2.
rewrite <- t in e2.
simpl in e2.
rewrite cop_exchange3 in e2.
rewrite e2 in H0.
inversion H0.
destruct H3.
destruct H3 as [f g]. destruct g as [s t].
rewrite <- f in e2.
rewrite <- s in e2.
rewrite <- t in e2.
simpl in e2.
rewrite cop_exchange3 in e2.
rewrite cop_exchange2 in e2.
rewrite e2 in H0.
inversion H0.
destruct H3.
destruct H3 as [f g]. destruct g as [s t].
rewrite <- f in e2.
rewrite <- s in e2.
rewrite <- t in e2.
simpl in e2.
rewrite cop_exchange2 in e2.
rewrite cop_exchange3 in e2.
rewrite e2 in H0.
inversion H0.
destruct H3 as [f g]. destruct g as [s t].
rewrite <- f in e2.
rewrite <- s in e2.
rewrite <- t in e2.
simpl in e2.
rewrite cop_exchange2 in e2.
rewrite cop_exchange3 in e2.
rewrite cop_exchange2 in e2.
rewrite e2 in H0.
inversion H0.
assumption.
assert (T:InA eq3 (b,c,d) reste).
inversion H1.
apply False_ind; solve [intuition].
assumption.
apply H; assumption.
intros; subst.
inversion H1.
Qed.

Lemma coplanar_inclA : forall a l m, inclA eq3 l m -> coplanar_with_all a m = true -> coplanar_with_all a l = true.
Proof.
intros a l; elim l using c_all_ind2.
intros; subst.
solve [trivial].
intros m y r Hl b c Hy d e Hy0 Hcop IH z. elim z using c_all_ind2.
intros; subst.
assert (T: InA eq3 (d,e,c) ((d,e,c)::r)).
apply InA_cons_hd.
unfold eq3; solve [intuition]. 
generalize (H (d,e,c) T); intros Hinv; inversion Hinv.
intros; subst.
eapply (IH ((b0,c0,d0)::reste)).
unfold inclA; intros.
apply H0.
apply InA_cons_tl.
assumption.
simpl.
destruct (coplanar a b0 c0 d0).
assumption.
inversion e3.
intros; subst.
inversion H0.
intros; subst.
assert (InA eq3 (b,c,d) m).
apply H.
apply InA_cons_hd.
unfold eq3; solve [intuition].
apply False_ind.
eapply cop_inA_all; eassumption.
Qed.

Lemma coplanar_equal : 
forall a b l, a[==]b -> coplanar_with_all a l = coplanar_with_all b l. 
Proof.
intros a b l Hab.
elim l using c_all_ind2.
solve [trivial].
intros; subst; simpl.
rewrite Hab in e2.
rewrite e2.
assumption.
intros; subst; simpl.
rewrite Hab in e2.
rewrite e2.
solve [trivial].
Qed.

Global Instance eq3_equiv : Equivalence eq3.
Proof.
split.
intros s; destruct s; unfold eq3; simpl; left.
split. reflexivity.
split. reflexivity.
reflexivity.
intros x y H; destruct x; destruct y; unfold eq3;  destruct H; simpl in *. 
left.
split. symmetry. solve [intuition].
split. symmetry. solve [intuition].
symmetry. solve [intuition].
destruct H.
right; left.
split. symmetry. solve [intuition].
split. symmetry. solve [intuition].
symmetry. solve [intuition].
destruct H.
right; right; left.
split. symmetry. solve [intuition].
split. symmetry. solve [intuition].
symmetry. solve [intuition].
destruct H.
right; right; right; right. left.
split. symmetry. solve [intuition].
split. symmetry. solve [intuition].
symmetry. solve [intuition].
destruct H.
right; right; right; left.
split. symmetry. solve [intuition].
split. symmetry. solve [intuition].
symmetry. solve [intuition].
right; right; right; right; right.
split. symmetry. solve [intuition].
split. symmetry. solve [intuition].
symmetry. solve [intuition].
 
intros x y z Hxy Hyz; unfold eq3 in *. 
  destruct x; destruct y; destruct z.
destruct p; destruct p1; destruct p3.
simpl in *.
destruct Hxy.
destruct Hyz.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H1.
rewrite H4 in H2.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H1.
rewrite H4 in H2.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H1.
rewrite H4 in H2.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H1.
rewrite H4 in H2.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H1.
rewrite H4 in H2.
intuition.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H1.
rewrite H4 in H2.
intuition.

destruct H.
destruct Hyz.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H2.
rewrite H4 in H1.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H2.
rewrite H4 in H1.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H2.
rewrite H4 in H1.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H2.
rewrite H4 in H1.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H2.
rewrite H4 in H1.
intuition.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H.
rewrite H3 in H2.
rewrite H4 in H1.
intuition.

destruct H.
destruct Hyz.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H.
rewrite H4 in H2.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H.
rewrite H4 in H2.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H.
rewrite H4 in H2.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H.
rewrite H4 in H2.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H.
rewrite H4 in H2.
intuition.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H.
rewrite H4 in H2.
intuition.

destruct H.
destruct Hyz.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H.
rewrite H4 in H1.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H.
rewrite H4 in H1.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H.
rewrite H4 in H1.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H.
rewrite H4 in H1.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H.
rewrite H4 in H1.
intuition.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H.
rewrite H4 in H1.
intuition.

destruct H.
destruct Hyz.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H2.
rewrite H4 in H.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H2.
rewrite H4 in H.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H2.
rewrite H4 in H.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H2.
rewrite H4 in H.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H2.
rewrite H4 in H.
intuition.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H1.
rewrite H3 in H2.
rewrite H4 in H.
intuition.

destruct Hyz.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H1.
rewrite H4 in H.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H1.
rewrite H4 in H.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H1.
rewrite H4 in H.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H1.
rewrite H4 in H.
intuition.
destruct H0.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H1.
rewrite H4 in H.
intuition.
destruct H; destruct H1; destruct H0; destruct H3.
rewrite H0 in H2.
rewrite H3 in H1.
rewrite H4 in H.
intuition.
Qed.

Global Instance eq3_InA : Proper (eq3 ==> (@equivlistA (Point*Point*Point) eq3) ==> flip impl) (InA eq3).
Proof.
repeat red.
intros x y Hxy.
intros l m. revert l. elim m.
intros; inversion H0.
intros; subst.
rewrite H0.
rewrite Hxy.
assumption.
Qed.

Instance coplanar_with_all_morph  : Proper (eq ==> @equivlistA (Point*Point*Point) eq3 ==> (@Logic.eq bool)) coplanar_with_all.
Proof.
repeat red.
intros p q Hpq x y Hxy.
case_eq (coplanar_with_all p x).
case_eq (coplanar_with_all q y).
solve [trivial].
intros HA HB.
assert (T : coplanar_with_all q x = true).
rewrite <- (coplanar_equal p q x Hpq).
assumption.
assert (U: inclA eq3 y x).
unfold inclA; intros t; destruct (Hxy t); solve [intuition].
assert (V:=coplanar_inclA q _ _ U T).
rewrite V in *.
solve [intuition].
case_eq (coplanar_with_all q y).
intros HA HB.
assert (T: coplanar_with_all p y = true).
rewrite <- (coplanar_equal q p y).
assumption.
symmetry; solve [intuition].
assert (U:inclA eq3 x y).
unfold inclA; intros t; destruct (Hxy t); solve [intuition].
assert (V:=coplanar_inclA p x y U T).
rewrite V in *.
solve [intuition].
solve [trivial].
Qed.

Lemma InA_eq3_aux1 : forall a B C a0, forall l,
InA eq3 (a, B, C) (map_monotonic (fun x : Point => (a, x, a0)) l) -> 
InA eq B (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1_bis : forall a B C a0, forall l,
InA eq3 (a, B, C) (map_monotonic (fun x : Point => (a, a0, x)) l) -> 
InA eq B (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1' : forall a B C a0, forall l,
InA eq3 (a, B, C) (map_monotonic (fun x : Point => (a, x, a0)) l) -> 
InA eq C (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1_bis' : forall a B C a0, forall l,
InA eq3 (a, B, C) (map_monotonic (fun x : Point => (a, a0, x)) l) -> 
InA eq C (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1'' : forall a B C a0, forall l,
InA eq3 (B, a, C) (map_monotonic (fun x : Point => (a, x, a0)) l) -> 
InA eq B (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
rewrite <-H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1_bis'' : forall a B C a0, forall l,
InA eq3 (B, a, C) (map_monotonic (fun x : Point => (a, a0, x)) l) -> 
InA eq B (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
rewrite <-H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1''' : forall a B C a0, forall l,
InA eq3 (B, a, C) (map_monotonic (fun x : Point => (a, x, a0)) l) -> 
InA eq C (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
rewrite <-H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1_bis''' : forall a B C a0, forall l,
InA eq3 (B, a, C) (map_monotonic (fun x : Point => (a, a0, x)) l) -> 
InA eq C (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H0.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
rewrite <-H1.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1'''' : forall a B C a0, forall l,
InA eq3 (B, C, a) (map_monotonic (fun x : Point => (a, x, a0)) l) -> 
InA eq B (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
rewrite <-H2.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H2.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1_bis'''' : forall a B C a0, forall l,
InA eq3 (B, C, a) (map_monotonic (fun x : Point => (a, a0, x)) l) -> 
InA eq B (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
rewrite <-H2.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H2.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1''''' : forall a B C a0, forall l,
InA eq3 (B, C, a) (map_monotonic (fun x : Point => (a, x, a0)) l) -> 
InA eq C (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H2.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H2.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux1_bis''''' : forall a B C a0, forall l,
InA eq3 (B, C, a) (map_monotonic (fun x : Point => (a, a0, x)) l) -> 
InA eq C (a0 :: l).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
destruct H1.
rewrite <-H2.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H2.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
apply InA_cons_tl.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H0.
destruct H1.
rewrite <-H2.
apply InA_cons_hd.
assumption.
destruct H0.
destruct H1.
apply InA_cons_hd.
assumption.
subst.
assert( HH0 := IHl H1).
inversion HH0.
rewrite H2.
intuition.
apply InA_cons_tl.
apply InA_cons_tl.
assumption.
Qed.

Lemma InA_eq3_aux2 : forall a B C a0, forall l, forall l',
InA eq3 (a, B, C)
      (flatten (Point * Point * Point)
         (List.map
            (fun y : Point =>
             (a, a0, y) :: (l' y)) l)) ->
InA eq3 (a, B, C) (map_monotonic (fun y : Point => (a, a0, y)) l) \/ 
InA eq3 (a, B, C) (flatten (Point * Point * Point)(List.map (fun y : Point => (l' y)) l)).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl.
simpl in H.
inversion H.
subst.
left.
apply InA_cons_hd.
assumption.
subst.
apply InA_app_iff in H1.
destruct H1.
right.
apply InA_app_iff.
left.
assumption.
assert( HH0 := IHl H0).
destruct HH0.
left.
apply InA_cons_tl.
assumption.
right.
apply InA_app_iff.
right.
assumption.
Qed.

Lemma InA_eq3_aux2' : forall a B C a0, forall l, forall l',
InA eq3 (B, a, C)
      (flatten (Point * Point * Point)
         (List.map
            (fun y : Point =>
             (a, a0, y) :: (l' y)) l)) ->
InA eq3 (B, a, C) (map_monotonic (fun y : Point => (a, a0, y)) l) \/ 
InA eq3 (B, a, C) (flatten (Point * Point * Point)(List.map (fun y : Point => (l' y)) l)).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl.
simpl in H.
inversion H.
subst.
left.
apply InA_cons_hd.
assumption.
subst.
apply InA_app_iff in H1.
destruct H1.
right.
apply InA_app_iff.
left.
assumption.
assert( HH0 := IHl H0).
destruct HH0.
left.
apply InA_cons_tl.
assumption.
right.
apply InA_app_iff.
right.
assumption.
Qed.

Lemma InA_eq3_aux2'' : forall a B C a0, forall l, forall l',
InA eq3 (B, C, a)
      (flatten (Point * Point * Point)
         (List.map
            (fun y : Point =>
             (a, a0, y) :: (l' y)) l)) ->
InA eq3 (B, C, a) (map_monotonic (fun y : Point => (a, a0, y)) l) \/ 
InA eq3 (B, C, a) (flatten (Point * Point * Point)(List.map (fun y : Point => (l' y)) l)).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl.
simpl in H.
inversion H.
subst.
left.
apply InA_cons_hd.
assumption.
subst.
apply InA_app_iff in H1.
destruct H1.
right.
apply InA_app_iff.
left.
assumption.
assert( HH0 := IHl H0).
destruct HH0.
left.
apply InA_cons_tl.
assumption.
right.
apply InA_app_iff.
right.
assumption.
Qed.

Lemma InA_eq3_eq_all_triples_aux : forall a B C l, InA eq3 (a, B, C)
       (flatten (Point * Point * Point)
          (List.map (fun y : Point => map_monotonic (fun x : Point => (a, x, y)) l) l)) -> InA eq B l.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl.
intros HInA.
inversion HInA; subst.
destruct H0.
destruct H. destruct H0.
simpl in *.
rewrite H0.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H0.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H0.
rewrite H.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H0.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H0.
rewrite H.
intuition.
destruct H. destruct H0.
simpl in *.
rewrite H0.
intuition.
apply InA_app_iff in H0.
destruct H0.
apply InA_eq3_aux1 with(a:=a) (C:=C).
assumption.
apply InA_eq3_aux2 in H.
destruct H.
apply InA_eq3_aux1_bis with(a:=a) (C:=C).
assumption.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_eq_all_triples_aux' : forall a B C l, InA eq3 (a, B, C)
       (flatten (Point * Point * Point)
          (List.map (fun y : Point => map_monotonic (fun x : Point => (a, x, y)) l) l)) -> InA eq C l.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl.
intros HInA.
inversion HInA; subst.
destruct H0.
destruct H. destruct H0.
simpl in *.
rewrite H1.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H1.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H1.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H1.
rewrite H.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H1.
intuition.
destruct H. destruct H0.
simpl in *.
rewrite H1.
rewrite H.
intuition.
apply InA_app_iff in H0.
destruct H0.
apply InA_eq3_aux1' with(a:=a) (B:=B).
assumption.
apply InA_eq3_aux2 in H.
destruct H.
apply InA_eq3_aux1_bis' with(a:=a) (B:=B).
assumption.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_eq_all_triples_aux'' : forall a B C l, InA eq3 (B, a, C)
       (flatten (Point * Point * Point)
          (List.map (fun y : Point => map_monotonic (fun x : Point => (a, x, y)) l) l)) -> InA eq B l.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl.
intros HInA.
inversion HInA; subst.
destruct H0.
destruct H. destruct H0.
simpl in *.
rewrite H.
rewrite H0.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H.
rewrite H0.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H.
intuition.
destruct H. destruct H0.
simpl in *.
rewrite H.
intuition.
apply InA_app_iff in H0.
destruct H0.
apply InA_eq3_aux1'' with(a:=a) (C:=C).
assumption.
apply InA_eq3_aux2' in H.
destruct H.
apply InA_eq3_aux1_bis'' with(a:=a) (C:=C).
assumption.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_eq_all_triples_aux''' : forall a B C l, InA eq3 (B, a, C)
       (flatten (Point * Point * Point)
          (List.map (fun y : Point => map_monotonic (fun x : Point => (a, x, y)) l) l)) -> InA eq C l.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl.
intros HInA.
inversion HInA; subst.
destruct H0.
destruct H. destruct H0.
simpl in *.
rewrite H1.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H1.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H1.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H1.
rewrite H0.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H1.
intuition.
destruct H. destruct H0.
simpl in *.
rewrite H1.
rewrite H0.
intuition.
apply InA_app_iff in H0.
destruct H0.
apply InA_eq3_aux1''' with(a:=a) (B:=B).
assumption.
apply InA_eq3_aux2' in H.
destruct H.
apply InA_eq3_aux1_bis''' with(a:=a) (B:=B).
assumption.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_eq_all_triples_aux'''' : forall a B C l, InA eq3 (B, C, a)
       (flatten (Point * Point * Point)
          (List.map (fun y : Point => map_monotonic (fun x : Point => (a, x, y)) l) l)) -> InA eq B l.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl.
intros HInA.
inversion HInA; subst.
destruct H0.
destruct H. destruct H0.
simpl in *.
rewrite H.
rewrite H1.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H.
rewrite H1.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H.
intuition.
destruct H. destruct H0.
simpl in *.
rewrite H.
intuition.
apply InA_app_iff in H0.
destruct H0.
apply InA_eq3_aux1'''' with(a:=a) (C:=C).
assumption.
apply InA_eq3_aux2'' in H.
destruct H.
apply InA_eq3_aux1_bis'''' with(a:=a) (C:=C).
assumption.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_eq_all_triples_aux''''' : forall a B C l, InA eq3 (B, C, a)
       (flatten (Point * Point * Point)
          (List.map (fun y : Point => map_monotonic (fun x : Point => (a, x, y)) l) l)) -> InA eq C l.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl.
intros HInA.
inversion HInA; subst.
destruct H0.
destruct H. destruct H0.
simpl in *.
rewrite H0.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H0.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H0.
rewrite H1.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H0.
intuition.
destruct H.
destruct H. destruct H0.
simpl in *.
rewrite H0.
rewrite H1.
intuition.
destruct H. destruct H0.
simpl in *.
rewrite H0.
intuition.
apply InA_app_iff in H0.
destruct H0.
apply InA_eq3_aux1''''' with(a:=a) (B:=B).
assumption.
apply InA_eq3_aux2'' in H.
destruct H.
apply InA_eq3_aux1_bis''''' with(a:=a) (B:=B).
assumption.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_aux3 :
forall B C D a a0,forall l,
InA eq3 (B, C, D) (map_monotonic (fun x : Point => (a, x, a0)) l) ->
B[==]a \/ C[==]a \/ D[==]a.
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
left.
assumption.
destruct H0.
destruct H0.
left.
assumption.
destruct H0.
destruct H0.
destruct H1.
right.
left.
assumption.
destruct H0.
destruct H0.
destruct H1.
right.
right.
assumption.
destruct H0.
destruct H0.
destruct H1.
right.
left.
assumption.
destruct H0.
destruct H1.
right.
right.
assumption.
subst.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_aux3_bis :
forall B C D a a0,forall l,
InA eq3 (B, C, D) (map_monotonic (fun x : Point => (a, a0, x)) l) ->
B[==]a \/ C[==]a \/ D[==]a.
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl in H.
inversion H.
subst.
unfold eq3 in H1.
simpl in H1.
destruct H1.
destruct H0.
left.
assumption.
destruct H0.
destruct H0.
left.
assumption.
destruct H0.
destruct H0.
destruct H1.
right.
left.
assumption.
destruct H0.
destruct H0.
destruct H1.
right.
right.
assumption.
destruct H0.
destruct H0.
destruct H1.
right.
left.
assumption.
destruct H0.
destruct H1.
right.
right.
assumption.
subst.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_aux4 :
forall B C D a a0, forall l, forall l',
InA eq3 (B, C, D)
      (flatten (Point * Point * Point)
         (List.map
            (fun y : Point =>
             (a, a0, y) :: (l' y)) l)) ->
InA eq3 (B, C, D) (map_monotonic (fun y : Point => (a, a0, y)) l) \/ 
InA eq3 (B, C, D) (flatten (Point * Point * Point)(List.map (fun y : Point => (l' y)) l)).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl.
simpl in H.
inversion H.
subst.
left.
apply InA_cons_hd.
assumption.
subst.
apply InA_app_iff in H1.
destruct H1.
right.
apply InA_app_iff.
left.
assumption.
assert( HH0 := IHl H0).
destruct HH0.
left.
apply InA_cons_tl.
assumption.
right.
apply InA_app_iff.
right.
assumption.
Qed.

Lemma InA_eq3_eq_all_triples_aux2 : forall B C D a l,
InA eq3 (B, C, D)
       (flatten (Point * Point * Point)
          (List.map (fun y : Point => map_monotonic (fun x : Point => (a, x, y)) l) l))
-> ~ B[==]a -> ~C[==]a -> ~D[==]a -> False.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl; intros Hv.
inversion Hv; subst.
destruct H0.
destruct H. destruct H0.
simpl in *.
intros; contradiction.
destruct H.
destruct H. destruct H0.
simpl in *.
intros; contradiction.
destruct H.
destruct H. destruct H0.
simpl in *.
intros; contradiction.
destruct H.
destruct H. destruct H0.
simpl in *.
intros; contradiction.
destruct H.
destruct H. destruct H0.
simpl in *.
intros; contradiction.
destruct H.
destruct H0.
simpl in *.
intros; contradiction.
apply InA_app_iff in H0.
destruct H0.
intros.
apply InA_eq3_aux3 in H.
destruct H.
contradiction.
destruct H.
contradiction.
contradiction.
apply InA_eq3_aux4 in H.
destruct H.
apply InA_eq3_aux3_bis in H.
intros.
destruct H.
contradiction.
destruct H.
contradiction.
contradiction.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_eq_all_triples : forall B C D l, InA eq3 (B,C,D) (all_triples l) -> InA eq B l /\ InA eq C l /\ InA eq D l .
Proof.
induction l; simpl.
intros Hx; inversion Hx.
intros.
apply InA_app_iff in H.
destruct H as [HA |HB].
destruct (eq_dec_u B a).
rewrite e.
destruct (eq_dec_u C a).
rewrite e0.
destruct (eq_dec_u D a).
rewrite e1. 
split. apply InA_cons_hd; reflexivity.
split; apply InA_cons_hd; reflexivity.
split. apply InA_cons_hd; reflexivity.
split. apply InA_cons_hd; reflexivity.
apply InA_cons_tl.
assert (f:eq3 (B,C,D) (a,C,D)).
unfold eq3. left. simpl. split. assumption. split. reflexivity. reflexivity.
rewrite f in HA.
eapply InA_eq3_eq_all_triples_aux' with (a:=a) (B:=C). assumption.
destruct (eq_dec_u D a).
split. apply InA_cons_hd; reflexivity.
split.
apply InA_cons_tl.
assert (f:eq3 (B,C,D) (a,C,D)).
unfold eq3. left. simpl. split. assumption. split. reflexivity. reflexivity.
rewrite f in HA.
eapply InA_eq3_eq_all_triples_aux with (a:=a) (B:=C) (C:=D). assumption.
rewrite e0.
intuition.
split.
intuition.
split.
apply InA_cons_tl.
assert (f:eq3 (B,C,D) (a,C,D)).
unfold eq3. left. simpl. split. assumption. split. reflexivity. reflexivity.
rewrite f in HA.
eapply InA_eq3_eq_all_triples_aux with (a:=a) (B:=C) (C:=D). assumption.
apply InA_cons_tl.
assert (f:eq3 (B,C,D) (a,C,D)).
unfold eq3. left. simpl. split. assumption. split. reflexivity. reflexivity.
rewrite f in HA.
eapply InA_eq3_eq_all_triples_aux' with (a:=a) (B:=C). assumption.
destruct (eq_dec_u C a).
rewrite e.
destruct (eq_dec_u D a).
rewrite e0.
split.
apply InA_cons_tl.
assert (f:eq3 (B,C,D) (B,a,D)).
unfold eq3. left. simpl. split. reflexivity. split. assumption. reflexivity.
rewrite f in HA.
eapply InA_eq3_eq_all_triples_aux'' with (a:=a) (C:=D). assumption.
split.
intuition.
intuition.
split.
apply InA_cons_tl.
assert (f:eq3 (B,C,D) (B,a,D)).
unfold eq3. left. simpl. split. reflexivity. split. assumption. reflexivity.
rewrite f in HA.
eapply InA_eq3_eq_all_triples_aux'' with (a:=a) (C:=D). assumption.
split.
intuition.
apply InA_cons_tl.
assert (f:eq3 (B,C,D) (B,a,D)).
unfold eq3. left. simpl. split. reflexivity. split. assumption. reflexivity.
rewrite f in HA.
eapply InA_eq3_eq_all_triples_aux''' with (B:=B) (a:=a) (C:=D). assumption.
destruct (eq_dec_u D a).
rewrite e.
split.
apply InA_cons_tl.
assert (f:eq3 (B,C,D) (B,C,a)).
unfold eq3. left. simpl. split. reflexivity. split. reflexivity. assumption.
rewrite f in HA.
eapply InA_eq3_eq_all_triples_aux'''' with (B:=B) (a:=a) (C:=C). assumption.
split.
apply InA_cons_tl.
assert (f:eq3 (B,C,D) (B,C,a)).
unfold eq3. left. simpl. split. reflexivity. split. reflexivity. assumption.
rewrite f in HA.
eapply InA_eq3_eq_all_triples_aux''''' with (B:=B) (a:=a) (C:=C). assumption.
intuition.
apply False_ind; eapply InA_eq3_eq_all_triples_aux2 with (B:=B)(C:=C)(D:=D)(a:=a)(l:=l).
assumption.
assumption.
assumption.
assumption.
destruct (IHl HB).
split.
apply InA_cons_tl; assumption.
split.
destruct H0.
apply InA_cons_tl; assumption.
destruct H0.
apply InA_cons_tl; assumption.
Qed.


Lemma InA_eq3_aux5 : forall a a0 x y z,forall l,forall l',
InA eq z l ->
x[==]a ->
y[==]a0 ->
InA eq3 (x, y, z) ((a, a0, z)::(l' z)) ->
InA eq3 (x, y, z) (flatten (Point * Point * Point) (List.map (fun y0 : Point => (a,a0,y0) :: (l' y0)) l)).
Proof.
induction l.
intros.
inversion H.
intros.
simpl.
inversion H.
subst.
apply InA_cons_hd.
unfold eq3.
simpl.
left.
split.
assumption.
split.
assumption.
reflexivity.
subst.
apply InA_cons_tl.
apply InA_app_iff.
right.
apply IHl.
assumption.
assumption.
assumption.
assumption.
Qed.

Lemma InA_eq3_aux6 :
forall a a0 x y z, forall l,
x[==]a ->
z[==]a0 ->
InA eq y l ->
InA eq3 (x, y, z) (map_monotonic (fun x0 : Point => (a, x0, a0)) l).
Proof.
intros.
induction l.
inversion H1.
simpl.
inversion H1.
subst.
apply InA_cons_hd.
unfold eq3.
simpl.
left.
split.
assumption.
split.
reflexivity.
assumption.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_aux7 : forall a a0 x y z, forall l, forall l',
InA eq3 (x, y, z)
  (flatten (Point * Point * Point)
  (List.map (fun y0 : Point => (l' y0)) l)) ->
InA eq3 (x, y, z)
  (flatten (Point * Point * Point)
     (List.map
        (fun y0 : Point =>
         (a, a0, y0) :: (l' y0)) l)).
Proof.
induction l.
simpl.
intros.
inversion H.
intros.
simpl in H.
simpl.
apply InA_app_iff in H.
destruct H.
apply InA_cons_tl.
apply InA_app_iff.
left.
assumption.
apply InA_cons_tl.
apply InA_app_iff.
right.
apply IHl.
assumption.
Qed.

Lemma InA_eq3_aux8 : 
forall a x y z l, 
x[==]a ->
InA eq y l-> 
InA eq z l -> 
InA eq3 (x, y, z)
  (flatten (Point * Point * Point)
     (List.map (fun y0 : Point => map_monotonic (fun x0 : Point => (a, x0, y0)) l) l)).
Proof.
intros.
induction l.
inversion H0.
simpl.
inversion H0.
inversion H1.
subst.
apply InA_cons_hd.
unfold eq3.
left.
split.
simpl.
assumption.
split.
simpl.
reflexivity.
simpl.
reflexivity.
subst.
apply InA_cons_tl.
apply InA_app_iff.
right.
apply InA_eq3_aux5.
assumption.
assumption.
reflexivity.
apply InA_cons_hd.
unfold eq3.
simpl.
left.
split.
assumption.
split.
reflexivity.
reflexivity.
subst.
inversion H1.
subst.
apply InA_cons_tl.
apply InA_app_iff.
left.
apply InA_eq3_aux6.
assumption.
reflexivity.
assumption.
subst.
apply InA_cons_tl.
apply InA_app_iff.
right.
eapply InA_eq3_aux7.
apply IHl.
assumption.
assumption.
Qed.

Lemma InA_eq3_aux9 :
forall A B C, forall a, forall l,
InA eq3 (A,B,C) (all_triples l) ->
inclA eq3 (all_triples l) (all_triples (a :: l)) ->
InA eq3 (A,B,C) (all_triples (a :: l)).
Proof.
intros.
induction l.
simpl in *.
inversion H.
unfold inclA in *.
assert( HH0 := H0 (A,B,C) H).
assumption.
Qed.

Lemma InA_eq_eq3_all_triples : forall x y z l, InA eq x l -> InA eq y l -> InA eq z l-> 
~(x[==]y) -> ~(x[==]z) -> ~(y[==]z) ->
InA eq3 (x,y,z) (all_triples l) \/ InA eq3 (x,z,y) (all_triples l)
\/ InA eq3 (y,x,z) (all_triples l) \/ InA eq3 (y,z,x) (all_triples l)
\/ InA eq3 (z,x,y) (all_triples l) \/ InA eq3 (z,y,x) (all_triples l).
Proof.
induction l.
intros.
inversion H.
intros.
inversion H.
inversion H0.
inversion H1.
subst.
apply False_ind.
apply H2.
reflexivity.
subst.
apply False_ind.
apply H2.
reflexivity.
subst.
inversion H1.
subst.
apply False_ind.
apply H3.
reflexivity.
subst.
left.
simpl.
apply InA_app_iff.
left.
apply InA_eq3_aux8.
reflexivity.
assumption.
assumption.
subst.
inversion H0.
subst.
inversion H1.
subst.
apply False_ind.
apply H4.
reflexivity.
subst.
right.
right.
left.
simpl.
apply InA_app_iff.
left.
apply InA_eq3_aux8.
reflexivity.
assumption.
assumption.
subst.
inversion H1.
subst.
right.
right.
right.
right.
left.
simpl.
apply InA_app_iff.
left.
apply InA_eq3_aux8.
reflexivity.
assumption.
assumption.
subst.
assert( HH0 := IHl H6 H7 H8 H2 H3 H4).
destruct HH0.
left.
assert( HH0 := all_triples_lemma a l).
apply InA_eq3_aux9.
assumption.
assumption.
destruct H5.
right.
left.
assert( HH0 := all_triples_lemma a l).
apply InA_eq3_aux9.
assumption.
assumption.
destruct H5.
right.
right.
left.
assert( HH0 := all_triples_lemma a l).
apply InA_eq3_aux9.
assumption.
assumption.
destruct H5.
right.
right.
right.
left.
assert( HH0 := all_triples_lemma a l).
apply InA_eq3_aux9.
assumption.
assumption.
destruct H5.
right.
right.
right.
right.
left.
assert( HH0 := all_triples_lemma a l).
apply InA_eq3_aux9.
assumption.
assumption.
right.
right.
right.
right.
right.
assert( HH0 := all_triples_lemma a l).
apply InA_eq3_aux9.
assumption.
assumption.
Qed.

Lemma cop_with_all_cop : forall a l, coplanar_with_all a l = true -> forall x y z, InA eq3 (x,y,z) l -> coplanar a x y z = true.
Proof.
induction l.
simpl; intros.
inversion H0.
destruct a0.
simpl.
destruct p.
case_eq(coplanar a p p1 p0).
intros.
inversion H1; subst.
unfold eq3 in H3.
simpl in H3.
destruct H3.
destruct H2.
destruct H3.
rewrite H2.
rewrite H3.
rewrite H4.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2.
rewrite H3.
rewrite H4.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2.
rewrite H3.
rewrite H4.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2.
rewrite H3.
rewrite H4.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2.
rewrite H3.
rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H3.
rewrite H2.
rewrite H3.
rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.

apply IHl.
assumption.
assumption.
intros.
inversion H0.
Qed.

Lemma contains_1_aux : forall A l,
coplanar_with_all A l = false <-> exists B C D, InA eq3 (B,C,D) l/\ coplanar A B C D= false.
Proof.
induction l.
intros; simpl; split.
intros; discriminate.
intros Hex; destruct Hex as [B [ C [D (HBCD, Hcop)]]].
inversion HBCD.
simpl.
case_eq a.
intros.
case_eq p.
intros.
case_eq (coplanar A p1 p2 p0).
intros.
split.
intros.
apply IHl in H2.
destruct H2 as [B [C [D (HIn, Hcop)]]].
exists B.
exists C.
exists D.
split.
apply InA_cons_tl; assumption.
assumption.
intros.
destruct H2 as [B [C [D (HBCD,Hcop)]]].
case_eq (eq3_dec (B,C,D) (p1,p2,p0)).
intros.
destruct e.
simpl in a0.
destruct a0.
destruct a0.
rewrite e in Hcop.
rewrite e0 in Hcop.
rewrite e1 in Hcop.
rewrite Hcop in H1.
inversion H1.
simpl in o.
destruct o.
destruct a0.
destruct a0.
rewrite e in Hcop.
rewrite e0 in Hcop.
rewrite e1 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite Hcop in H1.
inversion H1.
destruct o.
destruct a0.
destruct a0.
rewrite e in Hcop.
rewrite e0 in Hcop.
rewrite e1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite Hcop in H1.
inversion H1.
destruct o.
destruct a0.
destruct a0.
rewrite e in Hcop.
rewrite e0 in Hcop.
rewrite e1 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite Hcop in H1.
inversion H1.
destruct o.
destruct a0.
destruct a0.
rewrite e in Hcop.
rewrite e0 in Hcop.
rewrite e1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite Hcop in H1.
inversion H1.
destruct a0.
destruct a0.
rewrite e in Hcop.
rewrite e0 in Hcop.
rewrite e1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite Hcop in H1.
inversion H1.

intros.
inversion HBCD; subst.
apply False_ind; apply n; assumption.
apply IHl.
exists B.
exists C.
exists D.
split.
assumption.
assumption.
intros.
split.
intros.
exists p1.
exists p2.
exists p0.
split.
apply InA_cons_hd; reflexivity.
assumption.
solve [intuition].
Qed.

Lemma coplanar_with_all_map_aux :
forall a a0, forall l,
coplanar_with_all a (map_monotonic (fun x : Point => (a, x, a0)) l) = true.
Proof.
induction l.
intros.
simpl.
reflexivity.
simpl.
case_eq (coplanar a a a1 a0).
intros.
assumption.
intros.
assert( HH0 := cop_1 a a1 a0).
rewrite HH0 in H.
inversion H.
Qed.

Lemma coplanar_with_all_map_aux_bis :
forall a a0, forall l,
coplanar_with_all a (map_monotonic (fun x : Point => (a, a0, x)) l) = true.
Proof.
induction l.
intros.
simpl.
reflexivity.
simpl.
case_eq (coplanar a a a0 a1).
intros.
assumption.
intros.
assert( HH0 := cop_1 a a0 a1).
rewrite HH0 in H.
inversion H.
Qed.

Lemma coplanar_with_all_map_aux1 :
forall a , forall l l',
coplanar_with_all a (l ++ l') = true ->
coplanar_with_all a l = true /\ coplanar_with_all a l' = true.
Proof.
induction l.
induction l'.
intros.
simpl.
split.
reflexivity.
reflexivity.
simpl.
destruct a0.
destruct p.
case_eq (coplanar a p p1 p0).
intros.
split.
reflexivity.
assumption.
intros.
inversion H0.
simpl.
intro.
destruct a0.
destruct p.
case_eq (coplanar a p p1 p0).
intros.
apply IHl.
assumption.
intros.
inversion H0.
Qed.

Lemma coplanar_with_all_map_aux2 :
forall a a0, forall l l',
coplanar_with_all a
      (flatten (Point * Point * Point)
         (List.map
            (fun y : Point =>
             (a, a0, y) :: (l' y)) l)) = true ->
coplanar_with_all a
      (flatten (Point * Point * Point)
         (List.map
            (fun y : Point =>
             (l' y)) l)) = true.
Proof.
induction l.
intros.
simpl.
reflexivity.
intros.
generalize H.
simpl.
case_eq (coplanar a a a0 a1).
intros.
simpl.
apply coplanar_with_all_map_aux1 in H1.
destruct H1.
apply coplanar_app.
assumption.
apply IHl.
assumption.
intros.
inversion H1.
Qed.

Lemma coplanar_with_all_map_aux3 :
forall a a0, forall l, forall l',
coplanar_with_all a
  (flatten (Point * Point * Point)
     (List.map (fun y : Point => (a, a0, y) :: (l' y)) l)) = true ->
coplanar_with_all a (map_monotonic (fun y : Point => (a, a0, y)) l) = true /\ 
coplanar_with_all a (flatten (Point * Point * Point) (List.map (fun y : Point => (l' y)) l)) = true.
Proof.
intros.
induction l.
simpl.
split.
reflexivity.
reflexivity.
simpl.
case_eq (coplanar a a a0 a1).
intros.
split.
apply coplanar_with_all_map_aux_bis.
generalize H.
simpl.
case_eq (coplanar a a a0 a1).
intros.
apply coplanar_with_all_map_aux1 in H2.
destruct H2.
apply coplanar_app.
assumption.
apply IHl.
assumption.
intros.
inversion H2.
intros.
assert( HH0 := cop_1 a a0 a1).
rewrite HH0 in H0.
inversion H0.
Qed.

Lemma coplanar_with_all_map_aux3_bis :
forall a a0, forall l, forall l',
coplanar_with_all a (map_monotonic (fun y : Point => (a, a0, y)) l) = true -> 
coplanar_with_all a (flatten (Point * Point * Point) (List.map (fun y : Point => (l' y)) l)) = true ->
coplanar_with_all a
  (flatten (Point * Point * Point)
     (List.map (fun y : Point => (a, a0, y) :: (l' y)) l)) = true.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
case_eq (coplanar a a a0 a1).
intros.
generalize H0.
simpl.
intros.
apply coplanar_with_all_map_aux1 in H2.
destruct H2.
apply coplanar_app.
assumption.
apply IHl.
apply coplanar_with_all_map_aux_bis.
assumption.
intros.
assert( HH0 := cop_1 a a0 a1).
rewrite HH0 in H1.
inversion H1.
Qed.

Lemma coplanar_with_all_map : forall a l, coplanar_with_all a
  (flatten (Point * Point * Point)
     (List.map (fun y : Point => map_monotonic (fun x : Point => (a, x, y)) l) l)) = true.
Proof.
induction l.
simpl; solve [trivial].
simpl.
case_eq (coplanar a a a0 a0).
intros.
apply coplanar_app.
apply coplanar_with_all_map_aux.
apply coplanar_with_all_map_aux3_bis.
apply coplanar_with_all_map_aux_bis.
assumption.
intros.
assert( HH0 := cop_1 a a0 a0).
rewrite HH0 in H.
inversion H.
Qed.

Lemma cop_with_all_app : 
  forall a l m, coplanar_with_all a (l++m) = false -> coplanar_with_all a l = true -> coplanar_with_all a m = false.
Proof.
induction l.
simpl; solve [trivial].
intros; simpl.
apply IHl.
simpl in H.
destruct a0.
destruct p.
generalize H.
case_eq (coplanar a p p1 p0).
intros.
assumption.
intros.
simpl in H0.
generalize H0.
case_eq (coplanar a p p1 p0).
intros.
rewrite H3 in H1.
inversion H1.
intros.
inversion H4.
apply coplanar_cons in H0.
assumption.
Qed.

Lemma cop_with_all_map_aux :
forall a a0 a1, forall l,
(forall A B C D ,
    InA eq A (a :: a0 :: a1 :: l) ->
    InA eq B (a :: a0 :: a1 :: l) ->
    InA eq C (a :: a0 :: a1 :: l) ->
    InA eq D (a :: a0 :: a1 :: l) -> coplanar A B C D = true) ->
coplanar_with_all a (map_monotonic (fun x : Point => (a0, x, a1)) l) = true.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
case_eq (coplanar a a0 a2 a1).
intros.
apply IHl.
intros.
assert( HH0 := H A B C D).
apply HH0.
inversion H1.
rewrite H6.
apply InA_cons_hd. reflexivity.
inversion H6.
rewrite H9.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H9.
rewrite H12.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H2.
rewrite H6.
apply InA_cons_hd. reflexivity.
inversion H6.
rewrite H9.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H9.
rewrite H12.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H3.
rewrite H6.
apply InA_cons_hd. reflexivity.
inversion H6.
rewrite H9.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H9.
rewrite H12.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H4.
rewrite H6.
apply InA_cons_hd. reflexivity.
inversion H6.
rewrite H9.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H9.
rewrite H12.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.

intros.
assert( HH0 : InA eq a (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_hd. reflexivity.
assert( HH1 : InA eq a0 (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
assert( HH2 : InA eq a1 (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
assert( HH3 : InA eq a2 (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
assert( HH4 := H a a0 a1 a2 HH0 HH1 HH2 HH3).
rewrite cop_exchange2 in HH4.
rewrite HH4 in H0.
inversion H0.
Qed.

Lemma cop_with_all_map_aux_bis :
forall a a0 a1, forall l,
(forall A B C D ,
    InA eq A (a :: a0 :: a1 :: l) ->
    InA eq B (a :: a0 :: a1 :: l) ->
    InA eq C (a :: a0 :: a1 :: l) ->
    InA eq D (a :: a0 :: a1 :: l) -> coplanar A B C D = true) ->
coplanar_with_all a (map_monotonic (fun x : Point => (a0, a1, x)) l) = true.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
case_eq (coplanar a a0 a1 a2).
intros.
apply IHl.
intros.
assert( HH0 := H A B C D).
apply HH0.
inversion H1.
rewrite H6.
apply InA_cons_hd. reflexivity.
inversion H6.
rewrite H9.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H9.
rewrite H12.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H2.
rewrite H6.
apply InA_cons_hd. reflexivity.
inversion H6.
rewrite H9.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H9.
rewrite H12.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H3.
rewrite H6.
apply InA_cons_hd. reflexivity.
inversion H6.
rewrite H9.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H9.
rewrite H12.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H4.
rewrite H6.
apply InA_cons_hd. reflexivity.
inversion H6.
rewrite H9.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H9.
rewrite H12.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.

intros.
assert( HH0 : InA eq a (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_hd. reflexivity.
assert( HH1 : InA eq a0 (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
assert( HH2 : InA eq a1 (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
assert( HH3 : InA eq a2 (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
assert( HH4 := H a a0 a1 a2 HH0 HH1 HH2 HH3).
rewrite HH4 in H0.
inversion H0.
Qed.

Lemma cop_with_all_map_aux1 :
forall a a0 a1, forall l, forall l',
(forall A B C D ,
    InA eq A (a :: a0 :: a1 :: l) ->
    InA eq B (a :: a0 :: a1 :: l) ->
    InA eq C (a :: a0 :: a1 :: l) ->
    InA eq D (a :: a0 :: a1 :: l) -> coplanar A B C D = true) ->
coplanar_with_all a (map_monotonic (fun y : Point => (a0, a1, y)) l) = true ->
coplanar_with_all a
  (flatten (Point * Point * Point)
     (List.map
        (fun y : Point => (l' y)) l)) = true ->
coplanar_with_all a
  (flatten (Point * Point * Point)
     (List.map
        (fun y : Point => (a0, a1, y) :: (l' y)) l)) = true.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
case_eq (coplanar a a0 a1 a2).
intros.
generalize H1.
simpl.
intros.
apply coplanar_with_all_map_aux1 in H3.
destruct H3.
apply coplanar_app.
assumption.
apply IHl.
intros.
apply H.
inversion H5.
rewrite H10.
apply InA_cons_hd. reflexivity.
inversion H10.
rewrite H13.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H13.
rewrite H16.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H6.
rewrite H10.
apply InA_cons_hd. reflexivity.
inversion H10.
rewrite H13.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H13.
rewrite H16.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H7.
rewrite H10.
apply InA_cons_hd. reflexivity.
inversion H10.
rewrite H13.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H13.
rewrite H16.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H8.
rewrite H10.
apply InA_cons_hd. reflexivity.
inversion H10.
rewrite H13.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H13.
rewrite H16.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
apply cop_with_all_map_aux_bis.
intros.
apply H.
inversion H5.
rewrite H10.
apply InA_cons_hd. reflexivity.
inversion H10.
rewrite H13.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H13.
rewrite H16.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H6.
rewrite H10.
apply InA_cons_hd. reflexivity.
inversion H10.
rewrite H13.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H13.
rewrite H16.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H7.
rewrite H10.
apply InA_cons_hd. reflexivity.
inversion H10.
rewrite H13.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H13.
rewrite H16.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
inversion H8.
rewrite H10.
apply InA_cons_hd. reflexivity.
inversion H10.
rewrite H13.
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
inversion H13.
rewrite H16.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl. assumption.
assumption.
intros.
assert( HH0 : InA eq a (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_hd. reflexivity.
assert( HH1 : InA eq a0 (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_tl; apply InA_cons_hd. reflexivity.
assert( HH2 : InA eq a1 (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
assert( HH3 : InA eq a2 (a :: a0 :: a1 :: a2 :: l)).
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd. reflexivity.
assert( HH4 := H a a0 a1 a2 HH0 HH1 HH2 HH3).
rewrite HH4 in H2.
inversion H2.
Qed.

Lemma cop_with_all_map : forall a a0 l, 
(forall A B C D,
    InA eq A (a :: a0 :: l) ->
    InA eq B (a :: a0 :: l) ->
    InA eq C (a :: a0 :: l) -> 
    InA eq D (a :: a0 :: l) ->
coplanar A B C D = true) -> 
coplanar_with_all a
  (flatten (Point * Point * Point)
     (List.map (fun y : Point => map_monotonic (fun x : Point => (a0, x, y)) l) l)) = true.
Proof.
induction l.
intros; simpl.
solve [trivial].
intros.
simpl.
assert (T:coplanar a a0 a1 a1 = true).
apply H.
apply InA_cons_hd; reflexivity.
apply InA_cons_tl; apply InA_cons_hd; reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd; reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd; reflexivity.
rewrite T.
apply coplanar_app.
apply cop_with_all_map_aux.
assumption.
apply cop_with_all_map_aux1.
assumption.
apply cop_with_all_map_aux_bis.
assumption.

apply IHl.
intros; apply H.
inversion H0; subst.
my_inA.
inversion H5; subst.
my_inA.
my_inA.

inversion H1; subst.
my_inA.
inversion H5; subst.
my_inA.
my_inA.

inversion H2; subst.
my_inA.
inversion H5; subst.
my_inA.
my_inA.

inversion H3; subst.
my_inA.
inversion H5; subst.
my_inA.
my_inA.
Qed.

Lemma forall_InA_coplanar_with_all : 
forall a l, ( forall A B C D,
    InA eq A (a :: l) ->
    InA eq B (a :: l) -> 
    InA eq C (a :: l) -> 
    InA eq D (a :: l) ->
coplanar A B C D = true) ->
coplanar_with_all a (all_triples l) = false -> False.
Proof.
induction l.
simpl; intros HA HB.
inversion HB.
simpl;intros.
apply IHl.
intros; apply H.
inversion H1; subst.
apply InA_cons_hd.
reflexivity.
apply InA_cons_tl; apply InA_cons_tl; assumption.
inversion H2; subst.
apply InA_cons_hd.
reflexivity.
apply InA_cons_tl; apply InA_cons_tl; assumption.
inversion H3; subst.
apply InA_cons_hd.
reflexivity.
apply InA_cons_tl; apply InA_cons_tl; assumption.
inversion H4; subst.
apply InA_cons_hd.
reflexivity.
apply InA_cons_tl; apply InA_cons_tl; assumption.
eapply cop_with_all_app. 
eassumption.
apply cop_with_all_map.
intros; apply H; assumption.
Qed.

Lemma cop_aux : forall a B C D l, coplanar_with_all a l = true -> 
InA eq3 (B,C,D) l \/ InA eq3 (B,D,C) l \/ 
InA eq3 (C,B,D) l \/ InA eq3 (C,D,B) l \/
InA eq3 (D,B,C) l \/ InA eq3 (D,C,B) l -> 
coplanar a B C D = true.
Proof.
induction l.
simpl; intros HA HB.
destruct HB. inversion H.
destruct H. inversion H.
destruct H. inversion H.
destruct H. inversion H.
destruct H. inversion H.
inversion H.
simpl. 
destruct a0.
destruct p.
case_eq (coplanar a p p1 p0).
intros.

destruct H1.
inversion H1; subst.
unfold eq3 in H3.
simpl in H3.
destruct H3.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
apply IHl.
assumption.
left.
assumption.

destruct H1.
inversion H1; subst.
unfold eq3 in H3.
simpl in H3.
destruct H3.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
assumption.
apply IHl.
assumption.
right.
left.
assumption.

destruct H1.
inversion H1; subst.
unfold eq3 in H3.
simpl in H3.
destruct H3.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
apply IHl.
assumption.
right.
right.
left.
assumption.

destruct H1.
inversion H1; subst.
unfold eq3 in H3.
simpl in H3.
destruct H3.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
rewrite cop_exchange3.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
assumption.
apply IHl.
assumption.
right.
right.
right.
left.
assumption.

destruct H1.
inversion H1; subst.
unfold eq3 in H3.
simpl in H3.
destruct H3.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
rewrite cop_exchange3.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
assumption.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
assumption.
apply IHl.
assumption.
right.
right.
right.
right.
left.
assumption.

inversion H1; subst.
unfold eq3 in H3.
simpl in H3.
destruct H3.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange2.
assumption.
destruct H2.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
rewrite cop_exchange3.
assumption.
destruct H2.
destruct H3.
rewrite H2; rewrite H3; rewrite H4.
assumption.
apply IHl.
assumption.
right.
right.
right.
right.
right.
assumption.

intros.
inversion H0.
Qed.

Lemma all_triples_aux :
forall a b a0 l, forall x,
a[==]b ->
InA eq3 x (map_monotonic (fun x0 : Point => (a, x0, a0)) l) ->
InA eq3 x (map_monotonic (fun x0 : Point => (b, x0, a0)) l).
Proof.
induction l.
simpl.
intros.
assumption.
intros.
simpl.
simpl in H0.
inversion H0;subst.
rewrite H2.
apply InA_cons_hd.
unfold eq3.
simpl.
left.
split.
assumption.
split.
reflexivity.
reflexivity.
apply InA_cons_tl.
apply IHl.
assumption.
assumption.
Qed.

Lemma all_triples_aux_bis :
forall a b a0 l, forall x,
a[==]b ->
InA eq3 x (map_monotonic (fun x0 : Point => (a, a0, x0)) l) ->
InA eq3 x (map_monotonic (fun x0 : Point => (b, a0, x0)) l).
Proof.
induction l.
simpl.
intros.
assumption.
intros.
simpl.
simpl in H0.
inversion H0;subst.
rewrite H2.
apply InA_cons_hd.
unfold eq3.
simpl.
left.
split.
assumption.
split.
reflexivity.
reflexivity.
apply InA_cons_tl.
apply IHl.
assumption.
assumption.
Qed.

Lemma all_triples_aux1 : forall a a0, forall l, forall l', forall x,
InA eq3 x
      (flatten (Point * Point * Point)
         (List.map
            (fun y : Point =>
             (a, a0, y) :: (l' y)) l)) ->
InA eq3 x (map_monotonic (fun y : Point => (a, a0, y)) l) \/ 
InA eq3 x (flatten (Point * Point * Point)(List.map (fun y : Point => (l' y)) l)).
Proof.
intros.
induction l.
simpl in H.
inversion H.
simpl.
simpl in H.
inversion H.
subst.
left.
apply InA_cons_hd.
assumption.
subst.
apply InA_app_iff in H1.
destruct H1.
right.
apply InA_app_iff.
left.
assumption.
assert( HH0 := IHl H0).
destruct HH0.
left.
apply InA_cons_tl.
assumption.
right.
apply InA_app_iff.
right.
assumption.
Qed.

Lemma all_triples_aux2 :
forall a a0, forall l, forall l', forall x,
InA eq3 x (map_monotonic (fun y : Point => (a, a0, y)) l) \/ 
InA eq3 x (flatten (Point * Point * Point) (List.map (fun y : Point => (l' y)) l)) ->
InA eq3 x
  (flatten (Point * Point * Point)
     (List.map (fun y : Point => (a, a0, y) :: (l' y)) l)).
Proof.
intros.
induction l.
simpl in *.
destruct H.
inversion H.
inversion H.
simpl.
destruct H.
simpl in H.
inversion H;subst.
rewrite H1.
apply InA_cons_hd.
intuition.
apply InA_cons_tl.
apply InA_app_iff.
right.
apply IHl.
left.
assumption.
simpl in H.
apply InA_app_iff in H.
destruct H.
apply InA_cons_tl.
apply InA_app_iff.
left.
assumption.
apply InA_cons_tl.
apply InA_app_iff.
right.
apply IHl.
right.
assumption.
Qed.

Lemma all_triples_aux3 : forall a b l, 
a[==]b -> forall x,
InA eq3 x
        (flatten (Point * Point * Point)
           (List.map (fun y : Point => map_monotonic (fun x0 : Point => (a, x0, y)) l) l)) ->
InA eq3 x
  (flatten (Point * Point * Point)
     (List.map (fun y : Point => map_monotonic (fun x0 : Point => (b, x0, y)) l) l)).
Proof.
induction l.
intros.
simpl; trivial.
simpl.
intros.
inversion H0;subst.
rewrite H2.
apply InA_cons_hd.
unfold eq3.
simpl.
left.
split.
assumption.
split.
reflexivity.
reflexivity.
apply InA_app_iff in H2.
destruct H2.
apply InA_cons_tl.
apply InA_app_iff.
left.
simpl.
apply all_triples_aux with(a:=a).
assumption.
assumption.
apply all_triples_aux1 in H1.
destruct H1.
apply InA_cons_tl.
apply InA_app_iff.
right.
apply all_triples_aux2.
left.
apply all_triples_aux_bis with(a:=a).
assumption.
assumption. 
apply InA_cons_tl.
apply InA_app_iff.
right.
apply all_triples_aux2.
right.
apply IHl.
assumption.
assumption.
Qed.

Lemma all_triples_subst_aux : forall a b l, 
a [==]b -> forall x, InA eq3 x (all_triples (a :: l)) -> InA eq3 x (all_triples (b :: l)).
Proof.
intros a b l Hab x.
simpl; intros Hyp.
apply InA_app_iff in Hyp.
destruct Hyp as [Hyp|Hyp].
apply InA_app_iff.
left.
apply all_triples_aux3 with a; eassumption.
apply InA_app_iff.
right; assumption.
Qed.

Lemma all_triples_subst : forall a b l, a [==] b -> equivlistA eq3 (all_triples (a::l)) (all_triples  (b::l)).
Proof.
intros.
split.
apply all_triples_subst_aux; assumption.
apply all_triples_subst_aux; symmetry; assumption.
Qed.

Lemma matroid3_aux0_cop : forall l, forall a a0,
coplanar_with_all a (all_triples (a0 :: l)) = true ->
coplanar_with_all a (all_triples l) = true.
Proof.
intros.
simpl in *.
assert (T:inclA eq3 (all_triples l) ((flatten (Point * Point * Point)
         (List.map (fun y : Point => map_monotonic (fun x : Point => (a0, x, y)) l) l) ++
       all_triples l))).
apply inclA_concat2_cop.
eapply coplanar_inclA.
eassumption.
assumption.
Qed.

Lemma cop_caract : forall a l,
coplanar_with_all a l = true <-> forall x y z, InA eq3 (x,y,z) l -> coplanar a x y z = true.
Proof.
induction l.
split.
intros H x y z H'; inversion H'.
intros; simpl; solve [trivial].
split.
intros.
simpl in H.
destruct a0.
destruct p.
case_eq (coplanar a p p1 p0).
intros Hrew; rewrite Hrew in *.
inversion H0;subst.
destruct H2; destruct H1.
destruct H2.
rewrite H1; rewrite H2; rewrite H3; simpl ;assumption.
destruct H1; destruct H2.
rewrite H1; rewrite H2; rewrite H3; simpl.
rewrite cop_exchange2; assumption.
destruct H1.
destruct H1; destruct H2.
rewrite H1; rewrite H2; rewrite H3; simpl.
rewrite cop_exchange3; assumption.
destruct H1.
destruct H1; destruct H2.
rewrite H1; rewrite H2; rewrite H3; simpl.
rewrite cop_exchange2; rewrite cop_exchange3; assumption. 
destruct H1.
destruct H1; destruct H2.
rewrite H1; rewrite H2; rewrite H3; simpl.
rewrite cop_exchange3; rewrite cop_exchange2; assumption.
destruct H1.
destruct H2.
rewrite H1; rewrite H2; rewrite H3; simpl.
rewrite cop_exchange2; rewrite cop_exchange3; rewrite cop_exchange2; assumption.
apply IHl; assumption.
intros Hrew; rewrite Hrew in *.
inversion H.
intros.
simpl.
destruct a0.
destruct p.
case_eq (coplanar a p p1 p0).
intros.
apply IHl.
intros.
apply H.
apply InA_cons_tl.
assumption.
intros.
assert (Hc:coplanar a p p1 p0=true).
apply H; apply InA_cons_hd; unfold eq3; left; simpl; split. reflexivity. split. reflexivity. reflexivity.
rewrite Hc in *.
inversion H0.
Qed.

Lemma test :
forall x x0 x1 A,
collinear x x0 x1 = false ->
collinear x x0 A = false \/ collinear x x1 A = false \/ collinear x0 x1 A = false.
Proof.
intros.
unfold collinear.
case_eq (eq_dec_u x x0).
intros.
rewrite e in *.
assert( HH18 := col_1 x0 x1).
rewrite HH18 in H.
inversion H.
case_eq (eq_dec_u x x1).
intros.
rewrite e in *.
assert( HH18 := col_1 x1 x0).
assert( HH19 := col_shift x1 x1 x0).
rewrite HH19 in HH18.
rewrite HH18 in H.
inversion H.
case_eq (eq_dec_u x0 x1).
intros.
rewrite e in *.
assert( HH18 := col_2 x x1).
rewrite HH18 in H.
inversion H.
intros.
destruct (a1_exist x x0).
destruct (a1_exist x x1).
destruct (a1_exist x0 x1).
simpl.
case_eq (incid_dec A x2).
case_eq (incid_dec A x3).
case_eq (incid_dec A x4).
intros.
destruct a.
destruct a0.
destruct a1.
clear H0 H1 H2.
assert( HH0 := uniqueness x A x2 x3 H6 i1 H8 i0).
destruct HH0.
rewrite H0 in *.
assert( HH0 := uniqueness x0 A x2 x4 H7 i1 H10 i).
destruct HH0.
rewrite H1 in *.
apply False_ind.
apply n1.
reflexivity.
rewrite H1 in *.
rewrite <-H0 in *.
generalize H.
unfold collinear.
case_eq (eq_dec_u x x0).
intros.
contradiction.
destruct (a1_exist x x0).
simpl.
case_eq (incid_dec x1 x5).
intros.
inversion H13.
intros.
destruct a.
assert( HH0 := uniqueness x x0 x4 x5 H6 H7 H14 H15).
destruct HH0.
contradiction.
rewrite H16 in *.
contradiction.
rewrite H0 in *.
generalize H.
unfold collinear.
case_eq (eq_dec_u x x0).
intros.
contradiction.
destruct (a1_exist x x0).
simpl.
case_eq (incid_dec x1 x5).
intros.
inversion H12.
intros.
destruct a.
assert( HH0 := uniqueness x x0 x3 x5 H6 H7 H13 H14).
destruct HH0.
contradiction.
rewrite H15 in *.
contradiction.
intros.
right.
right.
reflexivity.
intros.
right.
left.
reflexivity.
intros.
left.
reflexivity.
Qed.

Lemma matroid3_aux0_cop_bis_aux : forall a x y z a0,
collinear a x y = false ->
coplanar a x y z = true ->
coplanar a x y a0 = true ->
coplanar a0 x y z = true.
Proof.
intros.
assert( HH0 := cop_trans_bis_bis a x y z a0 H H0 H1).
rewrite cop_exchange2 in HH0.
rewrite cop_exchange3 in HH0.
rewrite cop_exchange1 in HH0.
assumption.
Qed.

Lemma matroid3_aux0_cop_bis_aux1 : forall a x y z a0, forall l,
(forall x0 y0 z0,
      InA eq3 (x0, y0, z0) (all_triples (a0 :: l)) -> coplanar a x0 y0 z0 = true) ->
collinear a x y = false ->
coplanar a x y z = true ->
InA eq3 (a0, x, y) (all_triples (a0 :: l)) \/
InA eq3 (a0, y, x) (all_triples (a0 :: l)) \/
InA eq3 (x, a0, y) (all_triples (a0 :: l)) \/
InA eq3 (x, y, a0) (all_triples (a0 :: l)) \/
InA eq3 (y, a0, x) (all_triples (a0 :: l)) \/
InA eq3 (y, x, a0) (all_triples (a0 :: l)) ->
coplanar a0 x y z = true.
Proof.
intros.
destruct H2.
assert( HH0 := H a0 x y H2).
rewrite cop_exchange3 in HH0.
rewrite cop_exchange2 in HH0.
apply matroid3_aux0_cop_bis_aux with (a:=a);assumption.
destruct H2. 
assert( HH0 := H a0 y x H2).
rewrite cop_exchange3 in HH0.
rewrite cop_exchange2 in HH0.
rewrite cop_exchange3 in HH0.
apply matroid3_aux0_cop_bis_aux with (a:=a);assumption.
destruct H2.
assert( HH0 := H x a0 y H2).
rewrite cop_exchange2 in HH0.
apply matroid3_aux0_cop_bis_aux with (a:=a);assumption.
destruct H2.
assert( HH0 := H x y a0 H2).
apply matroid3_aux0_cop_bis_aux with (a:=a);assumption.
destruct H2.
assert( HH0 := H y a0 x H2).
rewrite cop_exchange2 in HH0.
rewrite cop_exchange3 in HH0.
apply matroid3_aux0_cop_bis_aux with (a:=a);assumption.
assert( HH0 := H y x a0 H2).
rewrite cop_exchange3 in HH0.
apply matroid3_aux0_cop_bis_aux with (a:=a);assumption.
Qed.

Lemma matroid3_aux0_cop_bis_aux2 : forall a x y z a0, forall l,
(forall x0 y0 z0,
      InA eq3 (x0, y0, z0) (all_triples (a0 :: l)) -> coplanar a x0 y0 z0 = true) ->
InA eq x (a0 :: l) ->
InA eq y (a0 :: l) ->
InA eq z (a0 :: l) ->
InA eq a0 (a0 :: l) ->
collinear a x y = false ->
InA eq3 (x, y, z) (all_triples (a0 :: l)) \/
InA eq3 (x, z, y) (all_triples (a0 :: l)) \/
InA eq3 (y, x, z) (all_triples (a0 :: l)) \/
InA eq3 (y, z, x) (all_triples (a0 :: l)) \/
InA eq3 (z, x, y) (all_triples (a0 :: l)) \/
InA eq3 (z, y, x) (all_triples (a0 :: l)) ->
InA eq3 (a0, x, y) (all_triples (a0 :: l)) \/
InA eq3 (a0, y, x) (all_triples (a0 :: l)) \/
InA eq3 (x, a0, y) (all_triples (a0 :: l)) \/
InA eq3 (x, y, a0) (all_triples (a0 :: l)) \/
InA eq3 (y, a0, x) (all_triples (a0 :: l)) \/
InA eq3 (y, x, a0) (all_triples (a0 :: l)) ->
coplanar a0 x y z = true.
Proof.
intros.
destruct H5.
assert( HH0 := H x y z H5).
apply matroid3_aux0_cop_bis_aux1 with (a:=a) (l:=l);assumption.
destruct H5.
assert( HH0 := H x z y H5).
rewrite cop_exchange2 in HH0.
apply matroid3_aux0_cop_bis_aux1 with (a:=a) (l:=l);assumption.
destruct H5.
assert( HH0 := H y x z H5).
rewrite cop_exchange3 in HH0.
apply matroid3_aux0_cop_bis_aux1 with (a:=a) (l:=l);assumption.
destruct H5.
assert( HH0 := H y z x H5).
rewrite cop_exchange2 in HH0.
rewrite cop_exchange3 in HH0.
apply matroid3_aux0_cop_bis_aux1 with (a:=a) (l:=l);assumption.
destruct H5.
assert( HH0 := H z x y H5).
rewrite cop_exchange3 in HH0.
rewrite cop_exchange2 in HH0.
apply matroid3_aux0_cop_bis_aux1 with (a:=a) (l:=l);assumption.
assert( HH0 := H z y x H5).
rewrite cop_exchange2 in HH0.
rewrite cop_exchange3 in HH0.
rewrite cop_exchange2 in HH0.
apply matroid3_aux0_cop_bis_aux1 with (a:=a) (l:=l);assumption.
Qed.

(*
Lemma matroid3_aux0_cop_bis_aux3 : forall a x y z a0, forall l,
(forall x0 y0 z0 : t,
      InA eq3 (x0, y0, z0) (all_triples (a0 :: l)) -> coplanar a x0 y0 z0 = true) ->
InA eq x (a0 :: l) ->
InA eq y (a0 :: l) ->
InA eq z (a0 :: l) ->
InA eq a0 (a0 :: l) ->
collinear a x y = false \/ collinear a x z = false \/ collinear a z y = false ->
coplanar a0 x y z = true.
Proof.
intros.
destruct H4.
apply matroid3_aux0_cop_bis_aux2 with (a:=a) (l:=l); assumption.
destruct H4.
rewrite cop_exchange2.
apply matroid3_aux0_cop_bis_aux2 with (a:=a) (l:=l); assumption.
rewrite cop_exchange3.
rewrite cop_exchange2.
rewrite cop_exchange3.
apply matroid3_aux0_cop_bis_aux2 with (a0 :=a0) (x:=z) (y:=y) (z:=x) (a:=a) (l:=l); assumption.
Qed.*)

Lemma matroid3_aux0_cop_bis : forall l, forall a a0,
coplanar_with_all a (all_triples (a0 :: l)) = true ->
coplanar_with_all a0 (all_triples l) = true.
Proof.
intros.
destruct (eq_dec_u a a0).
rewrite e in *.
eapply coplanar_inclA with (all_triples (a0 :: l)).
apply all_triples_lemma.
assumption.

generalize (cop_caract a (all_triples (a0::l))); intros (HA,HB).
generalize (HA H); intros Hyp; clear H HA HB.
apply cop_caract.
intros.
apply InA_eq3_eq_all_triples in H.
case_eq (eq_dec_u x y).
intros.
rewrite e.
apply cop_2.
intros.
case_eq (eq_dec_u x z).
intros.
rewrite e.
rewrite cop_exchange3.
apply cop_3.
case_eq (eq_dec_u y z).
intros.
rewrite e.
apply cop_3.
intros.
case_eq (eq_dec_u a0 x).
intros.
rewrite e.
apply cop_1.
intros.
case_eq (eq_dec_u a0 y).
intros.
rewrite e.
rewrite cop_exchange3.
apply cop_1.
intros.
case_eq (eq_dec_u a0 z).
intros.
rewrite e.
rewrite cop_exchange1.
rewrite cop_exchange2.
apply cop_2.
clear H0 H1 H2 H3 H4.
case_eq (collinear x y z).
intros.
assert( HH0 := col_to_cop x y z a0 H0).
rewrite cop_exchange2 in HH0.
rewrite cop_exchange3 in HH0.
rewrite cop_exchange1 in HH0.
assumption.
intros.
assert( HH0 := test x y z a H0).
destruct H.
destruct H2.
assert( HH : InA eq x (a0 :: l)).
apply InA_cons_tl.
assumption.
assert( HH2 : InA eq y (a0 :: l)).
apply InA_cons_tl.
assumption.
assert( HH3 : InA eq z (a0 :: l)).
apply InA_cons_tl.
assumption.
assert( HH4 : InA eq a0 (a0 :: l)).
intuition.

destruct HH0.
rewrite col_exchange2 in H4.
rewrite col_exchange in H4.
assert( HH5 := InA_eq_eq3_all_triples x y z (a0 :: l) HH HH2 HH3 n0 n2 n1).
assert( HH6 := InA_eq_eq3_all_triples a0 x y (a0 :: l) HH4 HH HH2 n3 n4 n0).
apply matroid3_aux0_cop_bis_aux2 with (a:=a) (l:=l); assumption.
destruct H4.
rewrite col_exchange2 in H4.
rewrite col_exchange in H4.
assert( n2bis : ~ z[==]y).
intro.
rewrite H5 in n1.
apply n1.
reflexivity.
assert( HH5 := InA_eq_eq3_all_triples x z y (a0 :: l) HH HH3 HH2 n2 n0 n2bis).
assert( HH6 := InA_eq_eq3_all_triples a0 x z (a0 :: l) HH4 HH HH3 n3 n5 n2).
rewrite cop_exchange2.
apply matroid3_aux0_cop_bis_aux2 with (a:=a)(l:=l); assumption.
rewrite col_exchange2 in H4.
rewrite col_exchange in H4.
assert( n0bis : ~ y[==]x).
intro.
rewrite H5 in n0.
apply n0.
reflexivity.
assert( n2bis : ~ z[==]x).
intro.
rewrite H5 in n2.
apply n2.
reflexivity.
assert( HH5 := InA_eq_eq3_all_triples y z x (a0 :: l) HH2 HH3 HH n1 n0bis n2bis).
assert( HH6 := InA_eq_eq3_all_triples a0 y z (a0 :: l) HH4 HH2 HH3 n4 n5 n1).
rewrite cop_exchange3.
rewrite cop_exchange2.
apply matroid3_aux0_cop_bis_aux2 with (a:=a)(l:=l); assumption.
Qed.

End s_psohEquivCopWA_2.
