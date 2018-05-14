Require Export ProjectiveGeometry.Dev.p_equiv_col.

(*****************************************************************************)
(** Collinear with all **)


Section s_pEquivColWA_1.

Context `{PSLEU : ProjectiveStructureLEU}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

(*** Definition all_pairs ***)
Fixpoint all_pairs (l : list Point) : list (Point * Point) := 
match l with 
| nil => nil
| a :: reste => (map_monotonic (fun x:Point => (a,x)) reste) ++ all_pairs reste
end.

(*** Definition collinear_with_all ***)
Fixpoint collinear_with_all a l :=
match l with
| nil => true
| (b,c)::reste => if collinear a b c then collinear_with_all a reste else false
end.

Functional Scheme c_all_ind := Induction for collinear_with_all Sort Prop.

(*** Definition eq2 ***)
Definition eq2 X Y := 
(fst X)[==](fst Y) /\ (snd X)[==](snd Y)
\/(fst X)[==](snd Y) /\ (snd X)[==](fst Y).

End s_pEquivColWA_1.


Ltac destruct_all := match goal with [|- forall w: Point*Point, ?M] => 
  let w:= fresh in intros w; let x:=fresh "x" in let y:=fresh "y" in destruct w as [x y]  end.


Section s_pEquivColWA_2.

Context `{PSLEU : ProjectiveStructureLEU}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

Lemma eq2_dec : forall X Y, {eq2 X Y}+{~eq2 X Y}.
Proof.
repeat destruct_all.
destruct (eq_dec_u x x0); destruct (eq_dec_u y y0); destruct (eq_dec_u x y0); destruct (eq_dec_u y x0); unfold eq2; simpl; try solve [intuition].
Qed.

Lemma inclA_concat : forall l m,  inclA eq2 l (l++m).
Proof.
induction l.
simpl; unfold inclA; intros.
inversion H.
intros; simpl.
unfold inclA; intros.
destruct (eq2_dec x a).
apply InA_cons_hd; assumption.
inversion H.
subst.
apply False_ind; solve [intuition].
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma inclA_concat2 : forall   l m,  inclA eq2 m (l++m).
Proof.
induction l.
simpl; unfold inclA; solve [trivial].
intros; simpl.
unfold inclA; intros.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma all_pairs_lemma : forall a l, inclA eq2 (all_pairs l) (all_pairs (a::l)).
Proof.
induction l.
unfold inclA; simpl; solve [trivial].
simpl.
apply inclA_concat2 with (l:= (((a, a0)
   :: map_monotonic (fun x : Point => (a, x)) l))).
Qed.

Lemma collinear_app : forall a l m, collinear_with_all a l = true -> collinear_with_all a m = true -> 
collinear_with_all a (l++m) = true.
Proof.
induction l.
simpl.
solve [trivial].
simpl; intros.
destruct a0.
destruct (collinear a p p0).
apply IHl; assumption.
inversion H.
Qed.

Lemma col_inA_all : forall a b c m, collinear a b c = false -> InA eq2 (b,c) m -> collinear_with_all a m=true -> False.
Proof.
intros a b c m; elim m using c_all_ind.
intros; subst.
inversion H0.
intros; subst.
destruct (eq2_dec (b,c) (b0,c0)).
eapply H.
eassumption.
destruct e as [(f, g) | (f, g)]; simpl in f,g.
rewrite <- f in e1.
rewrite <- g in e1.
rewrite e1 in H0.
inversion H0.
rewrite <- f in e1.
rewrite <- g in e1.
rewrite <- col_shift in e1; rewrite col_exchange in e1.
rewrite e1 in H0.
inversion H0.
assumption.
assert (T:InA eq2 (b,c) reste).
inversion H1.
apply False_ind; solve [intuition].
assumption.
apply H; assumption.
intros; subst.
inversion H1.
Qed.

Lemma collinear_inclA : forall a l m, inclA eq2 l m -> collinear_with_all a m = true -> collinear_with_all a l = true.
Proof.
intros a l; elim l using c_all_ind.
intros; subst.
solve [trivial].
intros m y r Hl b c Hy Hcol IH z; elim z using c_all_ind.
intros; subst.
assert (T: InA eq2 (b,c) ((b,c)::r)).
apply InA_cons_hd.
unfold eq2; solve [intuition]. 
generalize (H (b,c) T); intros Hinv; inversion Hinv.
intros; subst.
eapply (IH ((b0,c0)::reste)).
unfold inclA; intros.
apply H0.
apply InA_cons_tl.
assumption.
simpl.
destruct (collinear a b0 c0).
assumption.
inversion e1.
intros; subst.
inversion H0.
intros; subst.
assert (InA eq2 (b,c) m).
apply H.
apply InA_cons_hd.
unfold eq2; solve [intuition].
apply False_ind.
eapply col_inA_all; eassumption.
Qed.

Lemma collinear_equal : 
forall a b l, a[==]b -> collinear_with_all a l = collinear_with_all b l. 
Proof.
intros a b l Hab.
elim l using c_all_ind.
solve [trivial].
intros; subst; simpl.
rewrite Hab in e1.
rewrite e1.
assumption.
intros; subst; simpl.
rewrite Hab in e1.
rewrite e1.
solve [trivial].
Qed.

Global Instance eq2_equiv : Equivalence eq2.
Proof.
split.
intros s; destruct s; unfold eq2; simpl; left ; split; reflexivity.
intros x y H; destruct x; destruct y; unfold eq2;  destruct H; simpl in *. 
left ; split; symmetry; solve [intuition].
right; split; symmetry; solve [intuition]. 
intros x y z Hxy Hyz; unfold eq2 in *; 
  destruct x; destruct y; destruct z ; 
  destruct Hxy as [(Hxy1,Hxy2) | (Hxy1,Hxy2)]; 
  destruct Hyz as [(Hyz1,Hyz2) | (Hyz1,Hyz2)]; simpl in *.
left; split. 
rewrite Hxy1; rewrite Hyz1; reflexivity.
rewrite Hxy2; rewrite Hyz2; reflexivity.
right; split.
rewrite Hxy1; rewrite Hyz1; reflexivity.
rewrite Hxy2; rewrite Hyz2; reflexivity.
right; split.
rewrite Hxy1; rewrite Hyz2; reflexivity.
rewrite Hxy2; rewrite Hyz1; reflexivity.
left; split.
rewrite Hxy1; rewrite Hyz2; reflexivity.
rewrite Hxy2; rewrite Hyz1; reflexivity.
Qed.

Global Instance eq2_InA : Proper (eq2 ==> (@equivlistA (Point*Point) eq2) ==> flip impl) (InA eq2).
Proof.
repeat red.
intros x y Hxy.
intros l m; revert l; elim m.
intros; inversion H0.
intros; subst.
rewrite H0.
rewrite Hxy.
assumption.
Qed.

Global Instance collinear_with_all_morph  : Proper (eq ==> @equivlistA (Point*Point) eq2 ==> (@Logic.eq bool)) collinear_with_all.
Proof.
repeat red.
intros p q Hpq x y Hxy.
case_eq (collinear_with_all p x).
case_eq (collinear_with_all q y).
solve [trivial].
intros HA HB.
assert (T : collinear_with_all q x = true).
rewrite <- (collinear_equal p q x Hpq).
assumption.
assert (U: inclA eq2 y x).
unfold inclA; intros t; destruct (Hxy t); solve [intuition].
assert (V:=collinear_inclA q _ _ U T).
rewrite V in *.
solve [intuition].
case_eq (collinear_with_all q y).
intros HA HB.
assert (T: collinear_with_all p y = true).
rewrite <- (collinear_equal q p y).
assumption.
symmetry; solve [intuition].
assert (U:inclA eq2 x y).
unfold inclA; intros t; destruct (Hxy t); solve [intuition].
assert (V:=collinear_inclA p x y U T).
rewrite V in *.
solve [intuition].
solve [trivial].
Qed.

Lemma InA_eq2_eq_all_pairs_aux : forall a C l, InA eq2 (a, C) (map_monotonic (fun x : Point => (a, x)) l) -> InA eq C l.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl.
intros HInA.
inversion HInA; subst.
destruct H0 as [H0 | H0].
simpl in H0.
destruct H0 as [H1 H2]; simpl in H1,H2.
rewrite H2.
apply InA_cons_hd; reflexivity.
simpl in H0.
destruct H0.
rewrite <- H.
rewrite H0.
apply InA_cons_hd; reflexivity.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma InA_eq2_eq_all_pairs_aux' : forall a C l, InA eq2 (C, a) (map_monotonic (fun x : Point => (a, x)) l) -> InA eq C l.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl.
intros HInA.
inversion HInA; subst.
destruct H0 as [H0 | H0].
destruct H0 as [H1 H2]; simpl in H1,H2.
rewrite H1.
apply InA_cons_hd; assumption. 
simpl in H0.
destruct H0.
rewrite <- H.
apply InA_cons_hd; reflexivity.
apply InA_cons_tl.
apply IHl.
assumption.
Qed.

Lemma InA_eq2_eq_all_pairs_aux2 : forall B C a l,
InA eq2 (B, C) (map_monotonic (fun x : Point => (a, x)) l)
-> ~ B[==]a -> ~C[==]a -> False.
Proof.
induction l.
simpl; intros Hv; inversion Hv.
simpl; intros Hv.
inversion Hv; subst.
destruct H0 as [H0 | H0].
destruct H0 as [H1 H2]; simpl in H1,H2.
intros; solve [intuition].
simpl in H0.
intros; solve [intuition].
apply IHl; assumption.
Qed.

Lemma InA_eq2_eq_all_pairs : forall B C l, InA eq2 (B,C) (all_pairs l) -> InA eq B l /\ InA eq C l.
Proof.
induction l; simpl.
intros Hx; inversion Hx.
intros.
apply InA_app_iff in H.
destruct H as [HA |HB].
destruct (eq_dec_u B a).
rewrite e in *.
destruct (eq_dec_u C a).
rewrite e0 in *.
split; apply InA_cons_hd; reflexivity.
split.
apply InA_cons_hd; reflexivity.
apply InA_cons_tl.
assert (f:eq2 (B,C) (a,C)).
unfold eq2; left; simpl; split; [assumption | reflexivity].
eapply InA_eq2_eq_all_pairs_aux; eassumption.
destruct (eq_dec_u C a).
split.
apply InA_cons_tl.
assert (f:eq2 (B,C) (B,a)).
unfold eq2; left; simpl; split; [reflexivity | assumption].
unfold map_monotonic in HA.
rewrite f in HA.
eapply InA_eq2_eq_all_pairs_aux'; eassumption.
rewrite e.
apply InA_cons_hd; reflexivity.
apply False_ind; eapply InA_eq2_eq_all_pairs_aux2; eassumption.
destruct (IHl HB).
split; apply InA_cons_tl; assumption.
Qed.

Lemma InA_eq2_map : forall a y l, InA eq y l -> InA eq2 (a, y) (map_monotonic (fun x : Point => (a, x)) l).
Proof.
induction l.
intros Hv; inversion Hv.
simpl; intros Hv.
inversion Hv; subst.
solve [intuition].
solve [intuition].
Qed.

Lemma InA_eq2_map2 : forall a y l, InA eq y l -> InA eq2 (y, a) (map_monotonic (fun x : Point => (a, x)) l).
Proof.
induction l.
intros Hv; inversion Hv.
simpl; intros Hv.
inversion Hv;subst.
unfold eq2;left;solve [intuition].
solve [intuition].
Qed.

Lemma InA_eq_eq2_all_pairs : forall x y l, InA eq x l -> InA eq y l -> ~(x[==]y) -> InA eq2 (x,y) (all_pairs l)
\/ InA eq2 (y,x) (all_pairs l).
Proof.
induction l.
intros Hy; inversion Hy.
intros;simpl.
destruct (eq_dec_u x a).
left.
assert (f:eq2 (x,y) (a,y)).
unfold eq2; simpl; left; split; solve [reflexivity | assumption].
rewrite f.
apply InA_app_iff.
left.
inversion H0;subst.
contradiction.
apply InA_eq2_map; assumption.
inversion H;subst.
apply False_ind; apply n; reflexivity.
inversion H0;subst.
right.
apply InA_app_iff.
left.
apply InA_eq2_map; assumption.
destruct (IHl H3 H4 H1).
left.
apply InA_app_iff.
right.
assumption.
right.
apply InA_app_iff.
right.
assumption.
Qed.

Lemma col_with_all_col : forall a l, collinear_with_all a l = true -> forall x y, InA eq2 (x,y) l -> collinear a x y = true.
Proof.
induction l.
simpl; intros.
inversion H0.
destruct a0.
simpl.
case_eq(collinear a p p0).
intros.
inversion H1; subst.
unfold eq2 in H3; simpl in H3 ; destruct H3 as [(H21, H22) | (H21,H22)]; simpl in *.
rewrite H21.
rewrite H22.
assumption.
rewrite H21.
rewrite H22.
rewrite col_shift.
rewrite col_exchange.
rewrite <- col_shift.
assumption.

apply IHl.
assumption.
assumption.
intros Hv; inversion Hv.
intros Hrew.
rewrite Hrew in H0.
inversion H0.
Qed.

Lemma contains_1_aux : forall A l,
collinear_with_all A l = false <-> exists B C, InA eq2 (B,C) l/\ collinear A B C= false.
Proof.
induction l.
intros; simpl; split.
intros; discriminate.
intros Hex; destruct Hex as [B [ C (HBC, Hcol)]].
inversion HBC.
simpl.
case_eq a.
intros.
case_eq (collinear A p p0).
intros.
split.
intros.
apply IHl in H1.
destruct H1 as [B [C (HIn, Hcol)]].
exists B.
exists C.
split.
apply InA_cons_tl; assumption.
assumption.
intros.
destruct H1 as [B [C (HBC,Hcol)]].
case_eq (eq2_dec (B,C) (p,p0)).
intros.
destruct e as [(e1, e2) | (e1,e2)]; simpl in *.
rewrite e1 in Hcol.
rewrite e2 in Hcol.
rewrite H0 in Hcol.
inversion Hcol.
rewrite e1 in Hcol.
rewrite e2 in Hcol.
rewrite col_shift in Hcol.
rewrite col_exchange in Hcol.
rewrite <- col_shift in Hcol.
rewrite H0 in Hcol.
inversion Hcol.

intros.
inversion HBC; subst.
apply False_ind; apply n; assumption.
apply IHl.
exists B.
exists C.
split.
assumption.
assumption.
intros.
split.
intros.
exists p.
exists p0.
split.
apply InA_cons_hd; reflexivity.
assumption.
solve [intuition].
Qed.

Lemma collinear_with_all_map : forall a l, collinear_with_all a (map_monotonic (fun x:Point => (a,x)) l)= true.
Proof.
induction l.
simpl; solve [trivial].
simpl.
unfold collinear.
destruct (eq_dec_u a a).
assumption.
apply False_ind; apply n; reflexivity.
Qed.

Lemma col_with_all_app : 
  forall a l m, collinear_with_all a (l++m) = false -> collinear_with_all a l = true -> collinear_with_all a m = false.
Proof.
induction l.
simpl; solve [trivial].
intros; simpl.
apply IHl.
simpl in H.
destruct a0.
case_eq (collinear a p p0);
intros Hrew; rewrite Hrew in H.
assumption.
simpl in H0.
destruct (collinear a p p0).
inversion Hrew.
inversion H0.
simpl in H0.
destruct a0.
case_eq (collinear a p p0); intros Hrew; rewrite Hrew in H0.
assumption.
inversion H0.
Qed.

Lemma col_with_all_map : forall a a0 l, (forall A B C : Point,
    InA eq A (a :: a0 :: l) ->
    InA eq B (a :: a0 :: l) ->
    InA eq C (a :: a0 :: l) -> collinear A B C = true) -> collinear_with_all a (map_monotonic (fun x: Point => (a0,x)) l)=true.
Proof.
induction l.
intros; simpl.
solve [trivial].
intros.
simpl.
assert (T:collinear a a0 a1=true).
apply H.
apply InA_cons_hd; reflexivity.
apply InA_cons_tl; apply InA_cons_hd; reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_hd; reflexivity.
rewrite T.
apply IHl.
intros; apply H.
inversion H0; subst.
apply InA_cons_hd; reflexivity.
inversion H4; subst.
apply InA_cons_tl; apply InA_cons_hd; reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; assumption.

inversion H1; subst.
apply InA_cons_hd; reflexivity.
inversion H4; subst.
apply InA_cons_tl; apply InA_cons_hd; reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; assumption.

inversion H2; subst.
apply InA_cons_hd; reflexivity.
inversion H4; subst.
apply InA_cons_tl; apply InA_cons_hd; reflexivity.
apply InA_cons_tl; apply InA_cons_tl; apply InA_cons_tl; assumption.
Qed.

Lemma forall_InA_collinear_with_all : 
forall a l, ( forall A B C : Point,
    InA eq A (a :: l) ->
    InA eq B (a :: l) -> InA eq C (a :: l) -> collinear A B C = true) ->
collinear_with_all a (all_pairs l) = false -> False.
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
eapply col_with_all_app. 
eassumption.
apply col_with_all_map.
intros; apply H; assumption.
Qed.

Lemma col_aux : forall a B C l, collinear_with_all a l = true -> InA eq2 (B,C) l\/InA eq2 (C,B) l -> collinear a B C = true.
Proof.
induction l.
simpl; intros HA HB.
destruct HB as [HB | HB]; inversion HB.
simpl; destruct a0.
case_eq (collinear a p p0).
intros.
destruct H1 as [H1 | H1].
inversion H1; subst.
simpl in H3; destruct H3 as [(H3a, H3b)| (H3a, H3b)]; simpl in H3a, H3b.
rewrite H3a, H3b.
assumption.
rewrite H3a, H3b.
rewrite col_shift.
rewrite col_exchange.
rewrite <- col_shift.
assumption.
apply IHl.
assumption.
left.
assumption.
inversion H1; subst.
simpl in H3; destruct H3 as [(H3a,H3b)|(H3a,H3b)]; simpl in H3a, H3b.
rewrite H3a, H3b.
rewrite col_shift; rewrite col_exchange; rewrite <- col_shift.
assumption.
rewrite H3a, H3b.
assumption.
apply IHl.
assumption.
right.
assumption.
intros HA HB; inversion HB.
Qed.

Lemma matroid3_aux0 : forall l, forall a a0,
collinear_with_all a (all_pairs (a0 :: l)) = true ->
collinear_with_all a (all_pairs l) = true.
Proof.
intros.
simpl in *.
assert (T:inclA eq2 (all_pairs l) (map_monotonic (fun x : Point => (a0, x)) l ++ all_pairs l)).
apply inclA_concat2.
eapply collinear_inclA.
eassumption.
assumption.
Qed.

Lemma col_caract : forall a l,
collinear_with_all a l = true <-> forall x y, InA eq2 (x,y) l -> collinear a x y = true.
Proof.
induction l.
split.
intros H x y H'; inversion H'.
intros; simpl; solve [trivial].
split.
intros.
simpl in H.
destruct a0.
case_eq (collinear a p p0).
intros Hrew; rewrite Hrew in *.
inversion H0; subst.
destruct H2 as [(H2a,H2b) | (H2a,H2b)]; simpl in H2a,H2b.
rewrite H2a, H2b.
assumption.
rewrite H2a, H2b.
rewrite col_shift.
rewrite col_exchange.
rewrite <- col_shift.
assumption.
apply IHl; assumption.
intros Hrew; rewrite Hrew in *.
inversion H.
intros.
simpl.
destruct a0.
case_eq (collinear a p p0).
intros.
apply IHl.
intros.
apply H.
apply InA_cons_tl.
assumption.
intros.
assert (Hc:collinear a p p0=true).
apply H; apply InA_cons_hd; unfold eq2; left; simpl; split; reflexivity.
rewrite Hc in *.
inversion H0.
Qed. 

Lemma matroid3_aux0_bis : forall l, forall a a0,
collinear_with_all a (all_pairs (a0 :: l)) = true ->
collinear_with_all a0 (all_pairs l) = true.
Proof.
intros.
destruct (eq_dec_u a a0).
rewrite e in *.
eapply collinear_inclA with (all_pairs (a0 :: l)).
apply all_pairs_lemma.
assumption.

generalize (col_caract a (all_pairs (a0::l))); intros (HA,HB).
generalize (HA H); intros Hyp; clear H HA HB.
apply col_caract.
intros.
eapply col_trans_bis with a.
eassumption.
apply Hyp.
generalize (InA_eq2_eq_all_pairs x y l H); intros HInA.
simpl;apply InA_app_iff.
left.
apply InA_eq2_map; solve [intuition].
apply Hyp.
generalize (InA_eq2_eq_all_pairs x y l H); intros HInA.
simpl;apply InA_app_iff.
left.
apply InA_eq2_map; solve [intuition].
Qed.

End s_pEquivColWA_2.