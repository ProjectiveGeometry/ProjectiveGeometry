Require Export ProjectiveGeometry.Dev.basic_rank_space_list.

Ltac clear_ineg_rk :=
repeat match goal with
| H : rk _ >= _ |- _ => clear H
| H : rk _ <= _ |- _ => clear H
end.

Ltac clear_all_rk :=
repeat match goal with
| H : rk _ = _ |- _ => clear H
| H : rk _ >= _ |- _ => clear H
| H : rk _ <= _ |- _ => clear H
end.

Ltac equalize_pts :=
repeat match goal with
| H : rk (?X0 :: ?X1 :: nil) = 1 |- _ => 
          let HH := fresh in assert(HH := couple_rk2 X0 X1 H);clear H;rewrite HH
end.

Ltac eliminate_hyps :=
repeat match goal with
| H : rk ?X = _, H0 : rk ?X >= _ |- _ => clear H0
| H : rk ?X = _, H0 : rk ?X <= _ |- _ => clear H0
| H : rk ?X >= _, H0 : rk ?X >= _ |- _ => clear H
| H : rk ?X <= _, H0 : rk ?X <= _ |- _ => clear H
| H : rk ?X >= ?Y, H0 : rk ?X <= ?Y |- _ =>  let HH := fresh in assert(HH : rk X = Y) by (omega)
end.

Lemma le_S_sym : forall n m : nat,
n >= S m -> n >= m.
Proof.
intros.
intuition.
Qed.

Lemma eq_to_ge : forall n m : nat,
n = m -> n >= m.
Proof.
intros.
intuition.
Qed.

Lemma eq_to_le : forall n m : nat,
n = m -> n <= m.
Proof.
intros.
intuition.
Qed.

Ltac solve_hyps_max H H0 :=
solve[apply matroid1_b_useful;simpl;repeat constructor
|apply rk_upper_dim
|apply Nat.eq_le_incl;apply H
|apply Nat.eq_le_incl;apply eq_sym;apply H
|apply H0
|apply le_S;apply H0
|apply le_S;apply le_S;apply H0
|apply le_S;apply le_S;apply le_S;apply H0
].

Ltac solve_hyps_min H H0:=
solve[apply matroid1_b_useful2;simpl;repeat constructor
|apply matroid1_a
|apply Nat.eq_le_incl;apply H
|apply Nat.eq_le_incl;apply eq_sym;apply H
|apply H0
|apply le_S_sym;apply H0
|apply le_S_sym;apply le_S_sym;apply H0
|apply le_S_sym;apply le_S_sym;apply le_S_sym;apply H0
].

Lemma l1_scheme : forall P1 P2 : Point,
                  forall P3 P4 : Point,
                  forall P5 : Point,
                  rk (P1 :: P2 :: P5 :: nil) = 3 ->
                  rk (P1 :: P3 :: P5 :: nil) = 2 ->
                  rk (P2 :: P4 :: P5 :: nil) = 2 ->
                  rk (P3 :: P5 :: nil) = 2 ->
                  rk (P4 :: P5 :: nil) = 2  ->  rk (P3 :: P4 :: P5 :: nil) = 3.
Proof.
intros P1 P2 P3 P4 P5 HP1P2P5eq HP1P3P5eq HP2P4P5eq HP3P5eq HP4P5eq.

try clear HP1P2m;assert(HP1P2m : rk(P1 :: P2 :: nil) >= 2).
{
	try assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M).
	try assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: nil) (P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P5 :: nil) ((P1 :: P2 :: nil) ++ (P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5mtmp;try rewrite HT2 in HP1P2P5mtmp.
	assert(HT := rule_2 (P1 :: P2 :: nil) (P5 :: nil) (nil) 3 0 1 HP1P2P5mtmp Hmtmp HP5Mtmp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3).
{
	try assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5M;assert(HP1P2P3P4P5M : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) <= 3).
{
	try assert(HP1P3P5Mtmp : rk(P1 :: P3 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P3P5eq HP1P3P5M).
	try assert(HP2P4P5Mtmp : rk(P2 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP2P4P5eq HP2P4P5M).
	try assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m).
	assert(Hincl : incl (P5 :: nil) (list_inter (P1 :: P3 :: P5 :: nil) (P2 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P3 :: P5 :: P2 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P5 :: P2 :: P4 :: P5 :: nil) ((P1 :: P3 :: P5 :: nil) ++ (P2 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P3 :: P5 :: nil) (P2 :: P4 :: P5 :: nil) (P5 :: nil) 2 2 1 HP1P3P5Mtmp HP2P4P5Mtmp HP5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P5m;assert(HP2P5m : rk(P2 :: P5 :: nil) >= 2).
{
	try assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M).
	try assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P5 :: nil) ((P1 :: nil) ++ (P2 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5mtmp;try rewrite HT2 in HP1P2P5mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P5 :: nil) (nil) 3 0 1 HP1P2P5mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}

try clear HP2P3P4P5M;assert(HP2P3P4P5M : rk(P2 :: P3 :: P4 :: P5 :: nil) <= 3).
{
	try assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M).
	try assert(HP2P4P5Mtmp : rk(P2 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP2P4P5eq HP2P4P5M).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: nil) (P2 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P4 :: P5 :: nil) (P3 :: P2 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P2 :: P4 :: P5 :: nil) ((P3 :: nil) ++ (P2 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: nil) (P2 :: P4 :: P5 :: nil) (nil) 1 2 0 HP3Mtmp HP2P4P5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P4P5m;assert(HP2P3P4P5m : rk(P2 :: P3 :: P4 :: P5 :: nil) >= 2).
{
	try assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P3 :: P4 :: P5 :: nil) 2 2 HP2P5mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P4P5m;assert(HP2P3P4P5m : rk(P2 :: P3 :: P4 :: P5 :: nil) >= 3).
{
	try assert(HP1P3P5Mtmp : rk(P1 :: P3 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P3P5eq HP1P3P5M).
	try assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m).
	try assert(HP3P5mtmp : rk(P3 :: P5 :: nil) >= 2) by (solve_hyps_min HP3P5eq HP3P5m).
	assert(Hincl : incl (P3 :: P5 :: nil) (list_inter (P1 :: P3 :: P5 :: nil) (P2 :: P3 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P3 :: P5 :: P2 :: P3 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P5 :: P2 :: P3 :: P4 :: P5 :: nil) ((P1 :: P3 :: P5 :: nil) ++ (P2 :: P3 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5mtmp;try rewrite HT2 in HP1P2P3P4P5mtmp.
	assert(HT := rule_4 (P1 :: P3 :: P5 :: nil) (P2 :: P3 :: P4 :: P5 :: nil) (P3 :: P5 :: nil) 3 2 2 HP1P2P3P4P5mtmp HP3P5mtmp HP1P3P5Mtmp Hincl); apply HT.
}

try clear HP3P4P5m;assert(HP3P4P5m : rk(P3 :: P4 :: P5 :: nil) >= 2).
{
	try assert(HP3P5mtmp : rk(P3 :: P5 :: nil) >= 2) by (solve_hyps_min HP3P5eq HP3P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P5 :: nil) (P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P5 :: nil) (P3 :: P4 :: P5 :: nil) 2 2 HP3P5mtmp Hcomp Hincl); apply HT.
}

try clear HP3P4P5m;assert(HP3P4P5m : rk(P3 :: P4 :: P5 :: nil) >= 3).
{
	try assert(HP2P4P5Mtmp : rk(P2 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP2P4P5eq HP2P4P5M).
	try assert(HP2P3P4P5mtmp : rk(P2 :: P3 :: P4 :: P5 :: nil) >= 3) by (solve_hyps_min HP2P3P4P5eq HP2P3P4P5m).
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P2 :: P4 :: P5 :: nil) (P3 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P3 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P5 :: P3 :: P4 :: P5 :: nil) ((P2 :: P4 :: P5 :: nil) ++ (P3 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P4P5mtmp;try rewrite HT2 in HP2P3P4P5mtmp.
	assert(HT := rule_4 (P2 :: P4 :: P5 :: nil) (P3 :: P4 :: P5 :: nil) (P4 :: P5 :: nil) 3 2 2 HP2P3P4P5mtmp HP4P5mtmp HP2P4P5Mtmp Hincl); apply HT.
}

assert(rk(P3 :: P4 :: P5 ::  nil) <= 3) by (clear_ineg_rk;try omega;try apply rk_upper_dim;try solve[apply matroid1_b_useful;simpl;intuition]).
assert(rk(P3 :: P4 :: P5 ::  nil) >= 1) by (clear_ineg_rk;try omega;try solve[apply matroid1_b_useful2;simpl;intuition]).
omega.
Qed.

Lemma rABOo_scheme : forall P1 P2 : Point,
                     forall P3 P4 : Point,
                     rk (P1 :: P2 :: P3 :: P4 :: nil) >= 4 ->
                     forall P5 : Point,
                     rk (P3 :: P4 :: P5 :: nil) = 2 ->
                     rk (P3 :: P5 :: nil) = 2 -> rk (P1 :: P2 :: P3 :: P5 :: nil) >= 4.
Proof.
intros P1 P2 P3 P4 HP1P2P3P4m P5 HP3P4P5eq HP3P5eq. 

try clear HP1P2P3m;assert(HP1P2P3m : rk(P1 :: P2 :: P3 :: nil) >= 3).
{
	try assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M).
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: P3 :: nil) (P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4mtmp;try rewrite HT2 in HP1P2P3P4mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: nil) (P4 :: nil) (nil) 4 0 1 HP1P2P3P4mtmp Hmtmp HP4Mtmp Hincl); apply HT.
}

try clear HP2P3P4m;assert(HP2P3P4m : rk(P2 :: P3 :: P4 :: nil) >= 3).
{
	try assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M).
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P3 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) ((P1 :: nil) ++ (P2 :: P3 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4mtmp;try rewrite HT2 in HP1P2P3P4mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P3 :: P4 :: nil) (nil) 4 0 1 HP1P2P3P4mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}

try clear HP3P4m;assert(HP3P4m : rk(P3 :: P4 :: nil) >= 2).
{
	try assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M).
	try assert(HP2P3P4mtmp : rk(P2 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP2P3P4eq HP2P3P4m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P3 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P4 :: nil) (P2 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P4 :: nil) ((P2 :: nil) ++ (P3 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P4mtmp;try rewrite HT2 in HP2P3P4mtmp.
	assert(HT := rule_4 (P2 :: nil) (P3 :: P4 :: nil) (nil) 3 0 1 HP2P3P4mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}

try clear HP1P2m;assert(HP1P2m : rk(P1 :: P2 :: nil) >= 2).
{
	try assert(HP3P4Mtmp : rk(P3 :: P4 :: nil) <= 2) by (solve_hyps_max HP3P4eq HP3P4M).
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: nil) (P3 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) ((P1 :: P2 :: nil) ++ (P3 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4mtmp;try rewrite HT2 in HP1P2P3P4mtmp.
	assert(HT := rule_2 (P1 :: P2 :: nil) (P3 :: P4 :: nil) (nil) 4 0 2 HP1P2P3P4mtmp Hmtmp HP3P4Mtmp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 4).
{
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P5m;assert(HP1P2P3P5m : rk(P1 :: P2 :: P3 :: P5 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P5m;assert(HP1P2P3P5m : rk(P1 :: P2 :: P3 :: P5 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P5m;assert(HP1P2P3P5m : rk(P1 :: P2 :: P3 :: P5 :: nil) >= 4).
{
	try assert(HP3P4P5Mtmp : rk(P3 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP3P4P5eq HP3P4P5M).
	try assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m).
	try assert(HP3P5mtmp : rk(P3 :: P5 :: nil) >= 2) by (solve_hyps_min HP3P5eq HP3P5m).
	assert(Hincl : incl (P3 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: nil) (P3 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P3 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P3 :: P4 :: P5 :: nil) ((P1 :: P2 :: P3 :: P5 :: nil) ++ (P3 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5mtmp;try rewrite HT2 in HP1P2P3P4P5mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: P5 :: nil) (P3 :: P4 :: P5 :: nil) (P3 :: P5 :: nil) 4 2 2 HP1P2P3P4P5mtmp HP3P5mtmp HP3P4P5Mtmp Hincl); apply HT.
}

assert(rk(P1 :: P2 :: P3 :: P5 ::  nil) <= 4) by (clear_ineg_rk;try omega;try apply rk_upper_dim;try solve[apply matroid1_b_useful;simpl;intuition]).
assert(rk(P1 :: P2 :: P3 :: P5 ::  nil) >= 1) by (clear_ineg_rk;try omega;try solve[apply matroid1_b_useful2;simpl;intuition]).
omega.
Qed.

Lemma rk_line_unification : forall P1 P2 P3,
                            rk(P1 :: P2 :: nil) = 2 -> rk(P1 :: P3 :: nil) = 2 ->
                            rk(P2 :: P3 :: nil) = 2 -> rk(P1 :: P2 :: P3 :: nil) <= 2 ->
                            rk(P1 :: P2 :: P3 :: nil) = 2.
Proof.
intros P1 P2 P3 HP1P2eq HP1P3eq HP2P3eq HP1P2P3eq.

try clear HP1P2P3m;assert(HP1P2P3m : rk(P1 :: P2 :: P3 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

assert(rk(P1 :: P2 :: P3 ::  nil) <= 3) by (clear_ineg_rk;try omega;try apply rk_upper_dim;try solve[apply matroid1_b_useful;simpl;intuition]).
assert(rk(P1 :: P2 :: P3 ::  nil) >= 1) by (clear_ineg_rk;try omega;try solve[apply matroid1_b_useful2;simpl;intuition]).
omega.
Qed.

Lemma Desargues : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10,
rk(P1 :: P4 :: P7 :: nil) = 2 -> rk(P2 :: P5 :: P7 :: nil) = 2 -> rk(P3 :: P6 :: P7 :: nil) = 2 -> 
rk(P4 :: P5 :: P6 :: nil) = 3 -> rk(P1 :: P2 :: P3 :: nil) = 3 ->
rk(P1 :: P2 :: P3 :: P4 :: nil) = 4 -> 
rk(P4 :: P5 :: P10 :: nil) = 2 -> rk(P1 :: P2 :: P10 :: nil) = 2 ->
rk(P4 :: P6 :: P9 :: nil) = 2 -> rk(P1 :: P3 :: P9 :: nil) = 2 ->
rk(P5 :: P6 :: P8 :: nil) = 2 -> rk(P2 :: P3 :: P8 :: nil) = 2 ->
rk(P1 :: P4 :: nil) = 2 -> rk(P3 :: P6 :: nil) = 2 -> rk(P2 :: P5 :: nil) = 2 ->
rk (P8 :: P9 :: P10 :: nil) = 2.
Proof.
intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 HP1P4P7eq HP2P5P7eq HP3P6P7eq HP4P5P6eq HP1P2P3eq HP1P2P3P4eq HP4P5P10eq HP1P2P10eq HP4P6P9eq HP1P3P9eq HP5P6P8eq HP2P3P8eq HP1P4eq HP3P6eq HP2P5eq. 

try clear HP1P2m;assert(HP1P2m : rk(P1 :: P2 :: nil) >= 2).
{
	try assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M).
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: nil) (P3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: nil) ((P1 :: P2 :: nil) ++ (P3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3mtmp;try rewrite HT2 in HP1P2P3mtmp.
	assert(HT := rule_2 (P1 :: P2 :: nil) (P3 :: nil) (nil) 3 0 1 HP1P2P3mtmp Hmtmp HP3Mtmp Hincl); apply HT.
}

try clear HP1P2P3P8P10m;assert(HP1P2P3P8P10m : rk(P1 :: P2 :: P3 :: P8 :: P10 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P8P10m;assert(HP1P2P3P8P10m : rk(P1 :: P2 :: P3 :: P8 :: P10 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P8P10M;assert(HP1P2P3P8P10M : rk(P1 :: P2 :: P3 :: P8 :: P10 :: nil) <= 3).
{
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP1P2P10Mtmp : rk(P1 :: P2 :: P10 :: nil) <= 2) by (solve_hyps_max HP1P2P10eq HP1P2P10M).
	try assert(HP2mtmp : rk(P2 :: nil) >= 1) by (solve_hyps_min HP2eq HP2m).
	assert(Hincl : incl (P2 :: nil) (list_inter (P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P10 :: nil) (P2 :: P3 :: P8 :: P1 :: P2 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P8 :: P1 :: P2 :: P10 :: nil) ((P2 :: P3 :: P8 :: nil) ++ (P1 :: P2 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P10 :: nil) (P2 :: nil) 2 2 1 HP2P3P8Mtmp HP1P2P10Mtmp HP2mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP1P3m;assert(HP1P3m : rk(P1 :: P3 :: nil) >= 2).
{
	try assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M).
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: nil) (P2 :: P1 :: P3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P3 :: nil) ((P2 :: nil) ++ (P1 :: P3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3mtmp;try rewrite HT2 in HP1P2P3mtmp.
	assert(HT := rule_4 (P2 :: nil) (P1 :: P3 :: nil) (nil) 3 0 1 HP1P2P3mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}

try clear HP1P2P3P8P9P10m;assert(HP1P2P3P8P9P10m : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P8P9P10m;assert(HP1P2P3P8P9P10m : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P8P9P10M;assert(HP1P2P3P8P9P10M : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) <= 3).
{
	try assert(HP1P3P9Mtmp : rk(P1 :: P3 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P3P9eq HP1P3P9M).
	try assert(HP1P2P3P8P10Mtmp : rk(P1 :: P2 :: P3 :: P8 :: P10 :: nil) <= 3) by (solve_hyps_max HP1P2P3P8P10eq HP1P2P3P8P10M).
	try assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m).
	assert(Hincl : incl (P1 :: P3 :: nil) (list_inter (P1 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) (P1 :: P3 :: P9 :: P1 :: P2 :: P3 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P9 :: P1 :: P2 :: P3 :: P8 :: P10 :: nil) ((P1 :: P3 :: P9 :: nil) ++ (P1 :: P2 :: P3 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil) (P1 :: P3 :: nil) 2 3 2 HP1P3P9Mtmp HP1P2P3P8P10Mtmp HP1P3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP4P5m;assert(HP4P5m : rk(P4 :: P5 :: nil) >= 2).
{
	try assert(HP6Mtmp : rk(P6 :: nil) <= 1) by (solve_hyps_max HP6eq HP6M).
	try assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: P5 :: nil) (P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: nil) ((P4 :: P5 :: nil) ++ (P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6mtmp;try rewrite HT2 in HP4P5P6mtmp.
	assert(HT := rule_2 (P4 :: P5 :: nil) (P6 :: nil) (nil) 3 0 1 HP4P5P6mtmp Hmtmp HP6Mtmp Hincl); apply HT.
}

try clear HP4P5P6P8P9m;assert(HP4P5P6P8P9m : rk(P4 :: P5 :: P6 :: P8 :: P9 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P6P8P9m;assert(HP4P5P6P8P9m : rk(P4 :: P5 :: P6 :: P8 :: P9 :: nil) >= 3).
{
	try assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P6P8P9M;assert(HP4P5P6P8P9M : rk(P4 :: P5 :: P6 :: P8 :: P9 :: nil) <= 3).
{
	try assert(HP5P6P8Mtmp : rk(P5 :: P6 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P8eq HP5P6P8M).
	try assert(HP4P6P9Mtmp : rk(P4 :: P6 :: P9 :: nil) <= 2) by (solve_hyps_max HP4P6P9eq HP4P6P9M).
	try assert(HP6mtmp : rk(P6 :: nil) >= 1) by (solve_hyps_min HP6eq HP6m).
	assert(Hincl : incl (P6 :: nil) (list_inter (P5 :: P6 :: P8 :: nil) (P4 :: P6 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: P9 :: nil) (P5 :: P6 :: P8 :: P4 :: P6 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P8 :: P4 :: P6 :: P9 :: nil) ((P5 :: P6 :: P8 :: nil) ++ (P4 :: P6 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: P6 :: P8 :: nil) (P4 :: P6 :: P9 :: nil) (P6 :: nil) 2 2 1 HP5P6P8Mtmp HP4P6P9Mtmp HP6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP4P5P6P8M;assert(HP4P5P6P8M : rk(P4 :: P5 :: P6 :: P8 :: nil) <= 3).
{
	try assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M).
	try assert(HP5P6P8Mtmp : rk(P5 :: P6 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P8eq HP5P6P8M).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: nil) (P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P8 :: nil) ((P4 :: nil) ++ (P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: nil) (P5 :: P6 :: P8 :: nil) (nil) 1 2 0 HP4Mtmp HP5P6P8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP4P5P6P8m;assert(HP4P5P6P8m : rk(P4 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P6P8m;assert(HP4P5P6P8m : rk(P4 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	try assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P7m;assert(HP1P2P3P4P7m : rk(P1 :: P2 :: P3 :: P4 :: P7 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P7m;assert(HP1P2P3P4P7m : rk(P1 :: P2 :: P3 :: P4 :: P7 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P7m;assert(HP1P2P3P4P7m : rk(P1 :: P2 :: P3 :: P4 :: P7 :: nil) >= 4).
{
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3m;assert(HP2P3m : rk(P2 :: P3 :: nil) >= 2).
{
	try assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M).
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: nil) ((P1 :: nil) ++ (P2 :: P3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3mtmp;try rewrite HT2 in HP1P2P3mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P3 :: nil) (nil) 3 0 1 HP1P2P3mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}

try clear HP2P3P7m;assert(HP2P3P7m : rk(P2 :: P3 :: P7 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P7 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P7m;assert(HP2P3P7m : rk(P2 :: P3 :: P7 :: nil) >= 3).
{
	try assert(HP1P4P7Mtmp : rk(P1 :: P4 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P4P7eq HP1P4P7M).
	try assert(HP1P2P3P4P7mtmp : rk(P1 :: P2 :: P3 :: P4 :: P7 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P7eq HP1P2P3P4P7m).
	try assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m).
	assert(Hincl : incl (P7 :: nil) (list_inter (P2 :: P3 :: P7 :: nil) (P1 :: P4 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P7 :: nil) (P2 :: P3 :: P7 :: P1 :: P4 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P7 :: P1 :: P4 :: P7 :: nil) ((P2 :: P3 :: P7 :: nil) ++ (P1 :: P4 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P7mtmp;try rewrite HT2 in HP1P2P3P4P7mtmp.
	assert(HT := rule_2 (P2 :: P3 :: P7 :: nil) (P1 :: P4 :: P7 :: nil) (P7 :: nil) 4 1 2 HP1P2P3P4P7mtmp HP7mtmp HP1P4P7Mtmp Hincl); apply HT.
}

try clear HP2P3P5P7P8m;assert(HP2P3P5P7P8m : rk(P2 :: P3 :: P5 :: P7 :: P8 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P7 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P5P7P8m;assert(HP2P3P5P7P8m : rk(P2 :: P3 :: P5 :: P7 :: P8 :: nil) >= 3).
{
	try assert(HP2P3P7mtmp : rk(P2 :: P3 :: P7 :: nil) >= 3) by (solve_hyps_min HP2P3P7eq HP2P3P7m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P7 :: nil) (P2 :: P3 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P7 :: nil) (P2 :: P3 :: P5 :: P7 :: P8 :: nil) 3 3 HP2P3P7mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P5P7P8M;assert(HP2P3P5P7P8M : rk(P2 :: P3 :: P5 :: P7 :: P8 :: nil) <= 3).
{
	try assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M).
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP2mtmp : rk(P2 :: nil) >= 1) by (solve_hyps_min HP2eq HP2m).
	assert(Hincl : incl (P2 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P2 :: P3 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P2 :: P3 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P2 :: P3 :: P8 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P2 :: P3 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P5 :: P7 :: nil) (P2 :: P3 :: P8 :: nil) (P2 :: nil) 2 2 1 HP2P5P7Mtmp HP2P3P8Mtmp HP2mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P5P8m;assert(HP2P3P5P8m : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P5P8M;assert(HP2P3P5P8M : rk(P2 :: P3 :: P5 :: P8 :: nil) <= 3).
{
	try assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M).
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: nil) (P2 :: P3 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P8 :: nil) (P5 :: P2 :: P3 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P2 :: P3 :: P8 :: nil) ((P5 :: nil) ++ (P2 :: P3 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: nil) (P2 :: P3 :: P8 :: nil) (nil) 1 2 0 HP5Mtmp HP2P3P8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P5P8m;assert(HP2P3P5P8m : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 3).
{
	try assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M).
	try assert(HP2P3P5P7P8mtmp : rk(P2 :: P3 :: P5 :: P7 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P3P5P7P8eq HP2P3P5P7P8m).
	try assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m).
	assert(Hincl : incl (P2 :: P5 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P2 :: P3 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P2 :: P3 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P2 :: P3 :: P5 :: P8 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P2 :: P3 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P5P7P8mtmp;try rewrite HT2 in HP2P3P5P7P8mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P7 :: nil) (P2 :: P3 :: P5 :: P8 :: nil) (P2 :: P5 :: nil) 3 2 2 HP2P3P5P7P8mtmp HP2P5mtmp HP2P5P7Mtmp Hincl); apply HT.
}

try clear HP5P8m;assert(HP5P8m : rk(P5 :: P8 :: nil) >= 2).
{
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP2P3P5P8mtmp : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P3P5P8eq HP2P3P5P8m).
	try assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m).
	assert(Hincl : incl (P8 :: nil) (list_inter (P2 :: P3 :: P8 :: nil) (P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P8 :: nil) (P2 :: P3 :: P8 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P8 :: P5 :: P8 :: nil) ((P2 :: P3 :: P8 :: nil) ++ (P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P5P8mtmp;try rewrite HT2 in HP2P3P5P8mtmp.
	assert(HT := rule_4 (P2 :: P3 :: P8 :: nil) (P5 :: P8 :: nil) (P8 :: nil) 3 1 2 HP2P3P5P8mtmp HP8mtmp HP2P3P8Mtmp Hincl); apply HT.
}

try clear HP4P5P8m;assert(HP4P5P8m : rk(P4 :: P5 :: P8 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8m;assert(HP4P5P8m : rk(P4 :: P5 :: P8 :: nil) >= 3).
{
	try assert(HP5P6P8Mtmp : rk(P5 :: P6 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P8eq HP5P6P8M).
	try assert(HP4P5P6P8mtmp : rk(P4 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P6P8eq HP4P5P6P8m).
	try assert(HP5P8mtmp : rk(P5 :: P8 :: nil) >= 2) by (solve_hyps_min HP5P8eq HP5P8m).
	assert(Hincl : incl (P5 :: P8 :: nil) (list_inter (P4 :: P5 :: P8 :: nil) (P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: P8 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P8 :: P5 :: P6 :: P8 :: nil) ((P4 :: P5 :: P8 :: nil) ++ (P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8mtmp;try rewrite HT2 in HP4P5P6P8mtmp.
	assert(HT := rule_2 (P4 :: P5 :: P8 :: nil) (P5 :: P6 :: P8 :: nil) (P5 :: P8 :: nil) 3 2 2 HP4P5P6P8mtmp HP5P8mtmp HP5P6P8Mtmp Hincl); apply HT.
}

try clear HP4P5P8P9m;assert(HP4P5P8P9m : rk(P4 :: P5 :: P8 :: P9 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: P9 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9m;assert(HP4P5P8P9m : rk(P4 :: P5 :: P8 :: P9 :: nil) >= 3).
{
	try assert(HP4P5P8mtmp : rk(P4 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P8eq HP4P5P8m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P8 :: nil) (P4 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P8 :: nil) (P4 :: P5 :: P8 :: P9 :: nil) 3 3 HP4P5P8mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9M;assert(HP4P5P8P9M : rk(P4 :: P5 :: P8 :: P9 :: nil) <= 3).
{
	try assert(HP4P5P6P8P9Mtmp : rk(P4 :: P5 :: P6 :: P8 :: P9 :: nil) <= 3) by (solve_hyps_max HP4P5P6P8P9eq HP4P5P6P8P9M).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P8 :: P9 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P4 :: P5 :: P8 :: P9 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil) 3 3 HP4P5P6P8P9Mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9P10m;assert(HP4P5P8P9P10m : rk(P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9P10m;assert(HP4P5P8P9P10m : rk(P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 3).
{
	try assert(HP4P5P8mtmp : rk(P4 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P8eq HP4P5P8m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P8 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P8 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil) 3 3 HP4P5P8mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9P10M;assert(HP4P5P8P9P10M : rk(P4 :: P5 :: P8 :: P9 :: P10 :: nil) <= 3).
{
	try assert(HP4P5P8P9Mtmp : rk(P4 :: P5 :: P8 :: P9 :: nil) <= 3) by (solve_hyps_max HP4P5P8P9eq HP4P5P8P9M).
	try assert(HP4P5P10Mtmp : rk(P4 :: P5 :: P10 :: nil) <= 2) by (solve_hyps_max HP4P5P10eq HP4P5P10M).
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P4 :: P5 :: P8 :: P9 :: nil) (P4 :: P5 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P8 :: P9 :: P10 :: nil) (P4 :: P5 :: P8 :: P9 :: P4 :: P5 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P8 :: P9 :: P4 :: P5 :: P10 :: nil) ((P4 :: P5 :: P8 :: P9 :: nil) ++ (P4 :: P5 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P5 :: P8 :: P9 :: nil) (P4 :: P5 :: P10 :: nil) (P4 :: P5 :: nil) 3 2 2 HP4P5P8P9Mtmp HP4P5P10Mtmp HP4P5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP1P2P3P4P5P8P9P10m;assert(HP1P2P3P4P5P8P9P10m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5P8P9P10m;assert(HP1P2P3P4P5P8P9P10m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5P8P9P10m;assert(HP1P2P3P4P5P8P9P10m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 4).
{
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P6P7P8m;assert(HP2P3P6P7P8m : rk(P2 :: P3 :: P6 :: P7 :: P8 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P6 :: P7 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P6P7P8m;assert(HP2P3P6P7P8m : rk(P2 :: P3 :: P6 :: P7 :: P8 :: nil) >= 3).
{
	try assert(HP2P3P7mtmp : rk(P2 :: P3 :: P7 :: nil) >= 3) by (solve_hyps_min HP2P3P7eq HP2P3P7m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P7 :: nil) (P2 :: P3 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P7 :: nil) (P2 :: P3 :: P6 :: P7 :: P8 :: nil) 3 3 HP2P3P7mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P6P7P8M;assert(HP2P3P6P7P8M : rk(P2 :: P3 :: P6 :: P7 :: P8 :: nil) <= 3).
{
	try assert(HP3P6P7Mtmp : rk(P3 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP3P6P7eq HP3P6P7M).
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP3mtmp : rk(P3 :: nil) >= 1) by (solve_hyps_min HP3eq HP3m).
	assert(Hincl : incl (P3 :: nil) (list_inter (P3 :: P6 :: P7 :: nil) (P2 :: P3 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P6 :: P7 :: P8 :: nil) (P3 :: P6 :: P7 :: P2 :: P3 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P7 :: P2 :: P3 :: P8 :: nil) ((P3 :: P6 :: P7 :: nil) ++ (P2 :: P3 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P6 :: P7 :: nil) (P2 :: P3 :: P8 :: nil) (P3 :: nil) 2 2 1 HP3P6P7Mtmp HP2P3P8Mtmp HP3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P6P8m;assert(HP2P3P6P8m : rk(P2 :: P3 :: P6 :: P8 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P6 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P6P8M;assert(HP2P3P6P8M : rk(P2 :: P3 :: P6 :: P8 :: nil) <= 3).
{
	try assert(HP6Mtmp : rk(P6 :: nil) <= 1) by (solve_hyps_max HP6eq HP6M).
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P6 :: nil) (P2 :: P3 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P6 :: P8 :: nil) (P6 :: P2 :: P3 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P2 :: P3 :: P8 :: nil) ((P6 :: nil) ++ (P2 :: P3 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: nil) (P2 :: P3 :: P8 :: nil) (nil) 1 2 0 HP6Mtmp HP2P3P8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P6P8m;assert(HP2P3P6P8m : rk(P2 :: P3 :: P6 :: P8 :: nil) >= 3).
{
	try assert(HP3P6P7Mtmp : rk(P3 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP3P6P7eq HP3P6P7M).
	try assert(HP2P3P6P7P8mtmp : rk(P2 :: P3 :: P6 :: P7 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P3P6P7P8eq HP2P3P6P7P8m).
	try assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m).
	assert(Hincl : incl (P3 :: P6 :: nil) (list_inter (P3 :: P6 :: P7 :: nil) (P2 :: P3 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P6 :: P7 :: P8 :: nil) (P3 :: P6 :: P7 :: P2 :: P3 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P7 :: P2 :: P3 :: P6 :: P8 :: nil) ((P3 :: P6 :: P7 :: nil) ++ (P2 :: P3 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P6P7P8mtmp;try rewrite HT2 in HP2P3P6P7P8mtmp.
	assert(HT := rule_4 (P3 :: P6 :: P7 :: nil) (P2 :: P3 :: P6 :: P8 :: nil) (P3 :: P6 :: nil) 3 2 2 HP2P3P6P7P8mtmp HP3P6mtmp HP3P6P7Mtmp Hincl); apply HT.
}

try clear HP6P8m;assert(HP6P8m : rk(P6 :: P8 :: nil) >= 2).
{
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP2P3P6P8mtmp : rk(P2 :: P3 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P3P6P8eq HP2P3P6P8m).
	try assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m).
	assert(Hincl : incl (P8 :: nil) (list_inter (P2 :: P3 :: P8 :: nil) (P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P6 :: P8 :: nil) (P2 :: P3 :: P8 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P8 :: P6 :: P8 :: nil) ((P2 :: P3 :: P8 :: nil) ++ (P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P6P8mtmp;try rewrite HT2 in HP2P3P6P8mtmp.
	assert(HT := rule_4 (P2 :: P3 :: P8 :: nil) (P6 :: P8 :: nil) (P8 :: nil) 3 1 2 HP2P3P6P8mtmp HP8mtmp HP2P3P8Mtmp Hincl); apply HT.
}

try clear HP4P6m;assert(HP4P6m : rk(P4 :: P6 :: nil) >= 2).
{
	try assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M).
	try assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: nil) (P4 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: nil) (P5 :: P4 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P4 :: P6 :: nil) ((P5 :: nil) ++ (P4 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6mtmp;try rewrite HT2 in HP4P5P6mtmp.
	assert(HT := rule_4 (P5 :: nil) (P4 :: P6 :: nil) (nil) 3 0 1 HP4P5P6mtmp Hmtmp HP5Mtmp Hincl); apply HT.
}

try clear HP4P6P8m;assert(HP4P6P8m : rk(P4 :: P6 :: P8 :: nil) >= 2).
{
	try assert(HP4P6mtmp : rk(P4 :: P6 :: nil) >= 2) by (solve_hyps_min HP4P6eq HP4P6m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: nil) 2 2 HP4P6mtmp Hcomp Hincl); apply HT.
}

try clear HP4P6P8m;assert(HP4P6P8m : rk(P4 :: P6 :: P8 :: nil) >= 3).
{
	try assert(HP5P6P8Mtmp : rk(P5 :: P6 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P8eq HP5P6P8M).
	try assert(HP4P5P6P8mtmp : rk(P4 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P6P8eq HP4P5P6P8m).
	try assert(HP6P8mtmp : rk(P6 :: P8 :: nil) >= 2) by (solve_hyps_min HP6P8eq HP6P8m).
	assert(Hincl : incl (P6 :: P8 :: nil) (list_inter (P4 :: P6 :: P8 :: nil) (P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P6 :: P8 :: P5 :: P6 :: P8 :: nil) ((P4 :: P6 :: P8 :: nil) ++ (P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8mtmp;try rewrite HT2 in HP4P5P6P8mtmp.
	assert(HT := rule_2 (P4 :: P6 :: P8 :: nil) (P5 :: P6 :: P8 :: nil) (P6 :: P8 :: nil) 3 2 2 HP4P5P6P8mtmp HP6P8mtmp HP5P6P8Mtmp Hincl); apply HT.
}

try clear HP4P6P8P9P10m;assert(HP4P6P8P9P10m : rk(P4 :: P6 :: P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP4P6mtmp : rk(P4 :: P6 :: nil) >= 2) by (solve_hyps_min HP4P6eq HP4P6m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: P9 :: P10 :: nil) 2 2 HP4P6mtmp Hcomp Hincl); apply HT.
}

try clear HP4P6P8P9P10m;assert(HP4P6P8P9P10m : rk(P4 :: P6 :: P8 :: P9 :: P10 :: nil) >= 3).
{
	try assert(HP4P6P8mtmp : rk(P4 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P6P8eq HP4P6P8m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P9 :: P10 :: nil) 3 3 HP4P6P8mtmp Hcomp Hincl); apply HT.
}

try clear HP8P9P10m;assert(HP8P9P10m : rk(P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP4P6P9Mtmp : rk(P4 :: P6 :: P9 :: nil) <= 2) by (solve_hyps_max HP4P6P9eq HP4P6P9M).
	try assert(HP4P6P8P9P10mtmp : rk(P4 :: P6 :: P8 :: P9 :: P10 :: nil) >= 3) by (solve_hyps_min HP4P6P8P9P10eq HP4P6P8P9P10m).
	try assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m).
	assert(Hincl : incl (P9 :: nil) (list_inter (P4 :: P6 :: P9 :: nil) (P8 :: P9 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P6 :: P8 :: P9 :: P10 :: nil) (P4 :: P6 :: P9 :: P8 :: P9 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P6 :: P9 :: P8 :: P9 :: P10 :: nil) ((P4 :: P6 :: P9 :: nil) ++ (P8 :: P9 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P6P8P9P10mtmp;try rewrite HT2 in HP4P6P8P9P10mtmp.
	assert(HT := rule_4 (P4 :: P6 :: P9 :: nil) (P8 :: P9 :: P10 :: nil) (P9 :: nil) 3 1 2 HP4P6P8P9P10mtmp HP9mtmp HP4P6P9Mtmp Hincl); apply HT.
}

try clear HP8P9P10M;assert(HP8P9P10M : rk(P8 :: P9 :: P10 :: nil) <= 2).
{
	try assert(HP1P2P3P8P9P10Mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) <= 3) by (solve_hyps_max HP1P2P3P8P9P10eq HP1P2P3P8P9P10M).
	try assert(HP4P5P8P9P10Mtmp : rk(P4 :: P5 :: P8 :: P9 :: P10 :: nil) <= 3) by (solve_hyps_max HP4P5P8P9P10eq HP4P5P8P9P10M).
	try assert(HP1P2P3P4P5P8P9P10mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P8P9P10eq HP1P2P3P4P5P8P9P10m).
	assert(Hincl : incl (P8 :: P9 :: P10 :: nil) (list_inter (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) ((P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) ++ (P4 :: P5 :: P8 :: P9 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P8P9P10mtmp;try rewrite HT2 in HP1P2P3P4P5P8P9P10mtmp.
	assert(HT := rule_3 (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil) (P8 :: P9 :: P10 :: nil) 3 3 4 HP1P2P3P8P9P10Mtmp HP4P5P8P9P10Mtmp HP1P2P3P4P5P8P9P10mtmp Hincl); apply HT.
}

assert(rk(P8 :: P9 :: P10 ::  nil) <= 3) by (clear_ineg_rk;try omega;try apply rk_upper_dim;try solve[apply matroid1_b_useful;simpl;intuition]).
assert(rk(P8 :: P9 :: P10 ::  nil) >= 1) by (clear_ineg_rk;try omega;try solve[apply matroid1_b_useful2;simpl;intuition]).
omega.
Qed.