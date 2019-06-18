Require Export ProjectiveGeometry.Dev.lemmas_automation_gV2.

Lemma Desargues_plane : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15,
rk(P1 :: P4 :: P7 :: nil) = 2 -> rk(P2 :: P5 :: P7 :: nil) = 2 -> rk(P3 :: P6 :: P7 :: nil) = 2 ->
rk(P1 :: P4 :: nil) = 2 -> rk(P2 :: P5 :: nil) = 2 -> rk(P3 :: P6 :: nil) = 2 ->
rk(P4 :: P7 :: nil) = 2 -> rk(P5 :: P7 :: nil) = 2 -> rk(P6 :: P7 :: nil) = 2 ->
rk(P1 :: P2 :: P3 :: nil) = 3 -> rk(P4 :: P5 :: P6 :: nil) = 3 ->
rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) = 3 ->
rk(P1 :: P2 :: P3 :: P11 :: nil) = 4 ->
rk(P1 :: P2 :: P3 :: P12 :: nil) = 4 ->
rk(P11 :: P12 :: nil) = 2 ->
rk(P7 :: P11 :: P12 :: nil) = 2 ->
rk(P1 :: P8 :: P12 :: nil) = 2 -> rk(P2 :: P9 :: P12 :: nil) = 2 -> rk(P3 :: P10 :: P12 :: nil) = 2 ->
rk(P4 :: P8 :: P11 :: nil) = 2 -> rk(P5 :: P9 :: P11 :: nil) = 2 -> rk(P6 :: P10 :: P11 :: nil) = 2 ->
rk(P8 :: P10 :: P14 :: nil) = 2 -> rk(P4 :: P6 :: P14 :: nil) = 2 -> 
rk(P9 :: P10 :: P13 :: nil) = 2 -> rk(P5 :: P6 :: P13 :: nil) = 2 ->
rk(P8 :: P9 :: P15 :: nil) = 2 -> rk(P4 :: P5 :: P15 :: nil) = 2 -> rk(P13 :: P14 :: P15 :: nil) = 2.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15
HP1P4P7eq HP2P5P7eq HP3P6P7eq HP1P4eq HP2P5eq HP3P6eq HP4P7eq HP5P7eq HP6P7eq
HP1P2P3eq HP4P5P6eq HP1P2P3P4P5P6P7eq HP1P2P3P11eq HP1P2P3P12eq HP11P12eq HP7P11P12eq
HP1P8P12eq HP2P9P12eq HP3P10P12eq HP4P8P11eq HP5P9P11eq HP6P10P11eq
HP8P10P14eq HP4P6P14eq HP9P10P13eq HP5P6P13eq HP8P9P15eq HP4P5P15eq.

assert(HP1P2m2 : rk(P1 :: P2 :: nil) >= 2).
{
	assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M1).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: nil) (P3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: nil) ((P1 :: P2 :: nil) ++ (P3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3mtmp;try rewrite HT2 in HP1P2P3mtmp.
	assert(HT := rule_2 (P1 :: P2 :: nil) (P3 :: nil) (nil) 3 0 1 HP1P2P3mtmp Hmtmp HP3Mtmp Hincl);apply HT.
}
try clear HP1P2m1. 

assert(HP1P2P3P8P12m2 : rk(P1 :: P2 :: P3 :: P8 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P12m1. 

assert(HP1P2P3P8P12m3 : rk(P1 :: P2 :: P3 :: P8 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P12m2. 

assert(HP1P2P3P8P12m4 : rk(P1 :: P2 :: P3 :: P8 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P12m3. 

assert(HP1P2P3P4P8P11m2 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8P11m1. 

assert(HP1P2P3P4P8P11m3 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8P11m2. 

assert(HP1P2P3P4P8P11m4 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8P11m3. 

assert(HP1P2P3P4P5P6P11P13m2 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6P11P13m1. 

assert(HP1P2P3P4P5P6P11P13m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6P11P13m2. 

assert(HP1P2P3P4P5P6P11P13m4 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6P11P13m3. 

assert(HP4P5m2 : rk(P4 :: P5 :: nil) >= 2).
{
	assert(HP6Mtmp : rk(P6 :: nil) <= 1) by (solve_hyps_max HP6eq HP6M1).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: P5 :: nil) (P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: nil) ((P4 :: P5 :: nil) ++ (P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6mtmp;try rewrite HT2 in HP4P5P6mtmp.
	assert(HT := rule_2 (P4 :: P5 :: nil) (P6 :: nil) (nil) 3 0 1 HP4P5P6mtmp Hmtmp HP6Mtmp Hincl);apply HT.
}
try clear HP4P5m1. 

assert(HP3P4P5P6m2 : rk(P3 :: P4 :: P5 :: P6 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P3 :: P4 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P3 :: P4 :: P5 :: P6 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP3P4P5P6m1. 

assert(HP3P4P5P6m3 : rk(P3 :: P4 :: P5 :: P6 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P3 :: P4 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P3 :: P4 :: P5 :: P6 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP3P4P5P6m2. 

assert(HP3P4P5P6M3 : rk(P3 :: P4 :: P5 :: P6 :: nil) <= 3).
{
	assert(HP1P2P3P4P5P6P7Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P7eq HP1P2P3P4P5P6P7M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) 3 3 HP1P2P3P4P5P6P7Mtmp Hcomp Hincl);apply HT.
}
try clear HP3P4P5P6M4. 

assert(HP2P4P5P6m2 : rk(P2 :: P4 :: P5 :: P6 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P4 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P4 :: P5 :: P6 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P5P6m1. 

assert(HP2P4P5P6m3 : rk(P2 :: P4 :: P5 :: P6 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P2 :: P4 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P2 :: P4 :: P5 :: P6 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P5P6m2. 

assert(HP2P4P5P6M3 : rk(P2 :: P4 :: P5 :: P6 :: nil) <= 3).
{
	assert(HP1P2P3P4P5P6P7Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P7eq HP1P2P3P4P5P6P7M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P2 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) 3 3 HP1P2P3P4P5P6P7Mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P5P6M4. 

assert(HP1P4P5P6m2 : rk(P1 :: P4 :: P5 :: P6 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P6 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P6m1. 

assert(HP1P4P5P6m3 : rk(P1 :: P4 :: P5 :: P6 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P6m2. 

assert(HP1P4P5P6M3 : rk(P1 :: P4 :: P5 :: P6 :: nil) <= 3).
{
	assert(HP1P2P3P4P5P6P7Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P7eq HP1P2P3P4P5P6P7M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) 3 3 HP1P2P3P4P5P6P7Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P6M4. 

assert(HP5P6m2 : rk(P5 :: P6 :: nil) >= 2).
{
	assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M1).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: nil) (P5 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: nil) ((P4 :: nil) ++ (P5 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6mtmp;try rewrite HT2 in HP4P5P6mtmp.
	assert(HT := rule_4 (P4 :: nil) (P5 :: P6 :: nil) (nil) 3 0 1 HP4P5P6mtmp Hmtmp HP4Mtmp Hincl); apply HT.
}
try clear HP5P6m1. 

assert(HP1P4P5P6P13m2 : rk(P1 :: P4 :: P5 :: P6 :: P13 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P6P13m1. 

assert(HP1P4P5P6P13m3 : rk(P1 :: P4 :: P5 :: P6 :: P13 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P6P13m2. 

assert(HP1P4P5P6P13M3 : rk(P1 :: P4 :: P5 :: P6 :: P13 :: nil) <= 3).
{
	assert(HP1P4P5P6Mtmp : rk(P1 :: P4 :: P5 :: P6 :: nil) <= 3) by (solve_hyps_max HP1P4P5P6eq HP1P4P5P6M3).
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hincl : incl (P5 :: P6 :: nil) (list_inter (P1 :: P4 :: P5 :: P6 :: nil) (P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P6 :: P13 :: nil) (P1 :: P4 :: P5 :: P6 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P6 :: P5 :: P6 :: P13 :: nil) ((P1 :: P4 :: P5 :: P6 :: nil) ++ (P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P5 :: P6 :: nil) (P5 :: P6 :: P13 :: nil) (P5 :: P6 :: nil) 3 2 2 HP1P4P5P6Mtmp HP5P6P13Mtmp HP5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P6P13M4. 

assert(HP1P2P4P5P6P13m2 : rk(P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P6P13m1. 

assert(HP1P2P4P5P6P13m3 : rk(P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P6P13m2. 

assert(HP1P2P4P5P6P13M3 : rk(P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil) <= 3).
{
	assert(HP2P4P5P6Mtmp : rk(P2 :: P4 :: P5 :: P6 :: nil) <= 3) by (solve_hyps_max HP2P4P5P6eq HP2P4P5P6M3).
	assert(HP1P4P5P6P13Mtmp : rk(P1 :: P4 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P4P5P6P13eq HP1P4P5P6P13M3).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (list_inter (P2 :: P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil) (P2 :: P4 :: P5 :: P6 :: P1 :: P4 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P5 :: P6 :: P1 :: P4 :: P5 :: P6 :: P13 :: nil) ((P2 :: P4 :: P5 :: P6 :: nil) ++ (P1 :: P4 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: nil) (P4 :: P5 :: P6 :: nil) 3 3 3 HP2P4P5P6Mtmp HP1P4P5P6P13Mtmp HP4P5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P4P5P6M3. try clear HP2P4P5P6m3. try clear HP1P4P5P6P13M3. try clear HP1P4P5P6P13m3. try clear HP1P2P4P5P6P13M4. 

assert(HP1P2P3P4P5P6P13m2 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6P13m1. 

assert(HP1P2P3P4P5P6P13m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6P13m2. 

assert(HP1P2P3P4P5P6P13M3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) <= 3).
{
	assert(HP3P4P5P6Mtmp : rk(P3 :: P4 :: P5 :: P6 :: nil) <= 3) by (solve_hyps_max HP3P4P5P6eq HP3P4P5P6M3).
	assert(HP1P2P4P5P6P13Mtmp : rk(P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P4P5P6P13eq HP1P2P4P5P6P13M3).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (list_inter (P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) (P3 :: P4 :: P5 :: P6 :: P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P4 :: P5 :: P6 :: P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil) ((P3 :: P4 :: P5 :: P6 :: nil) ++ (P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P13 :: nil) (P4 :: P5 :: P6 :: nil) 3 3 3 HP3P4P5P6Mtmp HP1P2P4P5P6P13Mtmp HP4P5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P4P5P6M3. try clear HP3P4P5P6m3. try clear HP1P2P4P5P6P13M3. try clear HP1P2P4P5P6P13m3. try clear HP1P2P3P4P5P6P13M4. 

assert(HP1P4P11m2 : rk(P1 :: P4 :: P11 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P11 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P11m1. 

assert(HP1P4P11m3 : rk(P1 :: P4 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P4P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P13eq HP1P2P3P4P5P6P13M3).
	assert(HP1P2P3P4P5P6P11P13mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P11P13eq HP1P2P3P4P5P6P11P13m4).
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hincl : incl (P1 :: P4 :: nil) (list_inter (P1 :: P4 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) (P1 :: P4 :: P11 :: P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P11 :: P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) ((P1 :: P4 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P11P13mtmp;try rewrite HT2 in HP1P2P3P4P5P6P11P13mtmp.
	assert(HT := rule_2 (P1 :: P4 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) (P1 :: P4 :: nil) 4 2 3 HP1P2P3P4P5P6P11P13mtmp HP1P4mtmp HP1P2P3P4P5P6P13Mtmp Hincl);apply HT.
}
try clear HP1P4P11m2. 

assert(HP1P2P3P4P11m2 : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P11m1. 

assert(HP1P2P3P4P11m3 : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P11m2. 

assert(HP1P2P3P4P11m4 : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P11m3. 

assert(HP1P4P8P11M3 : rk(P1 :: P4 :: P8 :: P11 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P4 :: P8 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P11 :: nil) ((P1 :: nil) ++ (P4 :: P8 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P4 :: P8 :: P11 :: nil) (nil) 1 2 0 HP1Mtmp HP4P8P11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P8P11M4. 

assert(HP1P4P8P11m2 : rk(P1 :: P4 :: P8 :: P11 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11m1. 

assert(HP1P4P8P11m3 : rk(P1 :: P4 :: P8 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P4P11Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P11eq HP1P2P3P4P11M4).
	assert(HP1P2P3P4P8P11mtmp : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P8P11eq HP1P2P3P4P8P11m4).
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P4 :: P8 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P4 :: P8 :: P11 :: nil) ((P1 :: P2 :: P3 :: P4 :: P11 :: nil) ++ (P1 :: P4 :: P8 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P8P11mtmp;try rewrite HT2 in HP1P2P3P4P8P11mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: nil) (P1 :: P4 :: P11 :: nil) 4 3 4 HP1P2P3P4P8P11mtmp HP1P4P11mtmp HP1P2P3P4P11Mtmp Hincl); apply HT.
}
try clear HP1P4P8P11m2. try clear HP1P2P3P4P8P11M4. try clear HP1P2P3P4P8P11m4. 

assert(HP1P8m2 : rk(P1 :: P8 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P11mtmp : rk(P1 :: P4 :: P8 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P8P11eq HP1P4P8P11m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P1 :: P8 :: nil) (P4 :: P8 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P4 :: P8 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P4 :: P8 :: P11 :: nil) ((P1 :: P8 :: nil) ++ (P4 :: P8 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P11mtmp;try rewrite HT2 in HP1P4P8P11mtmp.
	assert(HT := rule_2 (P1 :: P8 :: nil) (P4 :: P8 :: P11 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P11mtmp HP8mtmp HP4P8P11Mtmp Hincl);apply HT.
}
try clear HP1P8m1. try clear HP1P4P8P11M3. try clear HP1P4P8P11m3. 

assert(HP1P2P3P8m2 : rk(P1 :: P2 :: P3 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8m1. 

assert(HP1P2P3P8m3 : rk(P1 :: P2 :: P3 :: P8 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8m2. 

assert(HP1P2P3P8m4 : rk(P1 :: P2 :: P3 :: P8 :: nil) >= 4).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P2P3P8P12mtmp : rk(P1 :: P2 :: P3 :: P8 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P12eq HP1P2P3P8P12m4).
	assert(HP1P8mtmp : rk(P1 :: P8 :: nil) >= 2) by (solve_hyps_min HP1P8eq HP1P8m2).
	assert(Hincl : incl (P1 :: P8 :: nil) (list_inter (P1 :: P2 :: P3 :: P8 :: nil) (P1 :: P8 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P1 :: P8 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P8 :: P1 :: P8 :: P12 :: nil) ((P1 :: P2 :: P3 :: P8 :: nil) ++ (P1 :: P8 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P12mtmp;try rewrite HT2 in HP1P2P3P8P12mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: P8 :: nil) (P1 :: P8 :: P12 :: nil) (P1 :: P8 :: nil) 4 2 2 HP1P2P3P8P12mtmp HP1P8mtmp HP1P8P12Mtmp Hincl);apply HT.
}
try clear HP1P2P3P8m3. try clear HP1P2P3P8P12M4. try clear HP1P2P3P8P12m4. 

assert(HP1P2P3P8P13P14P15m2 : rk(P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P13P14P15m1. 

assert(HP1P2P3P8P13P14P15m3 : rk(P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P13P14P15m2. 

assert(HP1P2P3P8P13P14P15m4 : rk(P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP1P2P3P8mtmp : rk(P1 :: P2 :: P3 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8eq HP1P2P3P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) 4 4 HP1P2P3P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P13P14P15m3. 

assert(HP1P2P3P9P10P12P13m2 : rk(P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P10P12P13m1. 

assert(HP1P2P3P9P10P12P13m3 : rk(P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P10P12P13m2. 

assert(HP1P2P3P9P10P12P13m4 : rk(P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P10P12P13m3. 

assert(HP1P2P3P5P7P11P12m2 : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P7P11P12m1. 

assert(HP1P2P3P5P7P11P12m3 : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P7P11P12m2. 

assert(HP1P2P3P5P7P11P12m4 : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P7P11P12m3. 

assert(HP1P2P3P5P6P11P13m2 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P11P13m1. 

assert(HP1P2P3P5P6P11P13m3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P11P13m2. 

assert(HP1P2P3P5P6P11P13m4 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P11P13m3. 

assert(HP1P2P3P5P6m2 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6m1. 

assert(HP1P2P3P5P6m3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6m2. 

assert(HP1P2P3P5P6M3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: nil) <= 3).
{
	assert(HP1P2P3P4P5P6P7Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P7eq HP1P2P3P4P5P6P7M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P2 :: P3 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) 3 3 HP1P2P3P4P5P6P7Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6M4. 

assert(HP1P2P3P5P6P13m2 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P13m1. 

assert(HP1P2P3P5P6P13m3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P13m2. 

assert(HP1P2P3P5P6P13M3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3).
{
	assert(HP1P2P3P5P6Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5P6eq HP1P2P3P5P6M3).
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hincl : incl (P5 :: P6 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P6 :: nil) (P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P5 :: P6 :: P13 :: nil) ((P1 :: P2 :: P3 :: P5 :: P6 :: nil) ++ (P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P5 :: P6 :: nil) (P5 :: P6 :: P13 :: nil) (P5 :: P6 :: nil) 3 2 2 HP1P2P3P5P6Mtmp HP5P6P13Mtmp HP5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P5P6M3. try clear HP1P2P3P5P6m3. try clear HP1P2P3P5P6P13M4. 

assert(HP2P5P11m2 : rk(P2 :: P5 :: P11 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P11 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P11m1. 

assert(HP2P5P11m3 : rk(P2 :: P5 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5P6P13eq HP1P2P3P5P6P13M3).
	assert(HP1P2P3P5P6P11P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P6P11P13eq HP1P2P3P5P6P11P13m4).
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hincl : incl (P2 :: P5 :: nil) (list_inter (P2 :: P5 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) (P2 :: P5 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) ((P2 :: P5 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P11P13mtmp;try rewrite HT2 in HP1P2P3P5P6P11P13mtmp.
	assert(HT := rule_2 (P2 :: P5 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) (P2 :: P5 :: nil) 4 2 3 HP1P2P3P5P6P11P13mtmp HP2P5mtmp HP1P2P3P5P6P13Mtmp Hincl);apply HT.
}
try clear HP2P5P11m2. 

assert(HP1P2P3P5P11m2 : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P11m1. 

assert(HP1P2P3P5P11m3 : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P11m2. 

assert(HP1P2P3P5P11m4 : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P11m3. 

assert(HP2P5P7P11P12m2 : rk(P2 :: P5 :: P7 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P11 :: P12 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P7P11P12m1. 

assert(HP2P5P7P11P12M3 : rk(P2 :: P5 :: P7 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP7P11P12Mtmp : rk(P7 :: P11 :: P12 :: nil) <= 2) by (solve_hyps_max HP7P11P12eq HP7P11P12M2).
	assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m1).
	assert(Hincl : incl (P7 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P7 :: P11 :: P12 :: nil) (P2 :: P5 :: P7 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P7 :: P11 :: P12 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P5 :: P7 :: nil) (P7 :: P11 :: P12 :: nil) (P7 :: nil) 2 2 1 HP2P5P7Mtmp HP7P11P12Mtmp HP7mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P5P7P11P12M4. 

assert(HP2P5P7P11P12m3 : rk(P2 :: P5 :: P7 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3P5P11Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P5P11eq HP1P2P3P5P11M4).
	assert(HP1P2P3P5P7P11P12mtmp : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P7P11P12eq HP1P2P3P5P7P11P12m4).
	assert(HP2P5P11mtmp : rk(P2 :: P5 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P5P11eq HP2P5P11m3).
	assert(Hincl : incl (P2 :: P5 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P7 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P5 :: P11 :: nil) ++ (P2 :: P5 :: P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P7P11P12mtmp;try rewrite HT2 in HP1P2P3P5P7P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P7 :: P11 :: P12 :: nil) (P2 :: P5 :: P11 :: nil) 4 3 4 HP1P2P3P5P7P11P12mtmp HP2P5P11mtmp HP1P2P3P5P11Mtmp Hincl); apply HT.
}
try clear HP2P5P7P11P12m2. try clear HP1P2P3P5P7P11P12M4. try clear HP1P2P3P5P7P11P12m4. 

assert(HP1P2P3P5P6P7P11P13m2 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P7P11P13m1. 

assert(HP1P2P3P5P6P7P11P13m3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P7P11P13m2. 

assert(HP1P2P3P5P6P7P11P13m4 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P7m2 : rk(P1 :: P2 :: P3 :: P7 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P7 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P7m1. 

assert(HP1P2P3P7m3 : rk(P1 :: P2 :: P3 :: P7 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P7 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P7m2. 

assert(HP1P2P3P7M3 : rk(P1 :: P2 :: P3 :: P7 :: nil) <= 3).
{
	assert(HP1P2P3P4P5P6P7Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P7eq HP1P2P3P4P5P6P7M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P7 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P2 :: P3 :: P7 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) 3 3 HP1P2P3P4P5P6P7Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P7M4. 

assert(HP1P2P3P5P6P7P13m2 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P7P13m1. 

assert(HP1P2P3P5P6P7P13m3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P7P13m2. 

assert(HP1P2P3P5P6P7P13M3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) <= 3).
{
	assert(HP1P2P3P7Mtmp : rk(P1 :: P2 :: P3 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P7eq HP1P2P3P7M3).
	assert(HP1P2P3P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5P6P13eq HP1P2P3P5P6P13M3).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (list_inter (P1 :: P2 :: P3 :: P7 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) (P1 :: P2 :: P3 :: P7 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P7 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) ((P1 :: P2 :: P3 :: P7 :: nil) ++ (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P7 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) (P1 :: P2 :: P3 :: nil) 3 3 3 HP1P2P3P7Mtmp HP1P2P3P5P6P13Mtmp HP1P2P3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P7M3. try clear HP1P2P3P7m3. try clear HP1P2P3P5P6P7P13M4. 

assert(HP5P7P11m2 : rk(P5 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P7 :: nil) (P5 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P7 :: nil) (P5 :: P7 :: P11 :: nil) 2 2 HP5P7mtmp Hcomp Hincl);apply HT.
}
try clear HP5P7P11m1. 

assert(HP5P7P11m3 : rk(P5 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P5P6P7P13Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5P6P7P13eq HP1P2P3P5P6P7P13M3).
	assert(HP1P2P3P5P6P7P11P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P6P7P11P13eq HP1P2P3P5P6P7P11P13m4).
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hincl : incl (P5 :: P7 :: nil) (list_inter (P5 :: P7 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) (P5 :: P7 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P7 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) ((P5 :: P7 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P7P11P13mtmp;try rewrite HT2 in HP1P2P3P5P6P7P11P13mtmp.
	assert(HT := rule_2 (P5 :: P7 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) (P5 :: P7 :: nil) 4 2 3 HP1P2P3P5P6P7P11P13mtmp HP5P7mtmp HP1P2P3P5P6P7P13Mtmp Hincl);apply HT.
}
try clear HP5P7P11m2. 

assert(HP1P2P3P5P7P11m2 : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P7P11m1. 

assert(HP1P2P3P5P7P11m3 : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P7P11m2. 

assert(HP1P2P3P5P7P11m4 : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P7P11m3. 

assert(HP2P5P7P11m2 : rk(P2 :: P5 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P11 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P7P11m1. 

assert(HP2P5P7P11M3 : rk(P2 :: P5 :: P7 :: P11 :: nil) <= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP11Mtmp : rk(P11 :: nil) <= 1) by (solve_hyps_max HP11eq HP11M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: P5 :: P7 :: nil) (P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P7 :: P11 :: nil) (P2 :: P5 :: P7 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P11 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P5 :: P7 :: nil) (P11 :: nil) (nil) 2 1 0 HP2P5P7Mtmp HP11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P5P7P11M4. 

assert(HP2P5P7P11m3 : rk(P2 :: P5 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P5P11Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P5P11eq HP1P2P3P5P11M4).
	assert(HP1P2P3P5P7P11mtmp : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P7P11eq HP1P2P3P5P7P11m4).
	assert(HP2P5P11mtmp : rk(P2 :: P5 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P5P11eq HP2P5P11m3).
	assert(Hincl : incl (P2 :: P5 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P7 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P7 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P7 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P7 :: P11 :: nil) ((P1 :: P2 :: P3 :: P5 :: P11 :: nil) ++ (P2 :: P5 :: P7 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P7P11mtmp;try rewrite HT2 in HP1P2P3P5P7P11mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P7 :: P11 :: nil) (P2 :: P5 :: P11 :: nil) 4 3 4 HP1P2P3P5P7P11mtmp HP2P5P11mtmp HP1P2P3P5P11Mtmp Hincl); apply HT.
}
try clear HP2P5P7P11m2. try clear HP1P2P3P5P7P11M4. try clear HP1P2P3P5P7P11m4. 

assert(HP5P7P11P12M3 : rk(P5 :: P7 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M1).
	assert(HP7P11P12Mtmp : rk(P7 :: P11 :: P12 :: nil) <= 2) by (solve_hyps_max HP7P11P12eq HP7P11P12M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: nil) (P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P7 :: P11 :: P12 :: nil) (P5 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P7 :: P11 :: P12 :: nil) ((P5 :: nil) ++ (P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: nil) (P7 :: P11 :: P12 :: nil) (nil) 1 2 0 HP5Mtmp HP7P11P12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP5P7P11P12M4. 

assert(HP5P7P11P12m2 : rk(P5 :: P7 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P7 :: nil) (P5 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P7 :: nil) (P5 :: P7 :: P11 :: P12 :: nil) 2 2 HP5P7mtmp Hcomp Hincl);apply HT.
}
try clear HP5P7P11P12m1. 

assert(HP5P7P11P12m3 : rk(P5 :: P7 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP2P5P7P11Mtmp : rk(P2 :: P5 :: P7 :: P11 :: nil) <= 3) by (solve_hyps_max HP2P5P7P11eq HP2P5P7P11M3).
	assert(HP2P5P7P11P12mtmp : rk(P2 :: P5 :: P7 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP2P5P7P11P12eq HP2P5P7P11P12m3).
	assert(HP5P7P11mtmp : rk(P5 :: P7 :: P11 :: nil) >= 3) by (solve_hyps_min HP5P7P11eq HP5P7P11m3).
	assert(Hincl : incl (P5 :: P7 :: P11 :: nil) (list_inter (P2 :: P5 :: P7 :: P11 :: nil) (P5 :: P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P7 :: P11 :: P12 :: nil) (P2 :: P5 :: P7 :: P11 :: P5 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P11 :: P5 :: P7 :: P11 :: P12 :: nil) ((P2 :: P5 :: P7 :: P11 :: nil) ++ (P5 :: P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P5P7P11P12mtmp;try rewrite HT2 in HP2P5P7P11P12mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P7 :: P11 :: nil) (P5 :: P7 :: P11 :: P12 :: nil) (P5 :: P7 :: P11 :: nil) 3 3 3 HP2P5P7P11P12mtmp HP5P7P11mtmp HP2P5P7P11Mtmp Hincl); apply HT.
}
try clear HP5P7P11P12m2. 

assert(HP1P2P3P5P11P12m2 : rk(P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P11P12m1. 

assert(HP1P2P3P5P11P12m3 : rk(P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P11P12m2. 

assert(HP1P2P3P5P11P12m4 : rk(P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P11P12m3. 

assert(HP5P11m2 : rk(P5 :: P11 :: nil) >= 2).
{
	assert(HP1P2P3P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5P6P13eq HP1P2P3P5P6P13M3).
	assert(HP1P2P3P5P6P11P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P6P11P13eq HP1P2P3P5P6P11P13m4).
	assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m1).
	assert(Hincl : incl (P5 :: nil) (list_inter (P5 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) (P5 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) ((P5 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P11P13mtmp;try rewrite HT2 in HP1P2P3P5P6P11P13mtmp.
	assert(HT := rule_2 (P5 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) (P5 :: nil) 4 1 3 HP1P2P3P5P6P11P13mtmp HP5mtmp HP1P2P3P5P6P13Mtmp Hincl);apply HT.
}
try clear HP5P11m1. 

assert(HP5P11P12m2 : rk(P5 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2P3P5P11Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P5P11eq HP1P2P3P5P11M4).
	assert(HP1P2P3P5P11P12mtmp : rk(P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P11P12eq HP1P2P3P5P11P12m4).
	assert(HP5P11mtmp : rk(P5 :: P11 :: nil) >= 2) by (solve_hyps_min HP5P11eq HP5P11m2).
	assert(Hincl : incl (P5 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P5 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P5 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P11 :: P5 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P5 :: P11 :: nil) ++ (P5 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P11P12mtmp;try rewrite HT2 in HP1P2P3P5P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P5 :: P11 :: P12 :: nil) (P5 :: P11 :: nil) 4 2 4 HP1P2P3P5P11P12mtmp HP5P11mtmp HP1P2P3P5P11Mtmp Hincl); apply HT.
}
try clear HP5P11P12m1. 

assert(HP5P11P12m3 : rk(P5 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP7P11P12Mtmp : rk(P7 :: P11 :: P12 :: nil) <= 2) by (solve_hyps_max HP7P11P12eq HP7P11P12M2).
	assert(HP5P7P11P12mtmp : rk(P5 :: P7 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP5P7P11P12eq HP5P7P11P12m3).
	assert(HP11P12mtmp : rk(P11 :: P12 :: nil) >= 2) by (solve_hyps_min HP11P12eq HP11P12m2).
	assert(Hincl : incl (P11 :: P12 :: nil) (list_inter (P5 :: P11 :: P12 :: nil) (P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P7 :: P11 :: P12 :: nil) (P5 :: P11 :: P12 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P11 :: P12 :: P7 :: P11 :: P12 :: nil) ((P5 :: P11 :: P12 :: nil) ++ (P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P7P11P12mtmp;try rewrite HT2 in HP5P7P11P12mtmp.
	assert(HT := rule_2 (P5 :: P11 :: P12 :: nil) (P7 :: P11 :: P12 :: nil) (P11 :: P12 :: nil) 3 2 2 HP5P7P11P12mtmp HP11P12mtmp HP7P11P12Mtmp Hincl);apply HT.
}
try clear HP5P11P12m2. try clear HP5P7P11P12M3. try clear HP5P7P11P12m3. 

assert(HP1P2P3P5P9P11P12m2 : rk(P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P9P11P12m1. 

assert(HP1P2P3P5P9P11P12m3 : rk(P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P9P11P12m2. 

assert(HP1P2P3P5P9P11P12m4 : rk(P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P9P11P12m3. 

assert(HP5P9P11P12m2 : rk(P5 :: P9 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2P3P5P11Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P5P11eq HP1P2P3P5P11M4).
	assert(HP1P2P3P5P9P11P12mtmp : rk(P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P9P11P12eq HP1P2P3P5P9P11P12m4).
	assert(HP5P11mtmp : rk(P5 :: P11 :: nil) >= 2) by (solve_hyps_min HP5P11eq HP5P11m2).
	assert(Hincl : incl (P5 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P5 :: P9 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P5 :: P9 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P11 :: P5 :: P9 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P5 :: P11 :: nil) ++ (P5 :: P9 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P9P11P12mtmp;try rewrite HT2 in HP1P2P3P5P9P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P5 :: P9 :: P11 :: P12 :: nil) (P5 :: P11 :: nil) 4 2 4 HP1P2P3P5P9P11P12mtmp HP5P11mtmp HP1P2P3P5P11Mtmp Hincl); apply HT.
}
try clear HP5P9P11P12m1. try clear HP5P11M2. try clear HP5P11m2. try clear HP1P2P3P5P9P11P12M4. try clear HP1P2P3P5P9P11P12m4. 

assert(HP5P9P11P12M3 : rk(P5 :: P9 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP5P9P11Mtmp : rk(P5 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP5P9P11eq HP5P9P11M2).
	assert(HP12Mtmp : rk(P12 :: nil) <= 1) by (solve_hyps_max HP12eq HP12M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: P9 :: P11 :: nil) (P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P9 :: P11 :: P12 :: nil) (P5 :: P9 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P9 :: P11 :: P12 :: nil) ((P5 :: P9 :: P11 :: nil) ++ (P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: P9 :: P11 :: nil) (P12 :: nil) (nil) 2 1 0 HP5P9P11Mtmp HP12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP5P9P11P12M4. 

assert(HP5P9P11P12m3 : rk(P5 :: P9 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP5P11P12mtmp : rk(P5 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP5P11P12eq HP5P11P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P5 :: P11 :: P12 :: nil) (P5 :: P9 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P11 :: P12 :: nil) (P5 :: P9 :: P11 :: P12 :: nil) 3 3 HP5P11P12mtmp Hcomp Hincl);apply HT.
}
try clear HP5P9P11P12m2. 

assert(HP9P12m2 : rk(P9 :: P12 :: nil) >= 2).
{
	assert(HP5P9P11Mtmp : rk(P5 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP5P9P11eq HP5P9P11M2).
	assert(HP5P9P11P12mtmp : rk(P5 :: P9 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP5P9P11P12eq HP5P9P11P12m3).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P5 :: P9 :: P11 :: nil) (P9 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P9 :: P11 :: P12 :: nil) (P5 :: P9 :: P11 :: P9 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P9 :: P11 :: P9 :: P12 :: nil) ((P5 :: P9 :: P11 :: nil) ++ (P9 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P9P11P12mtmp;try rewrite HT2 in HP5P9P11P12mtmp.
	assert(HT := rule_4 (P5 :: P9 :: P11 :: nil) (P9 :: P12 :: nil) (P9 :: nil) 3 1 2 HP5P9P11P12mtmp HP9mtmp HP5P9P11Mtmp Hincl); apply HT.
}
try clear HP9P12m1. try clear HP5P9P11P12M3. try clear HP5P9P11P12m3. 

assert(HP1P3P12m3 : rk(P1 :: P3 :: P12 :: nil) >= 3).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P3 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P12 :: nil) (P2 :: P1 :: P3 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P3 :: P12 :: nil) ((P2 :: nil) ++ (P1 :: P3 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P12mtmp;try rewrite HT2 in HP1P2P3P12mtmp.
	assert(HT := rule_4 (P2 :: nil) (P1 :: P3 :: P12 :: nil) (nil) 4 0 1 HP1P2P3P12mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}
try clear HP1P3P12m1. 

assert(HP1P3m2 : rk(P1 :: P3 :: nil) >= 2).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: nil) (P2 :: P1 :: P3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P3 :: nil) ((P2 :: nil) ++ (P1 :: P3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3mtmp;try rewrite HT2 in HP1P2P3mtmp.
	assert(HT := rule_4 (P2 :: nil) (P1 :: P3 :: nil) (nil) 3 0 1 HP1P2P3mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}
try clear HP1P3m1. 

assert(HP1P3P9P10P12P13m2 : rk(P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P9P10P12P13m1. 

assert(HP1P3P9P10P12P13m3 : rk(P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P3P12mtmp : rk(P1 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P12eq HP1P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) 3 3 HP1P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P9P10P12P13m2. 

assert(HP1P3P9P10P12P13m4 : rk(P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP1P2P3P9P10P12P13mtmp : rk(P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P9P10P12P13eq HP1P2P3P9P10P12P13m4).
	assert(HP9P12mtmp : rk(P9 :: P12 :: nil) >= 2) by (solve_hyps_min HP9P12eq HP9P12m2).
	assert(Hincl : incl (P9 :: P12 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) (P2 :: P9 :: P12 :: P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P9P10P12P13mtmp;try rewrite HT2 in HP1P2P3P9P10P12P13mtmp.
	assert(HT := rule_4 (P2 :: P9 :: P12 :: nil) (P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) (P9 :: P12 :: nil) 4 2 2 HP1P2P3P9P10P12P13mtmp HP9P12mtmp HP2P9P12Mtmp Hincl); apply HT.
}
try clear HP1P3P9P10P12P13m3. 

assert(HP1P2P3P6P10P11m2 : rk(P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P10P11m1. 

assert(HP1P2P3P6P10P11m3 : rk(P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P10P11m2. 

assert(HP1P2P3P6P10P11m4 : rk(P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P10P11m3. 

assert(HP3P6P11m2 : rk(P3 :: P6 :: P11 :: nil) >= 2).
{
	assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: nil) (P3 :: P6 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: nil) (P3 :: P6 :: P11 :: nil) 2 2 HP3P6mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6P11m1. 

assert(HP3P6P11m3 : rk(P3 :: P6 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5P6P13eq HP1P2P3P5P6P13M3).
	assert(HP1P2P3P5P6P11P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P6P11P13eq HP1P2P3P5P6P11P13m4).
	assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m2).
	assert(Hincl : incl (P3 :: P6 :: nil) (list_inter (P3 :: P6 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) (P3 :: P6 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) ((P3 :: P6 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P11P13mtmp;try rewrite HT2 in HP1P2P3P5P6P11P13mtmp.
	assert(HT := rule_2 (P3 :: P6 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) (P3 :: P6 :: nil) 4 2 3 HP1P2P3P5P6P11P13mtmp HP3P6mtmp HP1P2P3P5P6P13Mtmp Hincl);apply HT.
}
try clear HP3P6P11m2. 

assert(HP1P2P3P6P11m2 : rk(P1 :: P2 :: P3 :: P6 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P11m1. 

assert(HP1P2P3P6P11m3 : rk(P1 :: P2 :: P3 :: P6 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P11m2. 

assert(HP1P2P3P6P11m4 : rk(P1 :: P2 :: P3 :: P6 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P11m3. 

assert(HP3P6P10P11M3 : rk(P3 :: P6 :: P10 :: P11 :: nil) <= 3).
{
	assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M1).
	assert(HP6P10P11Mtmp : rk(P6 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP6P10P11eq HP6P10P11M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: nil) (P6 :: P10 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P6 :: P10 :: P11 :: nil) (P3 :: P6 :: P10 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P10 :: P11 :: nil) ((P3 :: nil) ++ (P6 :: P10 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: nil) (P6 :: P10 :: P11 :: nil) (nil) 1 2 0 HP3Mtmp HP6P10P11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P6P10P11M4. 

assert(HP3P6P10P11m2 : rk(P3 :: P6 :: P10 :: P11 :: nil) >= 2).
{
	assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: nil) (P3 :: P6 :: P10 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: nil) (P3 :: P6 :: P10 :: P11 :: nil) 2 2 HP3P6mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6P10P11m1. 

assert(HP3P6P10P11m3 : rk(P3 :: P6 :: P10 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P6P11Mtmp : rk(P1 :: P2 :: P3 :: P6 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P6P11eq HP1P2P3P6P11M4).
	assert(HP1P2P3P6P10P11mtmp : rk(P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P6P10P11eq HP1P2P3P6P10P11m4).
	assert(HP3P6P11mtmp : rk(P3 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP3P6P11eq HP3P6P11m3).
	assert(Hincl : incl (P3 :: P6 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P10 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P3 :: P6 :: P10 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P6 :: P11 :: P3 :: P6 :: P10 :: P11 :: nil) ((P1 :: P2 :: P3 :: P6 :: P11 :: nil) ++ (P3 :: P6 :: P10 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P6P10P11mtmp;try rewrite HT2 in HP1P2P3P6P10P11mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P10 :: P11 :: nil) (P3 :: P6 :: P11 :: nil) 4 3 4 HP1P2P3P6P10P11mtmp HP3P6P11mtmp HP1P2P3P6P11Mtmp Hincl); apply HT.
}
try clear HP3P6P10P11m2. try clear HP1P2P3P6P10P11M4. try clear HP1P2P3P6P10P11m4. 

assert(HP3P10m2 : rk(P3 :: P10 :: nil) >= 2).
{
	assert(HP6P10P11Mtmp : rk(P6 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP6P10P11eq HP6P10P11M2).
	assert(HP3P6P10P11mtmp : rk(P3 :: P6 :: P10 :: P11 :: nil) >= 3) by (solve_hyps_min HP3P6P10P11eq HP3P6P10P11m3).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P3 :: P10 :: nil) (P6 :: P10 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P6 :: P10 :: P11 :: nil) (P3 :: P10 :: P6 :: P10 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P10 :: P6 :: P10 :: P11 :: nil) ((P3 :: P10 :: nil) ++ (P6 :: P10 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP3P6P10P11mtmp;try rewrite HT2 in HP3P6P10P11mtmp.
	assert(HT := rule_2 (P3 :: P10 :: nil) (P6 :: P10 :: P11 :: nil) (P10 :: nil) 3 1 2 HP3P6P10P11mtmp HP10mtmp HP6P10P11Mtmp Hincl);apply HT.
}
try clear HP3P10m1. try clear HP3P6P10P11M3. try clear HP3P6P10P11m3. 

assert(HP1P3P9P10P13m2 : rk(P1 :: P3 :: P9 :: P10 :: P13 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P9 :: P10 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P9 :: P10 :: P13 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P9P10P13m1. 

assert(HP1P3P9P10P13m3 : rk(P1 :: P3 :: P9 :: P10 :: P13 :: nil) >= 3).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP1P2P3P9P10P12P13mtmp : rk(P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P9P10P12P13eq HP1P2P3P9P10P12P13m4).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P1 :: P3 :: P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) (P2 :: P9 :: P12 :: P1 :: P3 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P1 :: P3 :: P9 :: P10 :: P13 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P1 :: P3 :: P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P9P10P12P13mtmp;try rewrite HT2 in HP1P2P3P9P10P12P13mtmp.
	assert(HT := rule_4 (P2 :: P9 :: P12 :: nil) (P1 :: P3 :: P9 :: P10 :: P13 :: nil) (P9 :: nil) 4 1 2 HP1P2P3P9P10P12P13mtmp HP9mtmp HP2P9P12Mtmp Hincl); apply HT.
}
try clear HP1P3P9P10P13m2. try clear HP1P2P3P9P10P12P13M4. try clear HP1P2P3P9P10P12P13m4. 

assert(HP1P3P9P10P13m4 : rk(P1 :: P3 :: P9 :: P10 :: P13 :: nil) >= 4).
{
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(HP1P3P9P10P12P13mtmp : rk(P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P3P9P10P12P13eq HP1P3P9P10P12P13m4).
	assert(HP3P10mtmp : rk(P3 :: P10 :: nil) >= 2) by (solve_hyps_min HP3P10eq HP3P10m2).
	assert(Hincl : incl (P3 :: P10 :: nil) (list_inter (P3 :: P10 :: P12 :: nil) (P1 :: P3 :: P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) (P3 :: P10 :: P12 :: P1 :: P3 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P10 :: P12 :: P1 :: P3 :: P9 :: P10 :: P13 :: nil) ((P3 :: P10 :: P12 :: nil) ++ (P1 :: P3 :: P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P9P10P12P13mtmp;try rewrite HT2 in HP1P3P9P10P12P13mtmp.
	assert(HT := rule_4 (P3 :: P10 :: P12 :: nil) (P1 :: P3 :: P9 :: P10 :: P13 :: nil) (P3 :: P10 :: nil) 4 2 2 HP1P3P9P10P12P13mtmp HP3P10mtmp HP3P10P12Mtmp Hincl); apply HT.
}
try clear HP1P3P9P10P13m3. 

assert(HP1P3P13m2 : rk(P1 :: P3 :: P13 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P13 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P13m1. 

assert(HP1P3P13m3 : rk(P1 :: P3 :: P13 :: nil) >= 3).
{
	assert(HP9P10P13Mtmp : rk(P9 :: P10 :: P13 :: nil) <= 2) by (solve_hyps_max HP9P10P13eq HP9P10P13M2).
	assert(HP1P3P9P10P13mtmp : rk(P1 :: P3 :: P9 :: P10 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P3P9P10P13eq HP1P3P9P10P13m4).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P1 :: P3 :: P13 :: nil) (P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P9 :: P10 :: P13 :: nil) (P1 :: P3 :: P13 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P13 :: P9 :: P10 :: P13 :: nil) ((P1 :: P3 :: P13 :: nil) ++ (P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P9P10P13mtmp;try rewrite HT2 in HP1P3P9P10P13mtmp.
	assert(HT := rule_2 (P1 :: P3 :: P13 :: nil) (P9 :: P10 :: P13 :: nil) (P13 :: nil) 4 1 2 HP1P3P9P10P13mtmp HP13mtmp HP9P10P13Mtmp Hincl);apply HT.
}
try clear HP1P3P13m2. try clear HP1P3P9P10P13M4. try clear HP1P3P9P10P13m4. 

assert(HP1P2P3P13m2 : rk(P1 :: P2 :: P3 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P13m1. 

assert(HP1P2P3P13m3 : rk(P1 :: P2 :: P3 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P13m2. 

assert(HP1P2P3P13M3 : rk(P1 :: P2 :: P3 :: P13 :: nil) <= 3).
{
	assert(HP1P2P3P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5P6P13eq HP1P2P3P5P6P13M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) 3 3 HP1P2P3P5P6P13Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P13M4. 

assert(HP1P3P8P12M3 : rk(P1 :: P3 :: P8 :: P12 :: nil) <= 3).
{
	assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M1).
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: nil) (P1 :: P8 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P8 :: P12 :: nil) (P3 :: P1 :: P8 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P1 :: P8 :: P12 :: nil) ((P3 :: nil) ++ (P1 :: P8 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: nil) (P1 :: P8 :: P12 :: nil) (nil) 1 2 0 HP3Mtmp HP1P8P12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P3P8P12M4. 

assert(HP1P3P8P12m2 : rk(P1 :: P3 :: P8 :: P12 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P12 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P12m1. 

assert(HP1P3P8P12m3 : rk(P1 :: P3 :: P8 :: P12 :: nil) >= 3).
{
	assert(HP1P3P12mtmp : rk(P1 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P12eq HP1P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P12 :: nil) 3 3 HP1P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P12m2. 

assert(HP1P3P8m2 : rk(P1 :: P3 :: P8 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8m1. 

assert(HP1P3P8m3 : rk(P1 :: P3 :: P8 :: nil) >= 3).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P3P8P12mtmp : rk(P1 :: P3 :: P8 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P8P12eq HP1P3P8P12m3).
	assert(HP1P8mtmp : rk(P1 :: P8 :: nil) >= 2) by (solve_hyps_min HP1P8eq HP1P8m2).
	assert(Hincl : incl (P1 :: P8 :: nil) (list_inter (P1 :: P3 :: P8 :: nil) (P1 :: P8 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P8 :: P12 :: nil) (P1 :: P3 :: P8 :: P1 :: P8 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P8 :: P1 :: P8 :: P12 :: nil) ((P1 :: P3 :: P8 :: nil) ++ (P1 :: P8 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P8P12mtmp;try rewrite HT2 in HP1P3P8P12mtmp.
	assert(HT := rule_2 (P1 :: P3 :: P8 :: nil) (P1 :: P8 :: P12 :: nil) (P1 :: P8 :: nil) 3 2 2 HP1P3P8P12mtmp HP1P8mtmp HP1P8P12Mtmp Hincl);apply HT.
}
try clear HP1P3P8m2. try clear HP1P3P8P12M3. try clear HP1P3P8P12m3. 

assert(HP1P3P8P13P14P15m2 : rk(P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P13P14P15m1. 

assert(HP1P3P8P13P14P15m3 : rk(P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P3P8mtmp : rk(P1 :: P3 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P3P8eq HP1P3P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P8 :: nil) (P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P8 :: nil) (P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P3P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P13P14P15m2. 

assert(HP1P3P8P13P14P15m4 : rk(P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP1P2P3P13Mtmp : rk(P1 :: P2 :: P3 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P13eq HP1P2P3P13M3).
	assert(HP1P2P3P8P13P14P15mtmp : rk(P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P13P14P15eq HP1P2P3P8P13P14P15m4).
	assert(HP1P3P13mtmp : rk(P1 :: P3 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P3P13eq HP1P3P13m3).
	assert(Hincl : incl (P1 :: P3 :: P13 :: nil) (list_inter (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) (P1 :: P2 :: P3 :: P13 :: P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P13 :: P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) ((P1 :: P2 :: P3 :: P13 :: nil) ++ (P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P13P14P15mtmp;try rewrite HT2 in HP1P2P3P8P13P14P15mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) (P1 :: P3 :: P13 :: nil) 4 3 3 HP1P2P3P8P13P14P15mtmp HP1P3P13mtmp HP1P2P3P13Mtmp Hincl); apply HT.
}
try clear HP1P3P8P13P14P15m3. try clear HP1P3P13M3. try clear HP1P3P13m3. try clear HP1P2P3P8P13P14P15M4. try clear HP1P2P3P8P13P14P15m4. 

assert(HP1P2P3P8P9P10P12P13P14m2 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P10P12P13P14m1. 

assert(HP1P2P3P8P9P10P12P13P14m3 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P10P12P13P14m2. 

assert(HP1P2P3P8P9P10P12P13P14m4 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P10P12P13P14m3. 

assert(HP1P3P8P9P10P12P13P14m2 : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P9P10P12P13P14m1. 

assert(HP1P3P8P9P10P12P13P14m3 : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P3P12mtmp : rk(P1 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P12eq HP1P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P9P10P12P13P14m2. 

assert(HP1P3P8P9P10P12P13P14m4 : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP1P2P3P8P9P10P12P13P14mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P9P10P12P13P14eq HP1P2P3P8P9P10P12P13P14m4).
	assert(HP9P12mtmp : rk(P9 :: P12 :: nil) >= 2) by (solve_hyps_min HP9P12eq HP9P12m2).
	assert(Hincl : incl (P9 :: P12 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) (P2 :: P9 :: P12 :: P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P9P10P12P13P14mtmp;try rewrite HT2 in HP1P2P3P8P9P10P12P13P14mtmp.
	assert(HT := rule_4 (P2 :: P9 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) (P9 :: P12 :: nil) 4 2 2 HP1P2P3P8P9P10P12P13P14mtmp HP9P12mtmp HP2P9P12Mtmp Hincl); apply HT.
}
try clear HP1P3P8P9P10P12P13P14m3. try clear HP1P2P3P8P9P10P12P13P14M4. try clear HP1P2P3P8P9P10P12P13P14m4. 

assert(HP1P2P3P6P7P11P12m2 : rk(P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P7P11P12m1. 

assert(HP1P2P3P6P7P11P12m3 : rk(P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P7P11P12m2. 

assert(HP1P2P3P6P7P11P12m4 : rk(P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P7P11P12m3. 

assert(HP3P6P7P11P12m2 : rk(P3 :: P6 :: P7 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: nil) (P3 :: P6 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: nil) (P3 :: P6 :: P7 :: P11 :: P12 :: nil) 2 2 HP3P6mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6P7P11P12m1. 

assert(HP3P6P7P11P12M3 : rk(P3 :: P6 :: P7 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP3P6P7Mtmp : rk(P3 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP3P6P7eq HP3P6P7M2).
	assert(HP7P11P12Mtmp : rk(P7 :: P11 :: P12 :: nil) <= 2) by (solve_hyps_max HP7P11P12eq HP7P11P12M2).
	assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m1).
	assert(Hincl : incl (P7 :: nil) (list_inter (P3 :: P6 :: P7 :: nil) (P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P6 :: P7 :: P11 :: P12 :: nil) (P3 :: P6 :: P7 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P7 :: P7 :: P11 :: P12 :: nil) ((P3 :: P6 :: P7 :: nil) ++ (P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P6 :: P7 :: nil) (P7 :: P11 :: P12 :: nil) (P7 :: nil) 2 2 1 HP3P6P7Mtmp HP7P11P12Mtmp HP7mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P6P7P11P12M4. 

assert(HP3P6P7P11P12m3 : rk(P3 :: P6 :: P7 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3P6P11Mtmp : rk(P1 :: P2 :: P3 :: P6 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P6P11eq HP1P2P3P6P11M4).
	assert(HP1P2P3P6P7P11P12mtmp : rk(P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P6P7P11P12eq HP1P2P3P6P7P11P12m4).
	assert(HP3P6P11mtmp : rk(P3 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP3P6P11eq HP3P6P11m3).
	assert(Hincl : incl (P3 :: P6 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P6 :: P11 :: P3 :: P6 :: P7 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P6 :: P11 :: nil) ++ (P3 :: P6 :: P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P6P7P11P12mtmp;try rewrite HT2 in HP1P2P3P6P7P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P7 :: P11 :: P12 :: nil) (P3 :: P6 :: P11 :: nil) 4 3 4 HP1P2P3P6P7P11P12mtmp HP3P6P11mtmp HP1P2P3P6P11Mtmp Hincl); apply HT.
}
try clear HP3P6P7P11P12m2. try clear HP1P2P3P6P7P11P12M4. try clear HP1P2P3P6P7P11P12m4. 

assert(HP1P3P5P6P7P11P13m2 : rk(P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P6P7P11P13m1. 

assert(HP1P3P5P6P7P11P13m3 : rk(P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP1P2P3P5P6P7P11P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P3P5P6P7P11P13eq HP1P2P3P5P6P7P11P13m3).
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hincl : incl (P5 :: P7 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) (P2 :: P5 :: P7 :: P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P7P11P13mtmp;try rewrite HT2 in HP1P2P3P5P6P7P11P13mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P7 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) (P5 :: P7 :: nil) 3 2 2 HP1P2P3P5P6P7P11P13mtmp HP5P7mtmp HP2P5P7Mtmp Hincl); apply HT.
}
try clear HP1P3P5P6P7P11P13m2. try clear HP1P2P3P5P6P7P11P13M4. try clear HP1P2P3P5P6P7P11P13m3. 

assert(HP1P3P5P6P7P11P13m4 : rk(P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 4).
{
	assert(HP2P5P7P11Mtmp : rk(P2 :: P5 :: P7 :: P11 :: nil) <= 3) by (solve_hyps_max HP2P5P7P11eq HP2P5P7P11M3).
	assert(HP1P2P3P5P6P7P11P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P6P7P11P13eq HP1P2P3P5P6P7P11P13m4).
	assert(HP5P7P11mtmp : rk(P5 :: P7 :: P11 :: nil) >= 3) by (solve_hyps_min HP5P7P11eq HP5P7P11m3).
	assert(Hincl : incl (P5 :: P7 :: P11 :: nil) (list_inter (P2 :: P5 :: P7 :: P11 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) (P2 :: P5 :: P7 :: P11 :: P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P11 :: P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) ((P2 :: P5 :: P7 :: P11 :: nil) ++ (P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P7P11P13mtmp;try rewrite HT2 in HP1P2P3P5P6P7P11P13mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P7 :: P11 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) (P5 :: P7 :: P11 :: nil) 4 3 3 HP1P2P3P5P6P7P11P13mtmp HP5P7P11mtmp HP2P5P7P11Mtmp Hincl); apply HT.
}
try clear HP2P5P7P11M3. try clear HP2P5P7P11m3. try clear HP1P3P5P6P7P11P13m3. try clear HP5P7P11M3. try clear HP5P7P11m3. try clear HP1P2P3P5P6P7P11P13M4. try clear HP1P2P3P5P6P7P11P13m4. 

assert(HP1P3P5P6m2 : rk(P1 :: P3 :: P5 :: P6 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P6m1. 

assert(HP1P3P5P6M3 : rk(P1 :: P3 :: P5 :: P6 :: nil) <= 3).
{
	assert(HP1P2P3P4P5P6P7Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P7eq HP1P2P3P4P5P6P7M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P3 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) 3 3 HP1P2P3P4P5P6P7Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P6M4. 

assert(HP1P3P5P6P13m2 : rk(P1 :: P3 :: P5 :: P6 :: P13 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: P13 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P6P13m1. 

assert(HP1P3P5P6P13M3 : rk(P1 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3).
{
	assert(HP1P3P5P6Mtmp : rk(P1 :: P3 :: P5 :: P6 :: nil) <= 3) by (solve_hyps_max HP1P3P5P6eq HP1P3P5P6M3).
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hincl : incl (P5 :: P6 :: nil) (list_inter (P1 :: P3 :: P5 :: P6 :: nil) (P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P5 :: P6 :: P13 :: nil) (P1 :: P3 :: P5 :: P6 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P5 :: P6 :: P5 :: P6 :: P13 :: nil) ((P1 :: P3 :: P5 :: P6 :: nil) ++ (P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P3 :: P5 :: P6 :: nil) (P5 :: P6 :: P13 :: nil) (P5 :: P6 :: nil) 3 2 2 HP1P3P5P6Mtmp HP5P6P13Mtmp HP5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P3P5P6M3. try clear HP1P3P5P6m2. try clear HP1P3P5P6P13M4. 

assert(HP1P3P5P6P7P13m2 : rk(P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P6P7P13m1. 

assert(HP1P3P5P6P7P13m3 : rk(P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) >= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP1P2P3P5P6P7P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P3P5P6P7P13eq HP1P2P3P5P6P7P13m3).
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hincl : incl (P5 :: P7 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) (P2 :: P5 :: P7 :: P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P7P13mtmp;try rewrite HT2 in HP1P2P3P5P6P7P13mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P7 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) (P5 :: P7 :: nil) 3 2 2 HP1P2P3P5P6P7P13mtmp HP5P7mtmp HP2P5P7Mtmp Hincl); apply HT.
}
try clear HP1P3P5P6P7P13m2. try clear HP5P7M2. try clear HP5P7m2. try clear HP1P2P3P5P6P7P13M3. try clear HP1P2P3P5P6P7P13m3. 

assert(HP1P3P5P6P7P13M3 : rk(P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) <= 3).
{
	assert(HP3P6P7Mtmp : rk(P3 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP3P6P7eq HP3P6P7M2).
	assert(HP1P3P5P6P13Mtmp : rk(P1 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P3P5P6P13eq HP1P3P5P6P13M3).
	assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m2).
	assert(Hincl : incl (P3 :: P6 :: nil) (list_inter (P3 :: P6 :: P7 :: nil) (P1 :: P3 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) (P3 :: P6 :: P7 :: P1 :: P3 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P7 :: P1 :: P3 :: P5 :: P6 :: P13 :: nil) ((P3 :: P6 :: P7 :: nil) ++ (P1 :: P3 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P6 :: P7 :: nil) (P1 :: P3 :: P5 :: P6 :: P13 :: nil) (P3 :: P6 :: nil) 2 3 2 HP3P6P7Mtmp HP1P3P5P6P13Mtmp HP3P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P3P5P6P13M3. try clear HP1P3P5P6P13m2. try clear HP1P3P5P6P7P13M4. 

assert(HP6P7P11m2 : rk(P6 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP6P7mtmp : rk(P6 :: P7 :: nil) >= 2) by (solve_hyps_min HP6P7eq HP6P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P6 :: P7 :: nil) (P6 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P6 :: P7 :: nil) (P6 :: P7 :: P11 :: nil) 2 2 HP6P7mtmp Hcomp Hincl);apply HT.
}
try clear HP6P7P11m1. 

assert(HP6P7P11m3 : rk(P6 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P3P5P6P7P13Mtmp : rk(P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P3P5P6P7P13eq HP1P3P5P6P7P13M3).
	assert(HP1P3P5P6P7P11P13mtmp : rk(P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P3P5P6P7P11P13eq HP1P3P5P6P7P11P13m4).
	assert(HP6P7mtmp : rk(P6 :: P7 :: nil) >= 2) by (solve_hyps_min HP6P7eq HP6P7m2).
	assert(Hincl : incl (P6 :: P7 :: nil) (list_inter (P6 :: P7 :: P11 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) (P6 :: P7 :: P11 :: P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P7 :: P11 :: P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) ((P6 :: P7 :: P11 :: nil) ++ (P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P5P6P7P11P13mtmp;try rewrite HT2 in HP1P3P5P6P7P11P13mtmp.
	assert(HT := rule_2 (P6 :: P7 :: P11 :: nil) (P1 :: P3 :: P5 :: P6 :: P7 :: P13 :: nil) (P6 :: P7 :: nil) 4 2 3 HP1P3P5P6P7P11P13mtmp HP6P7mtmp HP1P3P5P6P7P13Mtmp Hincl);apply HT.
}
try clear HP6P7P11m2. try clear HP1P3P5P6P7P13M3. try clear HP1P3P5P6P7P13m3. try clear HP1P3P5P6P7P11P13M4. try clear HP1P3P5P6P7P11P13m4. 

assert(HP1P2P3P6P7P11m2 : rk(P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P7P11m1. 

assert(HP1P2P3P6P7P11m3 : rk(P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P7P11m2. 

assert(HP1P2P3P6P7P11m4 : rk(P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P7P11m3. 

assert(HP3P6P7P11m2 : rk(P3 :: P6 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: nil) (P3 :: P6 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: nil) (P3 :: P6 :: P7 :: P11 :: nil) 2 2 HP3P6mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6P7P11m1. 

assert(HP3P6P7P11M3 : rk(P3 :: P6 :: P7 :: P11 :: nil) <= 3).
{
	assert(HP3P6P7Mtmp : rk(P3 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP3P6P7eq HP3P6P7M2).
	assert(HP11Mtmp : rk(P11 :: nil) <= 1) by (solve_hyps_max HP11eq HP11M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: P6 :: P7 :: nil) (P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P6 :: P7 :: P11 :: nil) (P3 :: P6 :: P7 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P7 :: P11 :: nil) ((P3 :: P6 :: P7 :: nil) ++ (P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P6 :: P7 :: nil) (P11 :: nil) (nil) 2 1 0 HP3P6P7Mtmp HP11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P6P7P11M4. 

assert(HP3P6P7P11m3 : rk(P3 :: P6 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P6P11Mtmp : rk(P1 :: P2 :: P3 :: P6 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P6P11eq HP1P2P3P6P11M4).
	assert(HP1P2P3P6P7P11mtmp : rk(P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P6P7P11eq HP1P2P3P6P7P11m4).
	assert(HP3P6P11mtmp : rk(P3 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP3P6P11eq HP3P6P11m3).
	assert(Hincl : incl (P3 :: P6 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P7 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P3 :: P6 :: P7 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P6 :: P11 :: P3 :: P6 :: P7 :: P11 :: nil) ((P1 :: P2 :: P3 :: P6 :: P11 :: nil) ++ (P3 :: P6 :: P7 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P6P7P11mtmp;try rewrite HT2 in HP1P2P3P6P7P11mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P7 :: P11 :: nil) (P3 :: P6 :: P11 :: nil) 4 3 4 HP1P2P3P6P7P11mtmp HP3P6P11mtmp HP1P2P3P6P11Mtmp Hincl); apply HT.
}
try clear HP3P6P7P11m2. 

assert(HP6P7P11P12M3 : rk(P6 :: P7 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP6Mtmp : rk(P6 :: nil) <= 1) by (solve_hyps_max HP6eq HP6M1).
	assert(HP7P11P12Mtmp : rk(P7 :: P11 :: P12 :: nil) <= 2) by (solve_hyps_max HP7P11P12eq HP7P11P12M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P6 :: nil) (P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P7 :: P11 :: P12 :: nil) (P6 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P7 :: P11 :: P12 :: nil) ((P6 :: nil) ++ (P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: nil) (P7 :: P11 :: P12 :: nil) (nil) 1 2 0 HP6Mtmp HP7P11P12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP6P7P11P12M4. 

assert(HP6P7P11P12m2 : rk(P6 :: P7 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP6P7mtmp : rk(P6 :: P7 :: nil) >= 2) by (solve_hyps_min HP6P7eq HP6P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P6 :: P7 :: nil) (P6 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P6 :: P7 :: nil) (P6 :: P7 :: P11 :: P12 :: nil) 2 2 HP6P7mtmp Hcomp Hincl);apply HT.
}
try clear HP6P7P11P12m1. 

assert(HP6P7P11P12m3 : rk(P6 :: P7 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP3P6P7P11Mtmp : rk(P3 :: P6 :: P7 :: P11 :: nil) <= 3) by (solve_hyps_max HP3P6P7P11eq HP3P6P7P11M3).
	assert(HP3P6P7P11P12mtmp : rk(P3 :: P6 :: P7 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP3P6P7P11P12eq HP3P6P7P11P12m3).
	assert(HP6P7P11mtmp : rk(P6 :: P7 :: P11 :: nil) >= 3) by (solve_hyps_min HP6P7P11eq HP6P7P11m3).
	assert(Hincl : incl (P6 :: P7 :: P11 :: nil) (list_inter (P3 :: P6 :: P7 :: P11 :: nil) (P6 :: P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P6 :: P7 :: P11 :: P12 :: nil) (P3 :: P6 :: P7 :: P11 :: P6 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P7 :: P11 :: P6 :: P7 :: P11 :: P12 :: nil) ((P3 :: P6 :: P7 :: P11 :: nil) ++ (P6 :: P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP3P6P7P11P12mtmp;try rewrite HT2 in HP3P6P7P11P12mtmp.
	assert(HT := rule_4 (P3 :: P6 :: P7 :: P11 :: nil) (P6 :: P7 :: P11 :: P12 :: nil) (P6 :: P7 :: P11 :: nil) 3 3 3 HP3P6P7P11P12mtmp HP6P7P11mtmp HP3P6P7P11Mtmp Hincl); apply HT.
}
try clear HP6P7P11P12m2. try clear HP3P6P7P11P12M3. try clear HP3P6P7P11P12m3. 

assert(HP1P2P3P6P11P12m2 : rk(P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P11P12m1. 

assert(HP1P2P3P6P11P12m3 : rk(P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P11P12m2. 

assert(HP1P2P3P6P11P12m4 : rk(P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P11P12m3. 

assert(HP6P11m2 : rk(P6 :: P11 :: nil) >= 2).
{
	assert(HP1P2P3P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5P6P13eq HP1P2P3P5P6P13M3).
	assert(HP1P2P3P5P6P11P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P6P11P13eq HP1P2P3P5P6P11P13m4).
	assert(HP6mtmp : rk(P6 :: nil) >= 1) by (solve_hyps_min HP6eq HP6m1).
	assert(Hincl : incl (P6 :: nil) (list_inter (P6 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) (P6 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) ((P6 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P11P13mtmp;try rewrite HT2 in HP1P2P3P5P6P11P13mtmp.
	assert(HT := rule_2 (P6 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) (P6 :: nil) 4 1 3 HP1P2P3P5P6P11P13mtmp HP6mtmp HP1P2P3P5P6P13Mtmp Hincl);apply HT.
}
try clear HP6P11m1. try clear HP6M1. try clear HP6m1. 

assert(HP6P11P12m2 : rk(P6 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2P3P6P11Mtmp : rk(P1 :: P2 :: P3 :: P6 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P6P11eq HP1P2P3P6P11M4).
	assert(HP1P2P3P6P11P12mtmp : rk(P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P6P11P12eq HP1P2P3P6P11P12m4).
	assert(HP6P11mtmp : rk(P6 :: P11 :: nil) >= 2) by (solve_hyps_min HP6P11eq HP6P11m2).
	assert(Hincl : incl (P6 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P6 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P6 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P6 :: P11 :: P6 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P6 :: P11 :: nil) ++ (P6 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P6P11P12mtmp;try rewrite HT2 in HP1P2P3P6P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P6 :: P11 :: P12 :: nil) (P6 :: P11 :: nil) 4 2 4 HP1P2P3P6P11P12mtmp HP6P11mtmp HP1P2P3P6P11Mtmp Hincl); apply HT.
}
try clear HP6P11P12m1. try clear HP1P2P3P6P11P12M4. try clear HP1P2P3P6P11P12m4. 

assert(HP6P11P12m3 : rk(P6 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP7P11P12Mtmp : rk(P7 :: P11 :: P12 :: nil) <= 2) by (solve_hyps_max HP7P11P12eq HP7P11P12M2).
	assert(HP6P7P11P12mtmp : rk(P6 :: P7 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP6P7P11P12eq HP6P7P11P12m3).
	assert(HP11P12mtmp : rk(P11 :: P12 :: nil) >= 2) by (solve_hyps_min HP11P12eq HP11P12m2).
	assert(Hincl : incl (P11 :: P12 :: nil) (list_inter (P6 :: P11 :: P12 :: nil) (P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P7 :: P11 :: P12 :: nil) (P6 :: P11 :: P12 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P11 :: P12 :: P7 :: P11 :: P12 :: nil) ((P6 :: P11 :: P12 :: nil) ++ (P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP6P7P11P12mtmp;try rewrite HT2 in HP6P7P11P12mtmp.
	assert(HT := rule_2 (P6 :: P11 :: P12 :: nil) (P7 :: P11 :: P12 :: nil) (P11 :: P12 :: nil) 3 2 2 HP6P7P11P12mtmp HP11P12mtmp HP7P11P12Mtmp Hincl);apply HT.
}
try clear HP6P11P12m2. try clear HP6P7P11P12M3. try clear HP6P7P11P12m3. 

assert(HP1P2P3P6P10P11P12m2 : rk(P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P10P11P12m1. 

assert(HP1P2P3P6P10P11P12m3 : rk(P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P10P11P12m2. 

assert(HP1P2P3P6P10P11P12m4 : rk(P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P10P11P12m3. 

assert(HP6P10P11P12m2 : rk(P6 :: P10 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2P3P6P11Mtmp : rk(P1 :: P2 :: P3 :: P6 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P6P11eq HP1P2P3P6P11M4).
	assert(HP1P2P3P6P10P11P12mtmp : rk(P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P6P10P11P12eq HP1P2P3P6P10P11P12m4).
	assert(HP6P11mtmp : rk(P6 :: P11 :: nil) >= 2) by (solve_hyps_min HP6P11eq HP6P11m2).
	assert(Hincl : incl (P6 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P6 :: P10 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P6 :: P10 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P6 :: P11 :: P6 :: P10 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P6 :: P11 :: P6 :: P10 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P6 :: P11 :: nil) ++ (P6 :: P10 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P6P10P11P12mtmp;try rewrite HT2 in HP1P2P3P6P10P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P6 :: P11 :: nil) (P6 :: P10 :: P11 :: P12 :: nil) (P6 :: P11 :: nil) 4 2 4 HP1P2P3P6P10P11P12mtmp HP6P11mtmp HP1P2P3P6P11Mtmp Hincl); apply HT.
}
try clear HP1P2P3P6P11M4. try clear HP1P2P3P6P11m4. try clear HP6P10P11P12m1. try clear HP1P2P3P6P10P11P12M4. try clear HP1P2P3P6P10P11P12m4. 

assert(HP6P10P11P12M3 : rk(P6 :: P10 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP6P10P11Mtmp : rk(P6 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP6P10P11eq HP6P10P11M2).
	assert(HP12Mtmp : rk(P12 :: nil) <= 1) by (solve_hyps_max HP12eq HP12M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P6 :: P10 :: P11 :: nil) (P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P10 :: P11 :: P12 :: nil) (P6 :: P10 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P10 :: P11 :: P12 :: nil) ((P6 :: P10 :: P11 :: nil) ++ (P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: P10 :: P11 :: nil) (P12 :: nil) (nil) 2 1 0 HP6P10P11Mtmp HP12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP6P10P11P12M4. 

assert(HP6P10P11P12m3 : rk(P6 :: P10 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP6P11P12mtmp : rk(P6 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP6P11P12eq HP6P11P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P6 :: P11 :: P12 :: nil) (P6 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P6 :: P11 :: P12 :: nil) (P6 :: P10 :: P11 :: P12 :: nil) 3 3 HP6P11P12mtmp Hcomp Hincl);apply HT.
}
try clear HP6P11P12M3. try clear HP6P11P12m3. try clear HP6P10P11P12m2. 

assert(HP10P12m2 : rk(P10 :: P12 :: nil) >= 2).
{
	assert(HP6P10P11Mtmp : rk(P6 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP6P10P11eq HP6P10P11M2).
	assert(HP6P10P11P12mtmp : rk(P6 :: P10 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP6P10P11P12eq HP6P10P11P12m3).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P6 :: P10 :: P11 :: nil) (P10 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P10 :: P11 :: P12 :: nil) (P6 :: P10 :: P11 :: P10 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P10 :: P11 :: P10 :: P12 :: nil) ((P6 :: P10 :: P11 :: nil) ++ (P10 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP6P10P11P12mtmp;try rewrite HT2 in HP6P10P11P12mtmp.
	assert(HT := rule_4 (P6 :: P10 :: P11 :: nil) (P10 :: P12 :: nil) (P10 :: nil) 3 1 2 HP6P10P11P12mtmp HP10mtmp HP6P10P11Mtmp Hincl); apply HT.
}
try clear HP10P12m1. try clear HP6P10P11P12M3. try clear HP6P10P11P12m3. 

assert(HP1P2P3P6P7m2 : rk(P1 :: P2 :: P3 :: P6 :: P7 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P7m1. 

assert(HP1P2P3P6P7m3 : rk(P1 :: P2 :: P3 :: P6 :: P7 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P6 :: P7 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P6P7m2. 

assert(HP1P2P6P7m2 : rk(P1 :: P2 :: P6 :: P7 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P7 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7m1. 

assert(HP1P2P6P7m3 : rk(P1 :: P2 :: P6 :: P7 :: nil) >= 3).
{
	assert(HP3P6P7Mtmp : rk(P3 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP3P6P7eq HP3P6P7M2).
	assert(HP1P2P3P6P7mtmp : rk(P1 :: P2 :: P3 :: P6 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P3P6P7eq HP1P2P3P6P7m3).
	assert(HP6P7mtmp : rk(P6 :: P7 :: nil) >= 2) by (solve_hyps_min HP6P7eq HP6P7m2).
	assert(Hincl : incl (P6 :: P7 :: nil) (list_inter (P1 :: P2 :: P6 :: P7 :: nil) (P3 :: P6 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P6 :: P7 :: nil) (P1 :: P2 :: P6 :: P7 :: P3 :: P6 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P6 :: P7 :: P3 :: P6 :: P7 :: nil) ((P1 :: P2 :: P6 :: P7 :: nil) ++ (P3 :: P6 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P6P7mtmp;try rewrite HT2 in HP1P2P3P6P7mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P6 :: P7 :: nil) (P3 :: P6 :: P7 :: nil) (P6 :: P7 :: nil) 3 2 2 HP1P2P3P6P7mtmp HP6P7mtmp HP3P6P7Mtmp Hincl);apply HT.
}
try clear HP1P2P6P7m2. try clear HP3P6P7M2. try clear HP3P6P7m2. try clear HP6P7M2. try clear HP6P7m2. try clear HP1P2P3P6P7M4. try clear HP1P2P3P6P7m3. 

assert(HP1P2P6P7M3 : rk(P1 :: P2 :: P6 :: P7 :: nil) <= 3).
{
	assert(HP1P2P3P4P5P6P7Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P7eq HP1P2P3P4P5P6P7M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: P7 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P2 :: P6 :: P7 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) 3 3 HP1P2P3P4P5P6P7Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7M4. 

assert(HP1P2P6P7P11m2 : rk(P1 :: P2 :: P6 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P7 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7P11m1. 

assert(HP1P2P6P7P11m3 : rk(P1 :: P2 :: P6 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P2P6P7mtmp : rk(P1 :: P2 :: P6 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P6P7eq HP1P2P6P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: P7 :: nil) (P1 :: P2 :: P6 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: P7 :: nil) (P1 :: P2 :: P6 :: P7 :: P11 :: nil) 3 3 HP1P2P6P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7P11m2. 

assert(HP1P2P6P7P11m4 : rk(P1 :: P2 :: P6 :: P7 :: P11 :: nil) >= 4).
{
	assert(HP3P6P7P11Mtmp : rk(P3 :: P6 :: P7 :: P11 :: nil) <= 3) by (solve_hyps_max HP3P6P7P11eq HP3P6P7P11M3).
	assert(HP1P2P3P6P7P11mtmp : rk(P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P6P7P11eq HP1P2P3P6P7P11m4).
	assert(HP6P7P11mtmp : rk(P6 :: P7 :: P11 :: nil) >= 3) by (solve_hyps_min HP6P7P11eq HP6P7P11m3).
	assert(Hincl : incl (P6 :: P7 :: P11 :: nil) (list_inter (P1 :: P2 :: P6 :: P7 :: P11 :: nil) (P3 :: P6 :: P7 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P6 :: P7 :: P11 :: nil) (P1 :: P2 :: P6 :: P7 :: P11 :: P3 :: P6 :: P7 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P6 :: P7 :: P11 :: P3 :: P6 :: P7 :: P11 :: nil) ((P1 :: P2 :: P6 :: P7 :: P11 :: nil) ++ (P3 :: P6 :: P7 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P6P7P11mtmp;try rewrite HT2 in HP1P2P3P6P7P11mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P6 :: P7 :: P11 :: nil) (P3 :: P6 :: P7 :: P11 :: nil) (P6 :: P7 :: P11 :: nil) 4 3 3 HP1P2P3P6P7P11mtmp HP6P7P11mtmp HP3P6P7P11Mtmp Hincl);apply HT.
}
try clear HP1P2P6P7P11m3. try clear HP3P6P7P11M3. try clear HP3P6P7P11m3. try clear HP6P7P11M3. try clear HP6P7P11m3. try clear HP1P2P3P6P7P11M4. try clear HP1P2P3P6P7P11m4. 

assert(HP1P2P5P6P7P8P9P11m2 : rk(P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P6P7P8P9P11m1. 

assert(HP1P2P5P6P7P8P9P11m3 : rk(P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP1P2P6P7mtmp : rk(P1 :: P2 :: P6 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P6P7eq HP1P2P6P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: P7 :: nil) (P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: P7 :: nil) (P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil) 3 3 HP1P2P6P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7M3. try clear HP1P2P6P7m3. try clear HP1P2P5P6P7P8P9P11m2. 

assert(HP1P2P5P6P7P8P9P11m4 : rk(P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil) >= 4).
{
	assert(HP1P2P6P7P11mtmp : rk(P1 :: P2 :: P6 :: P7 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P6P7P11eq HP1P2P6P7P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: P7 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: P7 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil) 4 4 HP1P2P6P7P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7P11M4. try clear HP1P2P6P7P11m4. try clear HP1P2P5P6P7P8P9P11m3. 

assert(HP1P2P3P5P7P9P11m2 : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P7P9P11m1. 

assert(HP1P2P3P5P7P9P11m3 : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P7P9P11m2. 

assert(HP1P2P3P5P7P9P11m4 : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P7P9P11m3. 

assert(HP2P5P7P9P11m2 : rk(P2 :: P5 :: P7 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P9 :: P11 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P7P9P11m1. 

assert(HP2P5P7P9P11M3 : rk(P2 :: P5 :: P7 :: P9 :: P11 :: nil) <= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP5P9P11Mtmp : rk(P5 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP5P9P11eq HP5P9P11M2).
	assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m1).
	assert(Hincl : incl (P5 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P5 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P7 :: P9 :: P11 :: nil) (P2 :: P5 :: P7 :: P5 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P5 :: P9 :: P11 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P5 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P5 :: P7 :: nil) (P5 :: P9 :: P11 :: nil) (P5 :: nil) 2 2 1 HP2P5P7Mtmp HP5P9P11Mtmp HP5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P5P7M2. try clear HP2P5P7m2. try clear HP2P5P7P9P11M4. 

assert(HP2P5P7P9P11m3 : rk(P2 :: P5 :: P7 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P5P11Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P5P11eq HP1P2P3P5P11M4).
	assert(HP1P2P3P5P7P9P11mtmp : rk(P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P7P9P11eq HP1P2P3P5P7P9P11m4).
	assert(HP2P5P11mtmp : rk(P2 :: P5 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P5P11eq HP2P5P11m3).
	assert(Hincl : incl (P2 :: P5 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P7 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P7 :: P9 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P7 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P7 :: P9 :: P11 :: nil) ((P1 :: P2 :: P3 :: P5 :: P11 :: nil) ++ (P2 :: P5 :: P7 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P7P9P11mtmp;try rewrite HT2 in HP1P2P3P5P7P9P11mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P7 :: P9 :: P11 :: nil) (P2 :: P5 :: P11 :: nil) 4 3 4 HP1P2P3P5P7P9P11mtmp HP2P5P11mtmp HP1P2P3P5P11Mtmp Hincl); apply HT.
}
try clear HP2P5P7P9P11m2. try clear HP1P2P3P5P7P9P11M4. try clear HP1P2P3P5P7P9P11m4. 

assert(HP1P2P11m2 : rk(P1 :: P2 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P11m1. 

assert(HP1P2P11m3 : rk(P1 :: P2 :: P11 :: nil) >= 3).
{
	assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M1).
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: nil) (P1 :: P2 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P11 :: nil) (P3 :: P1 :: P2 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P1 :: P2 :: P11 :: nil) ((P3 :: nil) ++ (P1 :: P2 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P11mtmp;try rewrite HT2 in HP1P2P3P11mtmp.
	assert(HT := rule_4 (P3 :: nil) (P1 :: P2 :: P11 :: nil) (nil) 4 0 1 HP1P2P3P11mtmp Hmtmp HP3Mtmp Hincl); apply HT.
}
try clear HP1P2P11m2. 

assert(HP1P2P5P6P8P11m2 : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P6P8P11m1. 

assert(HP1P2P5P6P8P11m3 : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) >= 3).
{
	assert(HP1P2P11mtmp : rk(P1 :: P2 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P2P11eq HP1P2P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) 3 3 HP1P2P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P6P8P11m2. 

assert(HP1P2P5P6P8P11m4 : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) >= 4).
{
	assert(HP2P5P7P9P11Mtmp : rk(P2 :: P5 :: P7 :: P9 :: P11 :: nil) <= 3) by (solve_hyps_max HP2P5P7P9P11eq HP2P5P7P9P11M3).
	assert(HP1P2P5P6P7P8P9P11mtmp : rk(P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P5P6P7P8P9P11eq HP1P2P5P6P7P8P9P11m4).
	assert(HP2P5P11mtmp : rk(P2 :: P5 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P5P11eq HP2P5P11m3).
	assert(Hincl : incl (P2 :: P5 :: P11 :: nil) (list_inter (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) (P2 :: P5 :: P7 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P6 :: P7 :: P8 :: P9 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: P2 :: P5 :: P7 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: P2 :: P5 :: P7 :: P9 :: P11 :: nil) ((P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) ++ (P2 :: P5 :: P7 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P6P7P8P9P11mtmp;try rewrite HT2 in HP1P2P5P6P7P8P9P11mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) (P2 :: P5 :: P7 :: P9 :: P11 :: nil) (P2 :: P5 :: P11 :: nil) 4 3 3 HP1P2P5P6P7P8P9P11mtmp HP2P5P11mtmp HP2P5P7P9P11Mtmp Hincl);apply HT.
}
try clear HP1P2P5P6P8P11m3. try clear HP2P5P7P9P11M3. try clear HP2P5P7P9P11m3. try clear HP1P2P5P6P7P8P9P11M4. try clear HP1P2P5P6P7P8P9P11m4. 

assert(HP1P2P5P6P8P9P10P11P12P13P14m2 : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P6P8P9P10P11P12P13P14m1. 

assert(HP1P2P5P6P8P9P10P11P12P13P14m3 : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P2P11mtmp : rk(P1 :: P2 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P2P11eq HP1P2P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P2P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P6P8P9P10P11P12P13P14m2. 

assert(HP1P2P5P6P8P9P10P11P12P13P14m4 : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P2P5P6P8P11mtmp : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P5P6P8P11eq HP1P2P5P6P8P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) 4 4 HP1P2P5P6P8P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P6P8P9P10P11P12P13P14m3. 

assert(HP2P5P11P12m2 : rk(P2 :: P5 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P11 :: P12 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P11P12m1. 

assert(HP2P5P11P12m3 : rk(P2 :: P5 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3P5P11Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P5P11eq HP1P2P3P5P11M4).
	assert(HP1P2P3P5P11P12mtmp : rk(P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P11P12eq HP1P2P3P5P11P12m4).
	assert(HP2P5P11mtmp : rk(P2 :: P5 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P5P11eq HP2P5P11m3).
	assert(Hincl : incl (P2 :: P5 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P5 :: P11 :: nil) ++ (P2 :: P5 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P11P12mtmp;try rewrite HT2 in HP1P2P3P5P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P11 :: P12 :: nil) (P2 :: P5 :: P11 :: nil) 4 3 4 HP1P2P3P5P11P12mtmp HP2P5P11mtmp HP1P2P3P5P11Mtmp Hincl); apply HT.
}
try clear HP2P5P11P12m2. try clear HP1P2P3P5P11P12M4. try clear HP1P2P3P5P11P12m4. 

assert(HP2P5P11P12M3 : rk(P2 :: P5 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP2P5P7P11P12Mtmp : rk(P2 :: P5 :: P7 :: P11 :: P12 :: nil) <= 3) by (solve_hyps_max HP2P5P7P11P12eq HP2P5P7P11P12M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: P11 :: P12 :: nil) (P2 :: P5 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P2 :: P5 :: P11 :: P12 :: nil) (P2 :: P5 :: P7 :: P11 :: P12 :: nil) 3 3 HP2P5P7P11P12Mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P11P12M4. try clear HP2P5P7P11P12M3. try clear HP2P5P7P11P12m3. 

assert(HP5P6P11m2 : rk(P5 :: P6 :: P11 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P5 :: P6 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P5 :: P6 :: P11 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P11m1. 

assert(HP5P6P11m3 : rk(P5 :: P6 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5P6P13eq HP1P2P3P5P6P13M3).
	assert(HP1P2P3P5P6P11P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P6P11P13eq HP1P2P3P5P6P11P13m4).
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hincl : incl (P5 :: P6 :: nil) (list_inter (P5 :: P6 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P11 :: P13 :: nil) (P5 :: P6 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P11 :: P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) ((P5 :: P6 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P11P13mtmp;try rewrite HT2 in HP1P2P3P5P6P11P13mtmp.
	assert(HT := rule_2 (P5 :: P6 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P13 :: nil) (P5 :: P6 :: nil) 4 2 3 HP1P2P3P5P6P11P13mtmp HP5P6mtmp HP1P2P3P5P6P13Mtmp Hincl);apply HT.
}
try clear HP5P6P11m2. try clear HP1P2P3P5P6P13M3. try clear HP1P2P3P5P6P13m3. try clear HP1P2P3P5P6P11P13M4. try clear HP1P2P3P5P6P11P13m4. 

assert(HP1P5P6P8P9P10P11P12P13P14m2 : rk(P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6P8P9P10P11P12P13P14m1. 

assert(HP1P5P6P8P9P10P11P12P13P14m3 : rk(P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP5P6P11mtmp : rk(P5 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP5P6P11eq HP5P6P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: P11 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: P11 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) 3 3 HP5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6P8P9P10P11P12P13P14m2. 

assert(HP1P5P6P8P9P10P11P12P13P14m4 : rk(P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP2P5P11P12Mtmp : rk(P2 :: P5 :: P11 :: P12 :: nil) <= 3) by (solve_hyps_max HP2P5P11P12eq HP2P5P11P12M3).
	assert(HP1P2P5P6P8P9P10P11P12P13P14mtmp : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P5P6P8P9P10P11P12P13P14eq HP1P2P5P6P8P9P10P11P12P13P14m4).
	assert(HP5P11P12mtmp : rk(P5 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP5P11P12eq HP5P11P12m3).
	assert(Hincl : incl (P5 :: P11 :: P12 :: nil) (list_inter (P2 :: P5 :: P11 :: P12 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) (P2 :: P5 :: P11 :: P12 :: P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P11 :: P12 :: P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) ((P2 :: P5 :: P11 :: P12 :: nil) ++ (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P6P8P9P10P11P12P13P14mtmp;try rewrite HT2 in HP1P2P5P6P8P9P10P11P12P13P14mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P11 :: P12 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) (P5 :: P11 :: P12 :: nil) 4 3 3 HP1P2P5P6P8P9P10P11P12P13P14mtmp HP5P11P12mtmp HP2P5P11P12Mtmp Hincl); apply HT.
}
try clear HP1P5P6P8P9P10P11P12P13P14m3. try clear HP1P2P5P6P8P9P10P11P12P13P14M4. try clear HP1P2P5P6P8P9P10P11P12P13P14m4. 

assert(HP5P6P9P11P13m2 : rk(P5 :: P6 :: P9 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P5 :: P6 :: P9 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P5 :: P6 :: P9 :: P11 :: P13 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P9P11P13m1. 

assert(HP5P6P9P11P13m3 : rk(P5 :: P6 :: P9 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP5P6P11mtmp : rk(P5 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP5P6P11eq HP5P6P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: P11 :: nil) (P5 :: P6 :: P9 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: P11 :: nil) (P5 :: P6 :: P9 :: P11 :: P13 :: nil) 3 3 HP5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P9P11P13m2. 

assert(HP5P6P9P11P13M3 : rk(P5 :: P6 :: P9 :: P11 :: P13 :: nil) <= 3).
{
	assert(HP5P9P11Mtmp : rk(P5 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP5P9P11eq HP5P9P11M2).
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m1).
	assert(Hincl : incl (P5 :: nil) (list_inter (P5 :: P9 :: P11 :: nil) (P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P9 :: P11 :: P13 :: nil) (P5 :: P9 :: P11 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P9 :: P11 :: P5 :: P6 :: P13 :: nil) ((P5 :: P9 :: P11 :: nil) ++ (P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: P9 :: P11 :: nil) (P5 :: P6 :: P13 :: nil) (P5 :: nil) 2 2 1 HP5P9P11Mtmp HP5P6P13Mtmp HP5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP5P6P9P11P13M4. 

assert(HP5P6P9P10P11P13m2 : rk(P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P9P10P11P13m1. 

assert(HP5P6P9P10P11P13m3 : rk(P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP5P6P11mtmp : rk(P5 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP5P6P11eq HP5P6P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: P11 :: nil) (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: P11 :: nil) (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) 3 3 HP5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P9P10P11P13m2. 

assert(HP5P6P9P10P11P13M3 : rk(P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) <= 3).
{
	assert(HP6P10P11Mtmp : rk(P6 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP6P10P11eq HP6P10P11M2).
	assert(HP5P6P9P11P13Mtmp : rk(P5 :: P6 :: P9 :: P11 :: P13 :: nil) <= 3) by (solve_hyps_max HP5P6P9P11P13eq HP5P6P9P11P13M3).
	assert(HP6P11mtmp : rk(P6 :: P11 :: nil) >= 2) by (solve_hyps_min HP6P11eq HP6P11m2).
	assert(Hincl : incl (P6 :: P11 :: nil) (list_inter (P6 :: P10 :: P11 :: nil) (P5 :: P6 :: P9 :: P11 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) (P6 :: P10 :: P11 :: P5 :: P6 :: P9 :: P11 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P10 :: P11 :: P5 :: P6 :: P9 :: P11 :: P13 :: nil) ((P6 :: P10 :: P11 :: nil) ++ (P5 :: P6 :: P9 :: P11 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: P10 :: P11 :: nil) (P5 :: P6 :: P9 :: P11 :: P13 :: nil) (P6 :: P11 :: nil) 2 3 2 HP6P10P11Mtmp HP5P6P9P11P13Mtmp HP6P11mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP5P6P9P11P13M3. try clear HP5P6P9P11P13m3. try clear HP6P11M2. try clear HP6P11m2. try clear HP5P6P9P10P11P13M4. 

assert(HP1P4P8P9P10P11P12P13P14m2 : rk(P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P9P10P11P12P13P14m1. 

assert(HP1P4P8P9P10P11P12P13P14m3 : rk(P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P4P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P9P10P11P12P13P14m2. 

assert(HP1P8P9P10P12P13P14m2 : rk(P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P9P10P11P12P13P14mtmp : rk(P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P4P8P9P10P11P12P13P14eq HP1P4P8P9P10P11P12P13P14m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) (P4 :: P8 :: P11 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P9P10P11P12P13P14mtmp;try rewrite HT2 in HP1P4P8P9P10P11P12P13P14mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P9P10P11P12P13P14mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP1P8P9P10P12P13P14m1. try clear HP1P4P8P9P10P11P12P13P14M4. try clear HP1P4P8P9P10P11P12P13P14m3. 

assert(HP1P8P9P10P12P13P14m3 : rk(P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP5P6P9P10P11P13Mtmp : rk(P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) <= 3) by (solve_hyps_max HP5P6P9P10P11P13eq HP5P6P9P10P11P13M3).
	assert(HP1P5P6P8P9P10P11P12P13P14mtmp : rk(P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P5P6P8P9P10P11P12P13P14eq HP1P5P6P8P9P10P11P12P13P14m4).
	assert(HP9P10P13mtmp : rk(P9 :: P10 :: P13 :: nil) >= 2) by (solve_hyps_min HP9P10P13eq HP9P10P13m2).
	assert(Hincl : incl (P9 :: P10 :: P13 :: nil) (list_inter (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) ((P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) ++ (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P5P6P8P9P10P11P12P13P14mtmp;try rewrite HT2 in HP1P5P6P8P9P10P11P12P13P14mtmp.
	assert(HT := rule_4 (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) (P9 :: P10 :: P13 :: nil) 4 2 3 HP1P5P6P8P9P10P11P12P13P14mtmp HP9P10P13mtmp HP5P6P9P10P11P13Mtmp Hincl); apply HT.
}
try clear HP1P8P9P10P12P13P14m2. try clear HP1P5P6P8P9P10P11P12P13P14M4. try clear HP1P5P6P8P9P10P11P12P13P14m4. 

assert(HP1P8P9P10P12P13P14m4 : rk(P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(HP1P3P8P9P10P12P13P14mtmp : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P3P8P9P10P12P13P14eq HP1P3P8P9P10P12P13P14m4).
	assert(HP10P12mtmp : rk(P10 :: P12 :: nil) >= 2) by (solve_hyps_min HP10P12eq HP10P12m2).
	assert(Hincl : incl (P10 :: P12 :: nil) (list_inter (P3 :: P10 :: P12 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) (P3 :: P10 :: P12 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P10 :: P12 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) ((P3 :: P10 :: P12 :: nil) ++ (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P8P9P10P12P13P14mtmp;try rewrite HT2 in HP1P3P8P9P10P12P13P14mtmp.
	assert(HT := rule_4 (P3 :: P10 :: P12 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) (P10 :: P12 :: nil) 4 2 2 HP1P3P8P9P10P12P13P14mtmp HP10P12mtmp HP3P10P12Mtmp Hincl); apply HT.
}
try clear HP1P8P9P10P12P13P14m3. try clear HP1P3P8P9P10P12P13P14M4. try clear HP1P3P8P9P10P12P13P14m4. 

assert(HP1P2P3P10P12m2 : rk(P1 :: P2 :: P3 :: P10 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P10 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P10 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P10P12m1. 

assert(HP1P2P3P10P12m3 : rk(P1 :: P2 :: P3 :: P10 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P10P12m2. 

assert(HP1P2P3P10P12m4 : rk(P1 :: P2 :: P3 :: P10 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P10 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P10 :: P12 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P10P12m3. 

assert(HP1P2P3P10m2 : rk(P1 :: P2 :: P3 :: P10 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P10m1. 

assert(HP1P2P3P10m3 : rk(P1 :: P2 :: P3 :: P10 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P10m2. 

assert(HP1P2P3P10m4 : rk(P1 :: P2 :: P3 :: P10 :: nil) >= 4).
{
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(HP1P2P3P10P12mtmp : rk(P1 :: P2 :: P3 :: P10 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P10P12eq HP1P2P3P10P12m4).
	assert(HP3P10mtmp : rk(P3 :: P10 :: nil) >= 2) by (solve_hyps_min HP3P10eq HP3P10m2).
	assert(Hincl : incl (P3 :: P10 :: nil) (list_inter (P1 :: P2 :: P3 :: P10 :: nil) (P3 :: P10 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P10 :: P12 :: nil) (P1 :: P2 :: P3 :: P10 :: P3 :: P10 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P10 :: P3 :: P10 :: P12 :: nil) ((P1 :: P2 :: P3 :: P10 :: nil) ++ (P3 :: P10 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P10P12mtmp;try rewrite HT2 in HP1P2P3P10P12mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: P10 :: nil) (P3 :: P10 :: P12 :: nil) (P3 :: P10 :: nil) 4 2 2 HP1P2P3P10P12mtmp HP3P10mtmp HP3P10P12Mtmp Hincl);apply HT.
}
try clear HP1P2P3P10m3. try clear HP3P10M2. try clear HP3P10m2. try clear HP1P2P3P10P12M4. try clear HP1P2P3P10P12m4. 

assert(HP1P2P3P10P13m2 : rk(P1 :: P2 :: P3 :: P10 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P10P13m1. 

assert(HP1P2P3P10P13m3 : rk(P1 :: P2 :: P3 :: P10 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P10P13m2. 

assert(HP1P2P3P10P13m4 : rk(P1 :: P2 :: P3 :: P10 :: P13 :: nil) >= 4).
{
	assert(HP1P2P3P10mtmp : rk(P1 :: P2 :: P3 :: P10 :: nil) >= 4) by (solve_hyps_min HP1P2P3P10eq HP1P2P3P10m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P10 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P10 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil) 4 4 HP1P2P3P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P10M4. try clear HP1P2P3P10m4. try clear HP1P2P3P10P13m3. 

assert(HP10P13m2 : rk(P10 :: P13 :: nil) >= 2).
{
	assert(HP1P2P3P13Mtmp : rk(P1 :: P2 :: P3 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P13eq HP1P2P3P13M3).
	assert(HP1P2P3P10P13mtmp : rk(P1 :: P2 :: P3 :: P10 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P10P13eq HP1P2P3P10P13m4).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P1 :: P2 :: P3 :: P13 :: nil) (P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P10 :: P13 :: nil) (P1 :: P2 :: P3 :: P13 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P13 :: P10 :: P13 :: nil) ((P1 :: P2 :: P3 :: P13 :: nil) ++ (P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P10P13mtmp;try rewrite HT2 in HP1P2P3P10P13mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P13 :: nil) (P10 :: P13 :: nil) (P13 :: nil) 4 1 3 HP1P2P3P10P13mtmp HP13mtmp HP1P2P3P13Mtmp Hincl); apply HT.
}
try clear HP10P13m1. try clear HP1P2P3P10P13M4. try clear HP1P2P3P10P13m4. 

assert(HP1P3P10P12M3 : rk(P1 :: P3 :: P10 :: P12 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P3 :: P10 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P10 :: P12 :: nil) (P1 :: P3 :: P10 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P10 :: P12 :: nil) ((P1 :: nil) ++ (P3 :: P10 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P3 :: P10 :: P12 :: nil) (nil) 1 2 0 HP1Mtmp HP3P10P12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P3P10P12M4. 

assert(HP1P3P10P12m2 : rk(P1 :: P3 :: P10 :: P12 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P10 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P10 :: P12 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P10P12m1. 

assert(HP1P3P10P12m3 : rk(P1 :: P3 :: P10 :: P12 :: nil) >= 3).
{
	assert(HP1P3P12mtmp : rk(P1 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P12eq HP1P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P10 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P10 :: P12 :: nil) 3 3 HP1P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P10P12m2. 

assert(HP1P12m2 : rk(P1 :: P12 :: nil) >= 2).
{
	assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M1).
	assert(HP1P3P12mtmp : rk(P1 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P12eq HP1P3P12m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: nil) (P1 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P12 :: nil) (P3 :: P1 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P1 :: P12 :: nil) ((P3 :: nil) ++ (P1 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P12mtmp;try rewrite HT2 in HP1P3P12mtmp.
	assert(HT := rule_4 (P3 :: nil) (P1 :: P12 :: nil) (nil) 3 0 1 HP1P3P12mtmp Hmtmp HP3Mtmp Hincl); apply HT.
}
try clear HP1P12m1. 

assert(HP1P10P12m2 : rk(P1 :: P10 :: P12 :: nil) >= 2).
{
	assert(HP1P12mtmp : rk(P1 :: P12 :: nil) >= 2) by (solve_hyps_min HP1P12eq HP1P12m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P12 :: nil) (P1 :: P10 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P12 :: nil) (P1 :: P10 :: P12 :: nil) 2 2 HP1P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P10P12m1. 

assert(HP1P10P12m3 : rk(P1 :: P10 :: P12 :: nil) >= 3).
{
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(HP1P3P10P12mtmp : rk(P1 :: P3 :: P10 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P10P12eq HP1P3P10P12m3).
	assert(HP10P12mtmp : rk(P10 :: P12 :: nil) >= 2) by (solve_hyps_min HP10P12eq HP10P12m2).
	assert(Hincl : incl (P10 :: P12 :: nil) (list_inter (P1 :: P10 :: P12 :: nil) (P3 :: P10 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P10 :: P12 :: nil) (P1 :: P10 :: P12 :: P3 :: P10 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P10 :: P12 :: P3 :: P10 :: P12 :: nil) ((P1 :: P10 :: P12 :: nil) ++ (P3 :: P10 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P10P12mtmp;try rewrite HT2 in HP1P3P10P12mtmp.
	assert(HT := rule_2 (P1 :: P10 :: P12 :: nil) (P3 :: P10 :: P12 :: nil) (P10 :: P12 :: nil) 3 2 2 HP1P3P10P12mtmp HP10P12mtmp HP3P10P12Mtmp Hincl);apply HT.
}
try clear HP1P10P12m2. try clear HP1P3P10P12M3. try clear HP1P3P10P12m3. 

assert(HP1P4P8P10P11P12P13P14m2 : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P10P11P12P13P14m1. 

assert(HP1P4P8P10P11P12P13P14m3 : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P4P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P10P11P12P13P14m2. 

assert(HP1P8P10P12P13P14m2 : rk(P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P10P11P12P13P14mtmp : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P4P8P10P11P12P13P14eq HP1P4P8P10P11P12P13P14m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: P13 :: P14 :: nil) (P4 :: P8 :: P11 :: P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P10P11P12P13P14mtmp;try rewrite HT2 in HP1P4P8P10P11P12P13P14mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P10P11P12P13P14mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP1P8P10P12P13P14m1. try clear HP1P4P8P10P11P12P13P14M4. try clear HP1P4P8P10P11P12P13P14m3. 

assert(HP1P8P10P12P13P14m3 : rk(P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P10P12mtmp : rk(P1 :: P10 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P10P12eq HP1P10P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P10 :: P12 :: nil) (P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P10 :: P12 :: nil) (P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P10P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P8P10P12P13P14m2. 

assert(HP1P8P10P12P13P14m4 : rk(P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP9P10P13Mtmp : rk(P9 :: P10 :: P13 :: nil) <= 2) by (solve_hyps_max HP9P10P13eq HP9P10P13M2).
	assert(HP1P8P9P10P12P13P14mtmp : rk(P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P8P9P10P12P13P14eq HP1P8P9P10P12P13P14m4).
	assert(HP10P13mtmp : rk(P10 :: P13 :: nil) >= 2) by (solve_hyps_min HP10P13eq HP10P13m2).
	assert(Hincl : incl (P10 :: P13 :: nil) (list_inter (P9 :: P10 :: P13 :: nil) (P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: nil) (P9 :: P10 :: P13 :: P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P9 :: P10 :: P13 :: P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) ((P9 :: P10 :: P13 :: nil) ++ (P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P8P9P10P12P13P14mtmp;try rewrite HT2 in HP1P8P9P10P12P13P14mtmp.
	assert(HT := rule_4 (P9 :: P10 :: P13 :: nil) (P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) (P10 :: P13 :: nil) 4 2 2 HP1P8P9P10P12P13P14mtmp HP10P13mtmp HP9P10P13Mtmp Hincl); apply HT.
}
try clear HP1P8P10P12P13P14m3. try clear HP10P13M2. try clear HP10P13m2. try clear HP1P8P9P10P12P13P14M4. try clear HP1P8P9P10P12P13P14m4. 

assert(HP1P2P3P8P12P13m2 : rk(P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P12P13m1. 

assert(HP1P2P3P8P12P13m3 : rk(P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P12P13m2. 

assert(HP1P2P3P8P12P13m4 : rk(P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P12P13m3. 

assert(HP1P2P12m2 : rk(P1 :: P2 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P12m1. 

assert(HP1P2P12m3 : rk(P1 :: P2 :: P12 :: nil) >= 3).
{
	assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M1).
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: nil) (P1 :: P2 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P12 :: nil) (P3 :: P1 :: P2 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P1 :: P2 :: P12 :: nil) ((P3 :: nil) ++ (P1 :: P2 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P12mtmp;try rewrite HT2 in HP1P2P3P12mtmp.
	assert(HT := rule_4 (P3 :: nil) (P1 :: P2 :: P12 :: nil) (nil) 4 0 1 HP1P2P3P12mtmp Hmtmp HP3Mtmp Hincl); apply HT.
}
try clear HP1P2P12m2. 

assert(HP1P2P9P10P12P13m2 : rk(P1 :: P2 :: P9 :: P10 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P9 :: P10 :: P12 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P9P10P12P13m1. 

assert(HP1P2P9P10P12P13m3 : rk(P1 :: P2 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P12mtmp : rk(P1 :: P2 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P2P12eq HP1P2P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P12 :: nil) (P1 :: P2 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P12 :: nil) (P1 :: P2 :: P9 :: P10 :: P12 :: P13 :: nil) 3 3 HP1P2P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P9P10P12P13m2. 

assert(HP1P9P10P13M3 : rk(P1 :: P9 :: P10 :: P13 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP9P10P13Mtmp : rk(P9 :: P10 :: P13 :: nil) <= 2) by (solve_hyps_max HP9P10P13eq HP9P10P13M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P9 :: P10 :: P13 :: nil) (P1 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P9 :: P10 :: P13 :: nil) ((P1 :: nil) ++ (P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P9 :: P10 :: P13 :: nil) (nil) 1 2 0 HP1Mtmp HP9P10P13Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P9P10P13M4. 

assert(HP1P9P10P13m2 : rk(P1 :: P9 :: P10 :: P13 :: nil) >= 2).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP1P2P9P10P12P13mtmp : rk(P1 :: P2 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P9P10P12P13eq HP1P2P9P10P12P13m3).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P1 :: P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P9 :: P10 :: P12 :: P13 :: nil) (P2 :: P9 :: P12 :: P1 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P1 :: P9 :: P10 :: P13 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P1 :: P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P9P10P12P13mtmp;try rewrite HT2 in HP1P2P9P10P12P13mtmp.
	assert(HT := rule_4 (P2 :: P9 :: P12 :: nil) (P1 :: P9 :: P10 :: P13 :: nil) (P9 :: nil) 3 1 2 HP1P2P9P10P12P13mtmp HP9mtmp HP2P9P12Mtmp Hincl); apply HT.
}
try clear HP1P9P10P13m1. try clear HP1P2P9P10P12P13M4. try clear HP1P2P9P10P12P13m3. 

assert(HP1P9P10P13m3 : rk(P1 :: P9 :: P10 :: P13 :: nil) >= 3).
{
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(HP1P3P9P10P12P13mtmp : rk(P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P3P9P10P12P13eq HP1P3P9P10P12P13m4).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P3 :: P10 :: P12 :: nil) (P1 :: P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) (P3 :: P10 :: P12 :: P1 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P10 :: P12 :: P1 :: P9 :: P10 :: P13 :: nil) ((P3 :: P10 :: P12 :: nil) ++ (P1 :: P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P9P10P12P13mtmp;try rewrite HT2 in HP1P3P9P10P12P13mtmp.
	assert(HT := rule_4 (P3 :: P10 :: P12 :: nil) (P1 :: P9 :: P10 :: P13 :: nil) (P10 :: nil) 4 1 2 HP1P3P9P10P12P13mtmp HP10mtmp HP3P10P12Mtmp Hincl); apply HT.
}
try clear HP1P9P10P13m2. try clear HP1P3P9P10P12P13M4. try clear HP1P3P9P10P12P13m4. 

assert(HP1P13m2 : rk(P1 :: P13 :: nil) >= 2).
{
	assert(HP9P10P13Mtmp : rk(P9 :: P10 :: P13 :: nil) <= 2) by (solve_hyps_max HP9P10P13eq HP9P10P13M2).
	assert(HP1P9P10P13mtmp : rk(P1 :: P9 :: P10 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P9P10P13eq HP1P9P10P13m3).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P1 :: P13 :: nil) (P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P9 :: P10 :: P13 :: nil) (P1 :: P13 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P13 :: P9 :: P10 :: P13 :: nil) ((P1 :: P13 :: nil) ++ (P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P9P10P13mtmp;try rewrite HT2 in HP1P9P10P13mtmp.
	assert(HT := rule_2 (P1 :: P13 :: nil) (P9 :: P10 :: P13 :: nil) (P13 :: nil) 3 1 2 HP1P9P10P13mtmp HP13mtmp HP9P10P13Mtmp Hincl);apply HT.
}
try clear HP1P13m1. try clear HP1P9P10P13M3. try clear HP1P9P10P13m3. 

assert(HP1P4P8P11P12P13m2 : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P12P13m1. 

assert(HP1P4P8P11P12P13m3 : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: nil) 3 3 HP1P4P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P12P13m2. 

assert(HP1P8P12P13m2 : rk(P1 :: P8 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P11P12P13mtmp : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P4P8P11P12P13eq HP1P4P8P11P12P13m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: nil) (P4 :: P8 :: P11 :: P1 :: P8 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P1 :: P8 :: P12 :: P13 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P1 :: P8 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P11P12P13mtmp;try rewrite HT2 in HP1P4P8P11P12P13mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P12 :: P13 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P11P12P13mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP1P8P12P13m1. try clear HP1P4P8P11P12P13M4. try clear HP1P4P8P11P12P13m3. 

assert(HP1P8P12P13M3 : rk(P1 :: P8 :: P12 :: P13 :: nil) <= 3).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP13Mtmp : rk(P13 :: nil) <= 1) by (solve_hyps_max HP13eq HP13M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P8 :: P12 :: nil) (P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P12 :: P13 :: nil) (P1 :: P8 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P13 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P8 :: P12 :: nil) (P13 :: nil) (nil) 2 1 0 HP1P8P12Mtmp HP13Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P8P12P13M4. 

assert(HP1P8P12P13m3 : rk(P1 :: P8 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3P13Mtmp : rk(P1 :: P2 :: P3 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P13eq HP1P2P3P13M3).
	assert(HP1P2P3P8P12P13mtmp : rk(P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P12P13eq HP1P2P3P8P12P13m4).
	assert(HP1P13mtmp : rk(P1 :: P13 :: nil) >= 2) by (solve_hyps_min HP1P13eq HP1P13m2).
	assert(Hincl : incl (P1 :: P13 :: nil) (list_inter (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P8 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) (P1 :: P2 :: P3 :: P13 :: P1 :: P8 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P13 :: P1 :: P8 :: P12 :: P13 :: nil) ((P1 :: P2 :: P3 :: P13 :: nil) ++ (P1 :: P8 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P12P13mtmp;try rewrite HT2 in HP1P2P3P8P12P13mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P8 :: P12 :: P13 :: nil) (P1 :: P13 :: nil) 4 2 3 HP1P2P3P8P12P13mtmp HP1P13mtmp HP1P2P3P13Mtmp Hincl); apply HT.
}
try clear HP1P8P12P13m2. try clear HP1P2P3P8P12P13M4. try clear HP1P2P3P8P12P13m4. 

assert(HP1P4P8P10P11P14m2 : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P10P11P14m1. 

assert(HP1P4P8P10P11P14m3 : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) 3 3 HP1P4P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P10P11P14m2. 

assert(HP1P8P10P14M3 : rk(P1 :: P8 :: P10 :: P14 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP8P10P14Mtmp : rk(P8 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP8P10P14eq HP8P10P14M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P8 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P10 :: P14 :: nil) (P1 :: P8 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P10 :: P14 :: nil) ((P1 :: nil) ++ (P8 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P8 :: P10 :: P14 :: nil) (nil) 1 2 0 HP1Mtmp HP8P10P14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P8P10P14M4. 

assert(HP1P8P10P14m2 : rk(P1 :: P8 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P10P11P14mtmp : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P4P8P10P11P14eq HP1P4P8P10P11P14m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) (P4 :: P8 :: P11 :: P1 :: P8 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P1 :: P8 :: P10 :: P14 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P1 :: P8 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P10P11P14mtmp;try rewrite HT2 in HP1P4P8P10P11P14mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P10 :: P14 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P10P11P14mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP1P8P10P14m1. try clear HP1P4P8P10P11P14M4. try clear HP1P4P8P10P11P14m3. 

assert(HP1P8P10P14m3 : rk(P1 :: P8 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P8P12P13Mtmp : rk(P1 :: P8 :: P12 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P8P12P13eq HP1P8P12P13M3).
	assert(HP1P8P10P12P13P14mtmp : rk(P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P8P10P12P13P14eq HP1P8P10P12P13P14m4).
	assert(HP1P8mtmp : rk(P1 :: P8 :: nil) >= 2) by (solve_hyps_min HP1P8eq HP1P8m2).
	assert(Hincl : incl (P1 :: P8 :: nil) (list_inter (P1 :: P8 :: P12 :: P13 :: nil) (P1 :: P8 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P10 :: P12 :: P13 :: P14 :: nil) (P1 :: P8 :: P12 :: P13 :: P1 :: P8 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P13 :: P1 :: P8 :: P10 :: P14 :: nil) ((P1 :: P8 :: P12 :: P13 :: nil) ++ (P1 :: P8 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P8P10P12P13P14mtmp;try rewrite HT2 in HP1P8P10P12P13P14mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: P13 :: nil) (P1 :: P8 :: P10 :: P14 :: nil) (P1 :: P8 :: nil) 4 2 3 HP1P8P10P12P13P14mtmp HP1P8mtmp HP1P8P12P13Mtmp Hincl); apply HT.
}
try clear HP1P8P10P14m2. try clear HP1P8P10P12P13P14M4. try clear HP1P8P10P12P13P14m4. 

assert(HP1P14m2 : rk(P1 :: P14 :: nil) >= 2).
{
	assert(HP8P10P14Mtmp : rk(P8 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP8P10P14eq HP8P10P14M2).
	assert(HP1P8P10P14mtmp : rk(P1 :: P8 :: P10 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P8P10P14eq HP1P8P10P14m3).
	assert(HP14mtmp : rk(P14 :: nil) >= 1) by (solve_hyps_min HP14eq HP14m1).
	assert(Hincl : incl (P14 :: nil) (list_inter (P1 :: P14 :: nil) (P8 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P10 :: P14 :: nil) (P1 :: P14 :: P8 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P14 :: P8 :: P10 :: P14 :: nil) ((P1 :: P14 :: nil) ++ (P8 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P8P10P14mtmp;try rewrite HT2 in HP1P8P10P14mtmp.
	assert(HT := rule_2 (P1 :: P14 :: nil) (P8 :: P10 :: P14 :: nil) (P14 :: nil) 3 1 2 HP1P8P10P14mtmp HP14mtmp HP8P10P14Mtmp Hincl);apply HT.
}
try clear HP1P14m1. try clear HP1P8P10P14M3. try clear HP1P8P10P14m3. 

assert(HP3P6P8P10P11P12P14m2 : rk(P3 :: P6 :: P8 :: P10 :: P11 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: nil) (P3 :: P6 :: P8 :: P10 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: nil) (P3 :: P6 :: P8 :: P10 :: P11 :: P12 :: P14 :: nil) 2 2 HP3P6mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6P8P10P11P12P14m1. 

assert(HP3P6P8P10P11P12P14m3 : rk(P3 :: P6 :: P8 :: P10 :: P11 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP3P6P11mtmp : rk(P3 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP3P6P11eq HP3P6P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P8 :: P10 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P8 :: P10 :: P11 :: P12 :: P14 :: nil) 3 3 HP3P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6P8P10P11P12P14m2. 

assert(HP3P8P10P12P14m2 : rk(P3 :: P8 :: P10 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP6P10P11Mtmp : rk(P6 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP6P10P11eq HP6P10P11M2).
	assert(HP3P6P8P10P11P12P14mtmp : rk(P3 :: P6 :: P8 :: P10 :: P11 :: P12 :: P14 :: nil) >= 3) by (solve_hyps_min HP3P6P8P10P11P12P14eq HP3P6P8P10P11P12P14m3).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P6 :: P10 :: P11 :: nil) (P3 :: P8 :: P10 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P6 :: P8 :: P10 :: P11 :: P12 :: P14 :: nil) (P6 :: P10 :: P11 :: P3 :: P8 :: P10 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P10 :: P11 :: P3 :: P8 :: P10 :: P12 :: P14 :: nil) ((P6 :: P10 :: P11 :: nil) ++ (P3 :: P8 :: P10 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP3P6P8P10P11P12P14mtmp;try rewrite HT2 in HP3P6P8P10P11P12P14mtmp.
	assert(HT := rule_4 (P6 :: P10 :: P11 :: nil) (P3 :: P8 :: P10 :: P12 :: P14 :: nil) (P10 :: nil) 3 1 2 HP3P6P8P10P11P12P14mtmp HP10mtmp HP6P10P11Mtmp Hincl); apply HT.
}
try clear HP3P8P10P12P14m1. try clear HP3P6P8P10P11P12P14M4. try clear HP3P6P8P10P11P12P14m3. 

assert(HP3P8P10P12P14M3 : rk(P3 :: P8 :: P10 :: P12 :: P14 :: nil) <= 3).
{
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(HP8P10P14Mtmp : rk(P8 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP8P10P14eq HP8P10P14M2).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P3 :: P10 :: P12 :: nil) (P8 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P8 :: P10 :: P12 :: P14 :: nil) (P3 :: P10 :: P12 :: P8 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P10 :: P12 :: P8 :: P10 :: P14 :: nil) ((P3 :: P10 :: P12 :: nil) ++ (P8 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P10 :: P12 :: nil) (P8 :: P10 :: P14 :: nil) (P10 :: nil) 2 2 1 HP3P10P12Mtmp HP8P10P14Mtmp HP10mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P8P10P12P14M4. 

assert(HP2P3P12m3 : rk(P2 :: P3 :: P12 :: nil) >= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P3 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P12 :: nil) ((P1 :: nil) ++ (P2 :: P3 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P12mtmp;try rewrite HT2 in HP1P2P3P12mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P3 :: P12 :: nil) (nil) 4 0 1 HP1P2P3P12mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}
try clear HP2P3P12m1. 

assert(HP3P12m2 : rk(P3 :: P12 :: nil) >= 2).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP2P3P12mtmp : rk(P2 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP2P3P12eq HP2P3P12m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P3 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P12 :: nil) ((P2 :: nil) ++ (P3 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P12mtmp;try rewrite HT2 in HP2P3P12mtmp.
	assert(HT := rule_4 (P2 :: nil) (P3 :: P12 :: nil) (nil) 3 0 1 HP2P3P12mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}
try clear HP3P12m1. 

assert(HP3P8P12P14m2 : rk(P3 :: P8 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP3P12mtmp : rk(P3 :: P12 :: nil) >= 2) by (solve_hyps_min HP3P12eq HP3P12m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P12 :: nil) (P3 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P12 :: nil) (P3 :: P8 :: P12 :: P14 :: nil) 2 2 HP3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP3P8P12P14m1. 

assert(HP3P8P12P14M3 : rk(P3 :: P8 :: P12 :: P14 :: nil) <= 3).
{
	assert(HP3P8P10P12P14Mtmp : rk(P3 :: P8 :: P10 :: P12 :: P14 :: nil) <= 3) by (solve_hyps_max HP3P8P10P12P14eq HP3P8P10P12P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P3 :: P8 :: P12 :: P14 :: nil) (P3 :: P8 :: P10 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P3 :: P8 :: P12 :: P14 :: nil) (P3 :: P8 :: P10 :: P12 :: P14 :: nil) 3 3 HP3P8P10P12P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP3P8P12P14M4. try clear HP3P8P10P12P14M3. try clear HP3P8P10P12P14m2. 

assert(HP1P2P3P4P7P11P12m2 : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P7P11P12m1. 

assert(HP1P2P3P4P7P11P12m3 : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P7P11P12m2. 

assert(HP1P2P3P4P7P11P12m4 : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P7P11P12m3. 

assert(HP1P4P7P11P12m2 : rk(P1 :: P4 :: P7 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P7 :: P11 :: P12 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P7P11P12m1. 

assert(HP1P4P7P11P12M3 : rk(P1 :: P4 :: P7 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP1P4P7Mtmp : rk(P1 :: P4 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P4P7eq HP1P4P7M2).
	assert(HP7P11P12Mtmp : rk(P7 :: P11 :: P12 :: nil) <= 2) by (solve_hyps_max HP7P11P12eq HP7P11P12M2).
	assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m1).
	assert(Hincl : incl (P7 :: nil) (list_inter (P1 :: P4 :: P7 :: nil) (P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P7 :: P11 :: P12 :: nil) (P1 :: P4 :: P7 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P7 :: P7 :: P11 :: P12 :: nil) ((P1 :: P4 :: P7 :: nil) ++ (P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P7 :: nil) (P7 :: P11 :: P12 :: nil) (P7 :: nil) 2 2 1 HP1P4P7Mtmp HP7P11P12Mtmp HP7mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP7M1. try clear HP7m1. try clear HP1P4P7P11P12M4. 

assert(HP1P4P7P11P12m3 : rk(P1 :: P4 :: P7 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3P4P11Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P11eq HP1P2P3P4P11M4).
	assert(HP1P2P3P4P7P11P12mtmp : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P7P11P12eq HP1P2P3P4P7P11P12m4).
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P4 :: P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P4 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P4 :: P7 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P4 :: P11 :: nil) ++ (P1 :: P4 :: P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P7P11P12mtmp;try rewrite HT2 in HP1P2P3P4P7P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P4 :: P7 :: P11 :: P12 :: nil) (P1 :: P4 :: P11 :: nil) 4 3 4 HP1P2P3P4P7P11P12mtmp HP1P4P11mtmp HP1P2P3P4P11Mtmp Hincl); apply HT.
}
try clear HP1P4P7P11P12m2. try clear HP1P2P3P4P7P11P12M4. try clear HP1P2P3P4P7P11P12m4. 

assert(HP4P5P6P11m2 : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P11 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P11m1. 

assert(HP4P5P6P11m3 : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P11 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P11m2. 

assert(HP4P5P6P11m4 : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P4P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P13eq HP1P2P3P4P5P6P13M3).
	assert(HP1P2P3P4P5P6P11P13mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P11P13eq HP1P2P3P4P5P6P11P13m4).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (list_inter (P4 :: P5 :: P6 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) (P4 :: P5 :: P6 :: P11 :: P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P11 :: P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) ((P4 :: P5 :: P6 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P11P13mtmp;try rewrite HT2 in HP1P2P3P4P5P6P11P13mtmp.
	assert(HT := rule_2 (P4 :: P5 :: P6 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) (P4 :: P5 :: P6 :: nil) 4 3 3 HP1P2P3P4P5P6P11P13mtmp HP4P5P6mtmp HP1P2P3P4P5P6P13Mtmp Hincl);apply HT.
}
try clear HP4P5P6P11m3. 

assert(HP4P5P6P7P11P13m2 : rk(P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P7P11P13m1. 

assert(HP4P5P6P7P11P13m3 : rk(P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P7P11P13m2. 

assert(HP4P5P6P7P11P13m4 : rk(P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 4).
{
	assert(HP4P5P6P11mtmp : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 4) by (solve_hyps_min HP4P5P6P11eq HP4P5P6P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) 4 4 HP4P5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P7P11P13m3. 

assert(HP4P5P6P7m2 : rk(P4 :: P5 :: P6 :: P7 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P7 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P7m1. 

assert(HP4P5P6P7m3 : rk(P4 :: P5 :: P6 :: P7 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P7m2. 

assert(HP4P5P6P7M3 : rk(P4 :: P5 :: P6 :: P7 :: nil) <= 3).
{
	assert(HP1P2P3P4P5P6P7Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P7eq HP1P2P3P4P5P6P7M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: P7 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P4 :: P5 :: P6 :: P7 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: nil) 3 3 HP1P2P3P4P5P6P7Mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P7M4. try clear HP1P2P3P4P5P6P7M3. try clear HP1P2P3P4P5P6P7m3. 

assert(HP4P5P6P7P13m2 : rk(P4 :: P5 :: P6 :: P7 :: P13 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P7 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P7 :: P13 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P7P13m1. 

assert(HP4P5P6P7P13m3 : rk(P4 :: P5 :: P6 :: P7 :: P13 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P13 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P7P13m2. 

assert(HP4P5P6P7P13M3 : rk(P4 :: P5 :: P6 :: P7 :: P13 :: nil) <= 3).
{
	assert(HP4P5P6P7Mtmp : rk(P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP4P5P6P7eq HP4P5P6P7M3).
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hincl : incl (P5 :: P6 :: nil) (list_inter (P4 :: P5 :: P6 :: P7 :: nil) (P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P7 :: P13 :: nil) (P4 :: P5 :: P6 :: P7 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P7 :: P5 :: P6 :: P13 :: nil) ((P4 :: P5 :: P6 :: P7 :: nil) ++ (P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P5 :: P6 :: P7 :: nil) (P5 :: P6 :: P13 :: nil) (P5 :: P6 :: nil) 3 2 2 HP4P5P6P7Mtmp HP5P6P13Mtmp HP5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P5P6P7M3. try clear HP4P5P6P7m3. try clear HP4P5P6P7P13M4. 

assert(HP4P7P11m2 : rk(P4 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP4P7mtmp : rk(P4 :: P7 :: nil) >= 2) by (solve_hyps_min HP4P7eq HP4P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P7 :: nil) (P4 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P7 :: nil) (P4 :: P7 :: P11 :: nil) 2 2 HP4P7mtmp Hcomp Hincl);apply HT.
}
try clear HP4P7P11m1. 

assert(HP4P7P11m3 : rk(P4 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP4P5P6P7P13Mtmp : rk(P4 :: P5 :: P6 :: P7 :: P13 :: nil) <= 3) by (solve_hyps_max HP4P5P6P7P13eq HP4P5P6P7P13M3).
	assert(HP4P5P6P7P11P13mtmp : rk(P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP4P5P6P7P11P13eq HP4P5P6P7P11P13m4).
	assert(HP4P7mtmp : rk(P4 :: P7 :: nil) >= 2) by (solve_hyps_min HP4P7eq HP4P7m2).
	assert(Hincl : incl (P4 :: P7 :: nil) (list_inter (P4 :: P7 :: P11 :: nil) (P4 :: P5 :: P6 :: P7 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P7 :: P11 :: P13 :: nil) (P4 :: P7 :: P11 :: P4 :: P5 :: P6 :: P7 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P7 :: P11 :: P4 :: P5 :: P6 :: P7 :: P13 :: nil) ((P4 :: P7 :: P11 :: nil) ++ (P4 :: P5 :: P6 :: P7 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P7P11P13mtmp;try rewrite HT2 in HP4P5P6P7P11P13mtmp.
	assert(HT := rule_2 (P4 :: P7 :: P11 :: nil) (P4 :: P5 :: P6 :: P7 :: P13 :: nil) (P4 :: P7 :: nil) 4 2 3 HP4P5P6P7P11P13mtmp HP4P7mtmp HP4P5P6P7P13Mtmp Hincl);apply HT.
}
try clear HP4P7P11m2. try clear HP4P5P6P7P13M3. try clear HP4P5P6P7P13m3. try clear HP4P5P6P7P11P13M4. try clear HP4P5P6P7P11P13m4. 

assert(HP1P2P3P4P7P11m2 : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P7P11m1. 

assert(HP1P2P3P4P7P11m3 : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P7P11m2. 

assert(HP1P2P3P4P7P11m4 : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P7P11m3. 

assert(HP1P4P7P11m2 : rk(P1 :: P4 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P7 :: P11 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P7P11m1. 

assert(HP1P4P7P11M3 : rk(P1 :: P4 :: P7 :: P11 :: nil) <= 3).
{
	assert(HP1P4P7Mtmp : rk(P1 :: P4 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P4P7eq HP1P4P7M2).
	assert(HP11Mtmp : rk(P11 :: nil) <= 1) by (solve_hyps_max HP11eq HP11M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P4 :: P7 :: nil) (P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P7 :: P11 :: nil) (P1 :: P4 :: P7 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P7 :: P11 :: nil) ((P1 :: P4 :: P7 :: nil) ++ (P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P7 :: nil) (P11 :: nil) (nil) 2 1 0 HP1P4P7Mtmp HP11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P7M2. try clear HP1P4P7m2. try clear HP11M1. try clear HP11m1. try clear HP1P4P7P11M4. 

assert(HP1P4P7P11m3 : rk(P1 :: P4 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P4P11Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P11eq HP1P2P3P4P11M4).
	assert(HP1P2P3P4P7P11mtmp : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P7P11eq HP1P2P3P4P7P11m4).
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P4 :: P7 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P7 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P4 :: P7 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P4 :: P7 :: P11 :: nil) ((P1 :: P2 :: P3 :: P4 :: P11 :: nil) ++ (P1 :: P4 :: P7 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P7P11mtmp;try rewrite HT2 in HP1P2P3P4P7P11mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P4 :: P7 :: P11 :: nil) (P1 :: P4 :: P11 :: nil) 4 3 4 HP1P2P3P4P7P11mtmp HP1P4P11mtmp HP1P2P3P4P11Mtmp Hincl); apply HT.
}
try clear HP1P4P7P11m2. try clear HP1P2P3P4P7P11M4. try clear HP1P2P3P4P7P11m4. 

assert(HP4P7P11P12M3 : rk(P4 :: P7 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M1).
	assert(HP7P11P12Mtmp : rk(P7 :: P11 :: P12 :: nil) <= 2) by (solve_hyps_max HP7P11P12eq HP7P11P12M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: nil) (P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P7 :: P11 :: P12 :: nil) (P4 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P7 :: P11 :: P12 :: nil) ((P4 :: nil) ++ (P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: nil) (P7 :: P11 :: P12 :: nil) (nil) 1 2 0 HP4Mtmp HP7P11P12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P7P11P12M4. 

assert(HP4P7P11P12m2 : rk(P4 :: P7 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP4P7mtmp : rk(P4 :: P7 :: nil) >= 2) by (solve_hyps_min HP4P7eq HP4P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P7 :: nil) (P4 :: P7 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P7 :: nil) (P4 :: P7 :: P11 :: P12 :: nil) 2 2 HP4P7mtmp Hcomp Hincl);apply HT.
}
try clear HP4P7M2. try clear HP4P7m2. try clear HP4P7P11P12m1. 

assert(HP4P7P11P12m3 : rk(P4 :: P7 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P4P7P11Mtmp : rk(P1 :: P4 :: P7 :: P11 :: nil) <= 3) by (solve_hyps_max HP1P4P7P11eq HP1P4P7P11M3).
	assert(HP1P4P7P11P12mtmp : rk(P1 :: P4 :: P7 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P4P7P11P12eq HP1P4P7P11P12m3).
	assert(HP4P7P11mtmp : rk(P4 :: P7 :: P11 :: nil) >= 3) by (solve_hyps_min HP4P7P11eq HP4P7P11m3).
	assert(Hincl : incl (P4 :: P7 :: P11 :: nil) (list_inter (P1 :: P4 :: P7 :: P11 :: nil) (P4 :: P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P7 :: P11 :: P12 :: nil) (P1 :: P4 :: P7 :: P11 :: P4 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P7 :: P11 :: P4 :: P7 :: P11 :: P12 :: nil) ((P1 :: P4 :: P7 :: P11 :: nil) ++ (P4 :: P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P7P11P12mtmp;try rewrite HT2 in HP1P4P7P11P12mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P7 :: P11 :: nil) (P4 :: P7 :: P11 :: P12 :: nil) (P4 :: P7 :: P11 :: nil) 3 3 3 HP1P4P7P11P12mtmp HP4P7P11mtmp HP1P4P7P11Mtmp Hincl); apply HT.
}
try clear HP1P4P7P11M3. try clear HP1P4P7P11m3. try clear HP4P7P11P12m2. try clear HP4P7P11M3. try clear HP4P7P11m3. try clear HP1P4P7P11P12M3. try clear HP1P4P7P11P12m3. 

assert(HP1P2P3P4P11P12m2 : rk(P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P11P12m1. 

assert(HP1P2P3P4P11P12m3 : rk(P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P11P12m2. 

assert(HP1P2P3P4P11P12m4 : rk(P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P11P12m3. 

assert(HP4P11m2 : rk(P4 :: P11 :: nil) >= 2).
{
	assert(HP1P2P3P4P5P6P13Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P5P6P13eq HP1P2P3P4P5P6P13M3).
	assert(HP1P2P3P4P5P6P11P13mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P11P13eq HP1P2P3P4P5P6P11P13m4).
	assert(HP4mtmp : rk(P4 :: nil) >= 1) by (solve_hyps_min HP4eq HP4m1).
	assert(Hincl : incl (P4 :: nil) (list_inter (P4 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P11 :: P13 :: nil) (P4 :: P11 :: P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P11 :: P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) ((P4 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P11P13mtmp;try rewrite HT2 in HP1P2P3P4P5P6P11P13mtmp.
	assert(HT := rule_2 (P4 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P13 :: nil) (P4 :: nil) 4 1 3 HP1P2P3P4P5P6P11P13mtmp HP4mtmp HP1P2P3P4P5P6P13Mtmp Hincl);apply HT.
}
try clear HP4P11m1. try clear HP1P2P3P4P5P6P13M3. try clear HP1P2P3P4P5P6P13m3. try clear HP4M1. try clear HP4m1. try clear HP1P2P3P4P5P6P11P13M4. try clear HP1P2P3P4P5P6P11P13m4. 

assert(HP4P11P12m2 : rk(P4 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2P3P4P11Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P11eq HP1P2P3P4P11M4).
	assert(HP1P2P3P4P11P12mtmp : rk(P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P11P12eq HP1P2P3P4P11P12m4).
	assert(HP4P11mtmp : rk(P4 :: P11 :: nil) >= 2) by (solve_hyps_min HP4P11eq HP4P11m2).
	assert(Hincl : incl (P4 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P4 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P4 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P11 :: P4 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P4 :: P11 :: nil) ++ (P4 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P11P12mtmp;try rewrite HT2 in HP1P2P3P4P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P4 :: P11 :: P12 :: nil) (P4 :: P11 :: nil) 4 2 4 HP1P2P3P4P11P12mtmp HP4P11mtmp HP1P2P3P4P11Mtmp Hincl); apply HT.
}
try clear HP4P11P12m1. try clear HP1P2P3P4P11P12M4. try clear HP1P2P3P4P11P12m4. 

assert(HP4P11P12m3 : rk(P4 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP7P11P12Mtmp : rk(P7 :: P11 :: P12 :: nil) <= 2) by (solve_hyps_max HP7P11P12eq HP7P11P12M2).
	assert(HP4P7P11P12mtmp : rk(P4 :: P7 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP4P7P11P12eq HP4P7P11P12m3).
	assert(HP11P12mtmp : rk(P11 :: P12 :: nil) >= 2) by (solve_hyps_min HP11P12eq HP11P12m2).
	assert(Hincl : incl (P11 :: P12 :: nil) (list_inter (P4 :: P11 :: P12 :: nil) (P7 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P7 :: P11 :: P12 :: nil) (P4 :: P11 :: P12 :: P7 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P11 :: P12 :: P7 :: P11 :: P12 :: nil) ((P4 :: P11 :: P12 :: nil) ++ (P7 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P7P11P12mtmp;try rewrite HT2 in HP4P7P11P12mtmp.
	assert(HT := rule_2 (P4 :: P11 :: P12 :: nil) (P7 :: P11 :: P12 :: nil) (P11 :: P12 :: nil) 3 2 2 HP4P7P11P12mtmp HP11P12mtmp HP7P11P12Mtmp Hincl);apply HT.
}
try clear HP4P11P12m2. try clear HP7P11P12M2. try clear HP7P11P12m2. try clear HP11P12M2. try clear HP11P12m2. try clear HP4P7P11P12M3. try clear HP4P7P11P12m3. 

assert(HP1P2P3P4P8P11P12m2 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8P11P12m1. 

assert(HP1P2P3P4P8P11P12m3 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8P11P12m2. 

assert(HP1P2P3P4P8P11P12m4 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8P11P12m3. 

assert(HP4P8P11P12m2 : rk(P4 :: P8 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2P3P4P11Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P11eq HP1P2P3P4P11M4).
	assert(HP1P2P3P4P8P11P12mtmp : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P8P11P12eq HP1P2P3P4P8P11P12m4).
	assert(HP4P11mtmp : rk(P4 :: P11 :: nil) >= 2) by (solve_hyps_min HP4P11eq HP4P11m2).
	assert(Hincl : incl (P4 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P4 :: P8 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P8 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P4 :: P8 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P11 :: P4 :: P8 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P4 :: P11 :: nil) ++ (P4 :: P8 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P8P11P12mtmp;try rewrite HT2 in HP1P2P3P4P8P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P4 :: P8 :: P11 :: P12 :: nil) (P4 :: P11 :: nil) 4 2 4 HP1P2P3P4P8P11P12mtmp HP4P11mtmp HP1P2P3P4P11Mtmp Hincl); apply HT.
}
try clear HP4P8P11P12m1. try clear HP4P11M2. try clear HP4P11m2. try clear HP1P2P3P4P8P11P12M4. try clear HP1P2P3P4P8P11P12m4. 

assert(HP4P8P11P12M3 : rk(P4 :: P8 :: P11 :: P12 :: nil) <= 3).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP12Mtmp : rk(P12 :: nil) <= 1) by (solve_hyps_max HP12eq HP12M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: P8 :: P11 :: nil) (P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P8 :: P11 :: P12 :: nil) (P4 :: P8 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P12 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P8 :: P11 :: nil) (P12 :: nil) (nil) 2 1 0 HP4P8P11Mtmp HP12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP12M1. try clear HP12m1. try clear HP4P8P11P12M4. 

assert(HP4P8P11P12m3 : rk(P4 :: P8 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP4P11P12mtmp : rk(P4 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP4P11P12eq HP4P11P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P11 :: P12 :: nil) (P4 :: P8 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P11 :: P12 :: nil) (P4 :: P8 :: P11 :: P12 :: nil) 3 3 HP4P11P12mtmp Hcomp Hincl);apply HT.
}
try clear HP4P11P12M3. try clear HP4P11P12m3. try clear HP4P8P11P12m2. 

assert(HP8P12m2 : rk(P8 :: P12 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP4P8P11P12mtmp : rk(P4 :: P8 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP4P8P11P12eq HP4P8P11P12m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P8 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P8 :: P11 :: P12 :: nil) (P4 :: P8 :: P11 :: P8 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P8 :: P12 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P8 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P8P11P12mtmp;try rewrite HT2 in HP4P8P11P12mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P8 :: P12 :: nil) (P8 :: nil) 3 1 2 HP4P8P11P12mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP8P12m1. try clear HP4P8P11P12M3. try clear HP4P8P11P12m3. 

assert(HP1P3P8P12P14m2 : rk(P1 :: P3 :: P8 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P12 :: P14 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P12P14m1. 

assert(HP1P3P8P12P14m3 : rk(P1 :: P3 :: P8 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P3P12mtmp : rk(P1 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P12eq HP1P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P12 :: P14 :: nil) 3 3 HP1P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P12P14m2. 

assert(HP1P3P8P12P14M3 : rk(P1 :: P3 :: P8 :: P12 :: P14 :: nil) <= 3).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP3P8P12P14Mtmp : rk(P3 :: P8 :: P12 :: P14 :: nil) <= 3) by (solve_hyps_max HP3P8P12P14eq HP3P8P12P14M3).
	assert(HP8P12mtmp : rk(P8 :: P12 :: nil) >= 2) by (solve_hyps_min HP8P12eq HP8P12m2).
	assert(Hincl : incl (P8 :: P12 :: nil) (list_inter (P1 :: P8 :: P12 :: nil) (P3 :: P8 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P8 :: P12 :: P14 :: nil) (P1 :: P8 :: P12 :: P3 :: P8 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P3 :: P8 :: P12 :: P14 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P3 :: P8 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P8 :: P12 :: nil) (P3 :: P8 :: P12 :: P14 :: nil) (P8 :: P12 :: nil) 2 3 2 HP1P8P12Mtmp HP3P8P12P14Mtmp HP8P12mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P8P12P14M3. try clear HP3P8P12P14m2. try clear HP1P3P8P12P14M4. 

assert(HP1P3P8P14m2 : rk(P1 :: P3 :: P8 :: P14 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P14 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P14m1. 

assert(HP1P3P8P14m3 : rk(P1 :: P3 :: P8 :: P14 :: nil) >= 3).
{
	assert(HP1P3P8mtmp : rk(P1 :: P3 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P3P8eq HP1P3P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P8 :: nil) (P1 :: P3 :: P8 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P8 :: nil) (P1 :: P3 :: P8 :: P14 :: nil) 3 3 HP1P3P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8M3. try clear HP1P3P8m3. try clear HP1P3P8P14m2. 

assert(HP1P3P8P14M3 : rk(P1 :: P3 :: P8 :: P14 :: nil) <= 3).
{
	assert(HP1P3P8P12P14Mtmp : rk(P1 :: P3 :: P8 :: P12 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P3P8P12P14eq HP1P3P8P12P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P8 :: P14 :: nil) (P1 :: P3 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P3 :: P8 :: P14 :: nil) (P1 :: P3 :: P8 :: P12 :: P14 :: nil) 3 3 HP1P3P8P12P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P14M4. try clear HP1P3P8P12P14M3. try clear HP1P3P8P12P14m3. 

assert(HP4P6m2 : rk(P4 :: P6 :: nil) >= 2).
{
	assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M1).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: nil) (P4 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: nil) (P5 :: P4 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P4 :: P6 :: nil) ((P5 :: nil) ++ (P4 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6mtmp;try rewrite HT2 in HP4P5P6mtmp.
	assert(HT := rule_4 (P5 :: nil) (P4 :: P6 :: nil) (nil) 3 0 1 HP4P5P6mtmp Hmtmp HP5Mtmp Hincl); apply HT.
}
try clear HP5M1. try clear HP5m1. try clear HP4P6m1. 

assert(HP1P4P5P6P14m2 : rk(P1 :: P4 :: P5 :: P6 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P6 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P6 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P6P14m1. 

assert(HP1P4P5P6P14m3 : rk(P1 :: P4 :: P5 :: P6 :: P14 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: P14 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P6P14m2. 

assert(HP1P4P5P6P14M3 : rk(P1 :: P4 :: P5 :: P6 :: P14 :: nil) <= 3).
{
	assert(HP1P4P5P6Mtmp : rk(P1 :: P4 :: P5 :: P6 :: nil) <= 3) by (solve_hyps_max HP1P4P5P6eq HP1P4P5P6M3).
	assert(HP4P6P14Mtmp : rk(P4 :: P6 :: P14 :: nil) <= 2) by (solve_hyps_max HP4P6P14eq HP4P6P14M2).
	assert(HP4P6mtmp : rk(P4 :: P6 :: nil) >= 2) by (solve_hyps_min HP4P6eq HP4P6m2).
	assert(Hincl : incl (P4 :: P6 :: nil) (list_inter (P1 :: P4 :: P5 :: P6 :: nil) (P4 :: P6 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P6 :: P14 :: nil) (P1 :: P4 :: P5 :: P6 :: P4 :: P6 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P6 :: P4 :: P6 :: P14 :: nil) ((P1 :: P4 :: P5 :: P6 :: nil) ++ (P4 :: P6 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P5 :: P6 :: nil) (P4 :: P6 :: P14 :: nil) (P4 :: P6 :: nil) 3 2 2 HP1P4P5P6Mtmp HP4P6P14Mtmp HP4P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P6M3. try clear HP1P4P5P6m3. try clear HP4P6P14M2. try clear HP4P6P14m2. try clear HP4P6M2. try clear HP4P6m2. try clear HP1P4P5P6P14M4. 

assert(HP1P4P5P6P13P14m2 : rk(P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P6P13P14m1. 

assert(HP1P4P5P6P13P14m3 : rk(P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P6P13P14m2. 

assert(HP1P4P5P6P13P14M3 : rk(P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil) <= 3).
{
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP1P4P5P6P14Mtmp : rk(P1 :: P4 :: P5 :: P6 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P5P6P14eq HP1P4P5P6P14M3).
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hincl : incl (P5 :: P6 :: nil) (list_inter (P5 :: P6 :: P13 :: nil) (P1 :: P4 :: P5 :: P6 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil) (P5 :: P6 :: P13 :: P1 :: P4 :: P5 :: P6 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P13 :: P1 :: P4 :: P5 :: P6 :: P14 :: nil) ((P5 :: P6 :: P13 :: nil) ++ (P1 :: P4 :: P5 :: P6 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: P6 :: P13 :: nil) (P1 :: P4 :: P5 :: P6 :: P14 :: nil) (P5 :: P6 :: nil) 2 3 2 HP5P6P13Mtmp HP1P4P5P6P14Mtmp HP5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P6P14M3. try clear HP1P4P5P6P14m3. try clear HP1P4P5P6P13P14M4. 

assert(HP1P4P5P13P14m2 : rk(P1 :: P4 :: P5 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P13 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P13P14m1. 

assert(HP1P4P5P13P14M3 : rk(P1 :: P4 :: P5 :: P13 :: P14 :: nil) <= 3).
{
	assert(HP1P4P5P6P13P14Mtmp : rk(P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P5P6P13P14eq HP1P4P5P6P13P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P5 :: P13 :: P14 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P4 :: P5 :: P13 :: P14 :: nil) (P1 :: P4 :: P5 :: P6 :: P13 :: P14 :: nil) 3 3 HP1P4P5P6P13P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P13P14M4. try clear HP1P4P5P6P13P14M3. try clear HP1P4P5P6P13P14m3. 

assert(HP1P4P5P13P14P15m2 : rk(P1 :: P4 :: P5 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P13P14P15m1. 

assert(HP1P4P5P13P14P15M3 : rk(P1 :: P4 :: P5 :: P13 :: P14 :: P15 :: nil) <= 3).
{
	assert(HP1P4P5P13P14Mtmp : rk(P1 :: P4 :: P5 :: P13 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P5P13P14eq HP1P4P5P13P14M3).
	assert(HP4P5P15Mtmp : rk(P4 :: P5 :: P15 :: nil) <= 2) by (solve_hyps_max HP4P5P15eq HP4P5P15M2).
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P1 :: P4 :: P5 :: P13 :: P14 :: nil) (P4 :: P5 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P13 :: P14 :: P15 :: nil) (P1 :: P4 :: P5 :: P13 :: P14 :: P4 :: P5 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P13 :: P14 :: P4 :: P5 :: P15 :: nil) ((P1 :: P4 :: P5 :: P13 :: P14 :: nil) ++ (P4 :: P5 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P5 :: P13 :: P14 :: nil) (P4 :: P5 :: P15 :: nil) (P4 :: P5 :: nil) 3 2 2 HP1P4P5P13P14Mtmp HP4P5P15Mtmp HP4P5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P13P14M3. try clear HP1P4P5P13P14m2. try clear HP4P5P15M2. try clear HP4P5P15m2. try clear HP1P4P5P13P14P15M4. 

assert(HP1P13P14P15M3 : rk(P1 :: P13 :: P14 :: P15 :: nil) <= 3).
{
	assert(HP1P4P5P13P14P15Mtmp : rk(P1 :: P4 :: P5 :: P13 :: P14 :: P15 :: nil) <= 3) by (solve_hyps_max HP1P4P5P13P14P15eq HP1P4P5P13P14P15M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P13 :: P14 :: P15 :: nil) (P1 :: P4 :: P5 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P13 :: P14 :: P15 :: nil) (P1 :: P4 :: P5 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P4P5P13P14P15Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P13P14P15M4. try clear HP1P4P5P13P14P15M3. try clear HP1P4P5P13P14P15m2. 

assert(HP1P13P14P15m2 : rk(P1 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P13mtmp : rk(P1 :: P13 :: nil) >= 2) by (solve_hyps_min HP1P13eq HP1P13m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P13 :: nil) (P1 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P13 :: nil) (P1 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P13mtmp Hcomp Hincl);apply HT.
}
try clear HP1P13P14P15m1. 

assert(HP1P13P14P15m3 : rk(P1 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P3P8P14Mtmp : rk(P1 :: P3 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P3P8P14eq HP1P3P8P14M3).
	assert(HP1P3P8P13P14P15mtmp : rk(P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P3P8P13P14P15eq HP1P3P8P13P14P15m4).
	assert(HP1P14mtmp : rk(P1 :: P14 :: nil) >= 2) by (solve_hyps_min HP1P14eq HP1P14m2).
	assert(Hincl : incl (P1 :: P14 :: nil) (list_inter (P1 :: P3 :: P8 :: P14 :: nil) (P1 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) (P1 :: P3 :: P8 :: P14 :: P1 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P8 :: P14 :: P1 :: P13 :: P14 :: P15 :: nil) ((P1 :: P3 :: P8 :: P14 :: nil) ++ (P1 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P8P13P14P15mtmp;try rewrite HT2 in HP1P3P8P13P14P15mtmp.
	assert(HT := rule_4 (P1 :: P3 :: P8 :: P14 :: nil) (P1 :: P13 :: P14 :: P15 :: nil) (P1 :: P14 :: nil) 4 2 3 HP1P3P8P13P14P15mtmp HP1P14mtmp HP1P3P8P14Mtmp Hincl); apply HT.
}
try clear HP1P13P14P15m2. try clear HP1P14M2. try clear HP1P14m2. 

assert(HP1P2P3P8P9P12P13P14m2 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P12P13P14m1. 

assert(HP1P2P3P8P9P12P13P14m3 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P12P13P14m2. 

assert(HP1P2P3P8P9P12P13P14m4 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P12P13P14m3. 

assert(HP2P3m2 : rk(P2 :: P3 :: nil) >= 2).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: nil) ((P1 :: nil) ++ (P2 :: P3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3mtmp;try rewrite HT2 in HP1P2P3mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P3 :: nil) (nil) 3 0 1 HP1P2P3mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}
try clear HP2P3m1. 

assert(HP2P3P8P9P12P13P14m2 : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8P9P12P13P14m1. 

assert(HP2P3P8P9P12P13P14m3 : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP2P3P12mtmp : rk(P2 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP2P3P12eq HP2P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) 3 3 HP2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8P9P12P13P14m2. 

assert(HP2P3P8P9P12P13P14m4 : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P2P3P8P9P12P13P14mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P9P12P13P14eq HP1P2P3P8P9P12P13P14m4).
	assert(HP8P12mtmp : rk(P8 :: P12 :: nil) >= 2) by (solve_hyps_min HP8P12eq HP8P12m2).
	assert(Hincl : incl (P8 :: P12 :: nil) (list_inter (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P9P12P13P14mtmp;try rewrite HT2 in HP1P2P3P8P9P12P13P14mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) (P8 :: P12 :: nil) 4 2 2 HP1P2P3P8P9P12P13P14mtmp HP8P12mtmp HP1P8P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P12P13P14m3. 

assert(HP1P2P3P5P9P11m2 : rk(P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P9P11m1. 

assert(HP1P2P3P5P9P11m3 : rk(P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P9P11m2. 

assert(HP1P2P3P5P9P11m4 : rk(P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P9P11m3. 

assert(HP2P5P9P11M3 : rk(P2 :: P5 :: P9 :: P11 :: nil) <= 3).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP5P9P11Mtmp : rk(P5 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP5P9P11eq HP5P9P11M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P5 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P9 :: P11 :: nil) (P2 :: P5 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P9 :: P11 :: nil) ((P2 :: nil) ++ (P5 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: nil) (P5 :: P9 :: P11 :: nil) (nil) 1 2 0 HP2Mtmp HP5P9P11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2M1. try clear HP2m1. try clear HP2P5P9P11M4. 

assert(HP2P5P9P11m2 : rk(P2 :: P5 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P9 :: P11 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5M2. try clear HP2P5m2. try clear HP2P5P9P11m1. 

assert(HP2P5P9P11m3 : rk(P2 :: P5 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP1P2P3P5P11Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P5P11eq HP1P2P3P5P11M4).
	assert(HP1P2P3P5P9P11mtmp : rk(P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P9P11eq HP1P2P3P5P9P11m4).
	assert(HP2P5P11mtmp : rk(P2 :: P5 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P5P11eq HP2P5P11m3).
	assert(Hincl : incl (P2 :: P5 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P9 :: P11 :: nil) (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P11 :: P2 :: P5 :: P9 :: P11 :: nil) ((P1 :: P2 :: P3 :: P5 :: P11 :: nil) ++ (P2 :: P5 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P9P11mtmp;try rewrite HT2 in HP1P2P3P5P9P11mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: P11 :: nil) (P2 :: P5 :: P9 :: P11 :: nil) (P2 :: P5 :: P11 :: nil) 4 3 4 HP1P2P3P5P9P11mtmp HP2P5P11mtmp HP1P2P3P5P11Mtmp Hincl); apply HT.
}
try clear HP1P2P3P5P11M4. try clear HP1P2P3P5P11m4. try clear HP2P5P9P11m2. try clear HP2P5P11M3. try clear HP2P5P11m3. try clear HP1P2P3P5P9P11M4. try clear HP1P2P3P5P9P11m4. 

assert(HP2P9m2 : rk(P2 :: P9 :: nil) >= 2).
{
	assert(HP5P9P11Mtmp : rk(P5 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP5P9P11eq HP5P9P11M2).
	assert(HP2P5P9P11mtmp : rk(P2 :: P5 :: P9 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P5P9P11eq HP2P5P9P11m3).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P2 :: P9 :: nil) (P5 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P9 :: P11 :: nil) (P2 :: P9 :: P5 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P5 :: P9 :: P11 :: nil) ((P2 :: P9 :: nil) ++ (P5 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P5P9P11mtmp;try rewrite HT2 in HP2P5P9P11mtmp.
	assert(HT := rule_2 (P2 :: P9 :: nil) (P5 :: P9 :: P11 :: nil) (P9 :: nil) 3 1 2 HP2P5P9P11mtmp HP9mtmp HP5P9P11Mtmp Hincl);apply HT.
}
try clear HP2P9m1. try clear HP5P9P11M2. try clear HP5P9P11m2. try clear HP9M1. try clear HP9m1. try clear HP2P5P9P11M3. try clear HP2P5P9P11m3. 

assert(HP2P3P8P9P13P14m2 : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8P9P13P14m1. 

assert(HP2P3P8P9P13P14m3 : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P2P3P8P9P12P13P14mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P9P12P13P14eq HP1P2P3P8P9P12P13P14m4).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P9P12P13P14mtmp;try rewrite HT2 in HP1P2P3P8P9P12P13P14mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) (P8 :: nil) 4 1 2 HP1P2P3P8P9P12P13P14mtmp HP8mtmp HP1P8P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P13P14m2. try clear HP1P2P3P8P9P12P13P14M4. try clear HP1P2P3P8P9P12P13P14m4. 

assert(HP2P3P8P9P13P14m4 : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP2P3P8P9P12P13P14mtmp : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP2P3P8P9P12P13P14eq HP2P3P8P9P12P13P14m4).
	assert(HP2P9mtmp : rk(P2 :: P9 :: nil) >= 2) by (solve_hyps_min HP2P9eq HP2P9m2).
	assert(Hincl : incl (P2 :: P9 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: nil) (P2 :: P9 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P8P9P12P13P14mtmp;try rewrite HT2 in HP2P3P8P9P12P13P14mtmp.
	assert(HT := rule_4 (P2 :: P9 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) (P2 :: P9 :: nil) 4 2 2 HP2P3P8P9P12P13P14mtmp HP2P9mtmp HP2P9P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P13P14m3. try clear HP2P3P8P9P12P13P14M4. try clear HP2P3P8P9P12P13P14m4. 

assert(HP1P2P3P9P12m2 : rk(P1 :: P2 :: P3 :: P9 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P12m1. 

assert(HP1P2P3P9P12m3 : rk(P1 :: P2 :: P3 :: P9 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P12m2. 

assert(HP1P2P3P9P12m4 : rk(P1 :: P2 :: P3 :: P9 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P12m3. 

assert(HP1P2P3P9m2 : rk(P1 :: P2 :: P3 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9m1. 

assert(HP1P2P3P9m3 : rk(P1 :: P2 :: P3 :: P9 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P9 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9m2. 

assert(HP1P2P3P9m4 : rk(P1 :: P2 :: P3 :: P9 :: nil) >= 4).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP1P2P3P9P12mtmp : rk(P1 :: P2 :: P3 :: P9 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P9P12eq HP1P2P3P9P12m4).
	assert(HP2P9mtmp : rk(P2 :: P9 :: nil) >= 2) by (solve_hyps_min HP2P9eq HP2P9m2).
	assert(Hincl : incl (P2 :: P9 :: nil) (list_inter (P1 :: P2 :: P3 :: P9 :: nil) (P2 :: P9 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P9 :: P12 :: nil) (P1 :: P2 :: P3 :: P9 :: P2 :: P9 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P9 :: P2 :: P9 :: P12 :: nil) ((P1 :: P2 :: P3 :: P9 :: nil) ++ (P2 :: P9 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P9P12mtmp;try rewrite HT2 in HP1P2P3P9P12mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: P9 :: nil) (P2 :: P9 :: P12 :: nil) (P2 :: P9 :: nil) 4 2 2 HP1P2P3P9P12mtmp HP2P9mtmp HP2P9P12Mtmp Hincl);apply HT.
}
try clear HP1P2P3P9m3. try clear HP1P2P3P9P12M4. try clear HP1P2P3P9P12m4. 

assert(HP1P2P3P9P13m2 : rk(P1 :: P2 :: P3 :: P9 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P13m1. 

assert(HP1P2P3P9P13m3 : rk(P1 :: P2 :: P3 :: P9 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P9 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P9 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P13m2. 

assert(HP1P2P3P9P13m4 : rk(P1 :: P2 :: P3 :: P9 :: P13 :: nil) >= 4).
{
	assert(HP1P2P3P9mtmp : rk(P1 :: P2 :: P3 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P3P9eq HP1P2P3P9m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: P9 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: P9 :: P13 :: nil) 4 4 HP1P2P3P9mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9M4. try clear HP1P2P3P9m4. try clear HP1P2P3P9P13m3. 

assert(HP9P13m2 : rk(P9 :: P13 :: nil) >= 2).
{
	assert(HP1P2P3P13Mtmp : rk(P1 :: P2 :: P3 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P13eq HP1P2P3P13M3).
	assert(HP1P2P3P9P13mtmp : rk(P1 :: P2 :: P3 :: P9 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P9P13eq HP1P2P3P9P13m4).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P1 :: P2 :: P3 :: P13 :: nil) (P9 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P9 :: P13 :: nil) (P1 :: P2 :: P3 :: P13 :: P9 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P13 :: P9 :: P13 :: nil) ((P1 :: P2 :: P3 :: P13 :: nil) ++ (P9 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P9P13mtmp;try rewrite HT2 in HP1P2P3P9P13mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P13 :: nil) (P9 :: P13 :: nil) (P13 :: nil) 4 1 3 HP1P2P3P9P13mtmp HP13mtmp HP1P2P3P13Mtmp Hincl); apply HT.
}
try clear HP9P13m1. try clear HP1P2P3P9P13M4. try clear HP1P2P3P9P13m4. 

assert(HP3P6P9P10P11P12P13m2 : rk(P3 :: P6 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: nil) (P3 :: P6 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: nil) (P3 :: P6 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) 2 2 HP3P6mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6P9P10P11P12P13m1. 

assert(HP3P6P9P10P11P12P13m3 : rk(P3 :: P6 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP3P6P11mtmp : rk(P3 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP3P6P11eq HP3P6P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) 3 3 HP3P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6P9P10P11P12P13m2. 

assert(HP3P9P10P12P13m2 : rk(P3 :: P9 :: P10 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP6P10P11Mtmp : rk(P6 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP6P10P11eq HP6P10P11M2).
	assert(HP3P6P9P10P11P12P13mtmp : rk(P3 :: P6 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP3P6P9P10P11P12P13eq HP3P6P9P10P11P12P13m3).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P6 :: P10 :: P11 :: nil) (P3 :: P9 :: P10 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P6 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) (P6 :: P10 :: P11 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P10 :: P11 :: P3 :: P9 :: P10 :: P12 :: P13 :: nil) ((P6 :: P10 :: P11 :: nil) ++ (P3 :: P9 :: P10 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP3P6P9P10P11P12P13mtmp;try rewrite HT2 in HP3P6P9P10P11P12P13mtmp.
	assert(HT := rule_4 (P6 :: P10 :: P11 :: nil) (P3 :: P9 :: P10 :: P12 :: P13 :: nil) (P10 :: nil) 3 1 2 HP3P6P9P10P11P12P13mtmp HP10mtmp HP6P10P11Mtmp Hincl); apply HT.
}
try clear HP3P9P10P12P13m1. try clear HP3P6P9P10P11P12P13M4. try clear HP3P6P9P10P11P12P13m3. 

assert(HP3P9P10P12P13M3 : rk(P3 :: P9 :: P10 :: P12 :: P13 :: nil) <= 3).
{
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(HP9P10P13Mtmp : rk(P9 :: P10 :: P13 :: nil) <= 2) by (solve_hyps_max HP9P10P13eq HP9P10P13M2).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P3 :: P10 :: P12 :: nil) (P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P9 :: P10 :: P12 :: P13 :: nil) (P3 :: P10 :: P12 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P10 :: P12 :: P9 :: P10 :: P13 :: nil) ((P3 :: P10 :: P12 :: nil) ++ (P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P10 :: P12 :: nil) (P9 :: P10 :: P13 :: nil) (P10 :: nil) 2 2 1 HP3P10P12Mtmp HP9P10P13Mtmp HP10mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P9P10P12P13M4. 

assert(HP3P9P12P13m2 : rk(P3 :: P9 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP3P12mtmp : rk(P3 :: P12 :: nil) >= 2) by (solve_hyps_min HP3P12eq HP3P12m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P12 :: nil) (P3 :: P9 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P12 :: nil) (P3 :: P9 :: P12 :: P13 :: nil) 2 2 HP3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP3P12M2. try clear HP3P12m2. try clear HP3P9P12P13m1. 

assert(HP3P9P12P13M3 : rk(P3 :: P9 :: P12 :: P13 :: nil) <= 3).
{
	assert(HP3P9P10P12P13Mtmp : rk(P3 :: P9 :: P10 :: P12 :: P13 :: nil) <= 3) by (solve_hyps_max HP3P9P10P12P13eq HP3P9P10P12P13M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P3 :: P9 :: P12 :: P13 :: nil) (P3 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P3 :: P9 :: P12 :: P13 :: nil) (P3 :: P9 :: P10 :: P12 :: P13 :: nil) 3 3 HP3P9P10P12P13Mtmp Hcomp Hincl);apply HT.
}
try clear HP3P9P12P13M4. try clear HP3P9P10P12P13M3. try clear HP3P9P10P12P13m2. 

assert(HP2P3P9P12P13m2 : rk(P2 :: P3 :: P9 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: P12 :: P13 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P9P12P13m1. 

assert(HP2P3P9P12P13m3 : rk(P2 :: P3 :: P9 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP2P3P12mtmp : rk(P2 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP2P3P12eq HP2P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P9 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P9 :: P12 :: P13 :: nil) 3 3 HP2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P9P12P13m2. 

assert(HP2P3P9P12P13M3 : rk(P2 :: P3 :: P9 :: P12 :: P13 :: nil) <= 3).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP3P9P12P13Mtmp : rk(P3 :: P9 :: P12 :: P13 :: nil) <= 3) by (solve_hyps_max HP3P9P12P13eq HP3P9P12P13M3).
	assert(HP9P12mtmp : rk(P9 :: P12 :: nil) >= 2) by (solve_hyps_min HP9P12eq HP9P12m2).
	assert(Hincl : incl (P9 :: P12 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P3 :: P9 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P9 :: P12 :: P13 :: nil) (P2 :: P9 :: P12 :: P3 :: P9 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P3 :: P9 :: P12 :: P13 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P3 :: P9 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P9 :: P12 :: nil) (P3 :: P9 :: P12 :: P13 :: nil) (P9 :: P12 :: nil) 2 3 2 HP2P9P12Mtmp HP3P9P12P13Mtmp HP9P12mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P9P12P13M3. try clear HP3P9P12P13m2. try clear HP2P3P9P12P13M4. 

assert(HP2P3P9P12M3 : rk(P2 :: P3 :: P9 :: P12 :: nil) <= 3).
{
	assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M1).
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: nil) (P2 :: P9 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P9 :: P12 :: nil) (P3 :: P2 :: P9 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P2 :: P9 :: P12 :: nil) ((P3 :: nil) ++ (P2 :: P9 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: nil) (P2 :: P9 :: P12 :: nil) (nil) 1 2 0 HP3Mtmp HP2P9P12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3M1. try clear HP3m1. try clear HP2P3P9P12M4. 

assert(HP2P3P9P12m2 : rk(P2 :: P3 :: P9 :: P12 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: P12 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P9P12m1. 

assert(HP2P3P9P12m3 : rk(P2 :: P3 :: P9 :: P12 :: nil) >= 3).
{
	assert(HP2P3P12mtmp : rk(P2 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP2P3P12eq HP2P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P9 :: P12 :: nil) 3 3 HP2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P9P12m2. 

assert(HP2P3P9m2 : rk(P2 :: P3 :: P9 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P9m1. 

assert(HP2P3P9m3 : rk(P2 :: P3 :: P9 :: nil) >= 3).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP2P3P9P12mtmp : rk(P2 :: P3 :: P9 :: P12 :: nil) >= 3) by (solve_hyps_min HP2P3P9P12eq HP2P3P9P12m3).
	assert(HP2P9mtmp : rk(P2 :: P9 :: nil) >= 2) by (solve_hyps_min HP2P9eq HP2P9m2).
	assert(Hincl : incl (P2 :: P9 :: nil) (list_inter (P2 :: P3 :: P9 :: nil) (P2 :: P9 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P9 :: P12 :: nil) (P2 :: P3 :: P9 :: P2 :: P9 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P9 :: P2 :: P9 :: P12 :: nil) ((P2 :: P3 :: P9 :: nil) ++ (P2 :: P9 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P9P12mtmp;try rewrite HT2 in HP2P3P9P12mtmp.
	assert(HT := rule_2 (P2 :: P3 :: P9 :: nil) (P2 :: P9 :: P12 :: nil) (P2 :: P9 :: nil) 3 2 2 HP2P3P9P12mtmp HP2P9mtmp HP2P9P12Mtmp Hincl);apply HT.
}
try clear HP2P3P9m2. try clear HP2P3P9P12M3. try clear HP2P3P9P12m3. 

assert(HP2P3P9P13m2 : rk(P2 :: P3 :: P9 :: P13 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: P13 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P9P13m1. 

assert(HP2P3P9P13m3 : rk(P2 :: P3 :: P9 :: P13 :: nil) >= 3).
{
	assert(HP2P3P9mtmp : rk(P2 :: P3 :: P9 :: nil) >= 3) by (solve_hyps_min HP2P3P9eq HP2P3P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P9 :: nil) (P2 :: P3 :: P9 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P9 :: nil) (P2 :: P3 :: P9 :: P13 :: nil) 3 3 HP2P3P9mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P9M3. try clear HP2P3P9m3. try clear HP2P3P9P13m2. 

assert(HP2P3P9P13M3 : rk(P2 :: P3 :: P9 :: P13 :: nil) <= 3).
{
	assert(HP2P3P9P12P13Mtmp : rk(P2 :: P3 :: P9 :: P12 :: P13 :: nil) <= 3) by (solve_hyps_max HP2P3P9P12P13eq HP2P3P9P12P13M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P9 :: P13 :: nil) (P2 :: P3 :: P9 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P2 :: P3 :: P9 :: P13 :: nil) (P2 :: P3 :: P9 :: P12 :: P13 :: nil) 3 3 HP2P3P9P12P13Mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P9P13M4. try clear HP2P3P9P12P13M3. try clear HP2P3P9P12P13m3. 

assert(HP4P5P6P8P9P10P11P13P14m2 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P10P11P13P14m1. 

assert(HP4P5P6P8P9P10P11P13P14m3 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P10P11P13P14m2. 

assert(HP4P5P6P8P9P10P11P13P14m4 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP4P5P6P11mtmp : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 4) by (solve_hyps_min HP4P5P6P11eq HP4P5P6P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil) 4 4 HP4P5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P10P11P13P14m3. 

assert(HP5P6P8P9P10P13P14m2 : rk(P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P8P9P10P13P14m1. 

assert(HP5P6P8P9P10P13P14m3 : rk(P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP4P5P6P8P9P10P11P13P14mtmp : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP4P5P6P8P9P10P11P13P14eq HP4P5P6P8P9P10P11P13P14m4).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: P14 :: nil) (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8P9P10P11P13P14mtmp;try rewrite HT2 in HP4P5P6P8P9P10P11P13P14mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil) (P8 :: nil) 4 1 2 HP4P5P6P8P9P10P11P13P14mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP5P6P8P9P10P13P14m2. try clear HP4P5P6P8P9P10P11P13P14M4. try clear HP4P5P6P8P9P10P11P13P14m4. 

assert(HP8P9P10P13P14m2 : rk(P8 :: P9 :: P10 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6P8P9P10P13P14mtmp : rk(P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil) >= 3) by (solve_hyps_min HP5P6P8P9P10P13P14eq HP5P6P8P9P10P13P14m3).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P10 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil) (P5 :: P6 :: P13 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P13 :: P8 :: P9 :: P10 :: P13 :: P14 :: nil) ((P5 :: P6 :: P13 :: nil) ++ (P8 :: P9 :: P10 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P6P8P9P10P13P14mtmp;try rewrite HT2 in HP5P6P8P9P10P13P14mtmp.
	assert(HT := rule_4 (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P10 :: P13 :: P14 :: nil) (P13 :: nil) 3 1 2 HP5P6P8P9P10P13P14mtmp HP13mtmp HP5P6P13Mtmp Hincl); apply HT.
}
try clear HP8P9P10P13P14m1. try clear HP5P6P8P9P10P13P14M4. try clear HP5P6P8P9P10P13P14m3. 

assert(HP8P9P10P13P14M3 : rk(P8 :: P9 :: P10 :: P13 :: P14 :: nil) <= 3).
{
	assert(HP9P10P13Mtmp : rk(P9 :: P10 :: P13 :: nil) <= 2) by (solve_hyps_max HP9P10P13eq HP9P10P13M2).
	assert(HP8P10P14Mtmp : rk(P8 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP8P10P14eq HP8P10P14M2).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P9 :: P10 :: P13 :: nil) (P8 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P8 :: P9 :: P10 :: P13 :: P14 :: nil) (P9 :: P10 :: P13 :: P8 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P9 :: P10 :: P13 :: P8 :: P10 :: P14 :: nil) ((P9 :: P10 :: P13 :: nil) ++ (P8 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P9 :: P10 :: P13 :: nil) (P8 :: P10 :: P14 :: nil) (P10 :: nil) 2 2 1 HP9P10P13Mtmp HP8P10P14Mtmp HP10mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP8P10P14M2. try clear HP8P10P14m2. try clear HP8P9P10P13P14M4. 

assert(HP4P5P6P8P9P11P13P14m2 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P11P13P14m1. 

assert(HP4P5P6P8P9P11P13P14m3 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P11P13P14m2. 

assert(HP4P5P6P8P9P11P13P14m4 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP4P5P6P11mtmp : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 4) by (solve_hyps_min HP4P5P6P11eq HP4P5P6P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil) 4 4 HP4P5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P11P13P14m3. 

assert(HP5P6P8P9P13P14m2 : rk(P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P8P9P13P14m1. 

assert(HP5P6P8P9P13P14m3 : rk(P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP4P5P6P8P9P11P13P14mtmp : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP4P5P6P8P9P11P13P14eq HP4P5P6P8P9P11P13P14m4).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: nil) (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8P9P11P13P14mtmp;try rewrite HT2 in HP4P5P6P8P9P11P13P14mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil) (P8 :: nil) 4 1 2 HP4P5P6P8P9P11P13P14mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP5P6P8P9P13P14m2. try clear HP4P5P6P8P9P11P13P14M4. try clear HP4P5P6P8P9P11P13P14m4. 

assert(HP8P9P13P14m2 : rk(P8 :: P9 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6P8P9P13P14mtmp : rk(P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil) >= 3) by (solve_hyps_min HP5P6P8P9P13P14eq HP5P6P8P9P13P14m3).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: nil) (P5 :: P6 :: P13 :: P8 :: P9 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P13 :: P8 :: P9 :: P13 :: P14 :: nil) ((P5 :: P6 :: P13 :: nil) ++ (P8 :: P9 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P6P8P9P13P14mtmp;try rewrite HT2 in HP5P6P8P9P13P14mtmp.
	assert(HT := rule_4 (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P13 :: P14 :: nil) (P13 :: nil) 3 1 2 HP5P6P8P9P13P14mtmp HP13mtmp HP5P6P13Mtmp Hincl); apply HT.
}
try clear HP8P9P13P14m1. try clear HP5P6P8P9P13P14M4. try clear HP5P6P8P9P13P14m3. 

assert(HP8P9P13P14M3 : rk(P8 :: P9 :: P13 :: P14 :: nil) <= 3).
{
	assert(HP8P9P10P13P14Mtmp : rk(P8 :: P9 :: P10 :: P13 :: P14 :: nil) <= 3) by (solve_hyps_max HP8P9P10P13P14eq HP8P9P10P13P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P8 :: P9 :: P13 :: P14 :: nil) (P8 :: P9 :: P10 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P8 :: P9 :: P13 :: P14 :: nil) (P8 :: P9 :: P10 :: P13 :: P14 :: nil) 3 3 HP8P9P10P13P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP8P9P13P14M4. try clear HP8P9P10P13P14M3. try clear HP8P9P10P13P14m2. 

assert(HP8P9P13P14m3 : rk(P8 :: P9 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP2P3P9P13Mtmp : rk(P2 :: P3 :: P9 :: P13 :: nil) <= 3) by (solve_hyps_max HP2P3P9P13eq HP2P3P9P13M3).
	assert(HP2P3P8P9P13P14mtmp : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP2P3P8P9P13P14eq HP2P3P8P9P13P14m4).
	assert(HP9P13mtmp : rk(P9 :: P13 :: nil) >= 2) by (solve_hyps_min HP9P13eq HP9P13m2).
	assert(Hincl : incl (P9 :: P13 :: nil) (list_inter (P2 :: P3 :: P9 :: P13 :: nil) (P8 :: P9 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: nil) (P2 :: P3 :: P9 :: P13 :: P8 :: P9 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P9 :: P13 :: P8 :: P9 :: P13 :: P14 :: nil) ((P2 :: P3 :: P9 :: P13 :: nil) ++ (P8 :: P9 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P8P9P13P14mtmp;try rewrite HT2 in HP2P3P8P9P13P14mtmp.
	assert(HT := rule_4 (P2 :: P3 :: P9 :: P13 :: nil) (P8 :: P9 :: P13 :: P14 :: nil) (P9 :: P13 :: nil) 4 2 3 HP2P3P8P9P13P14mtmp HP9P13mtmp HP2P3P9P13Mtmp Hincl); apply HT.
}
try clear HP8P9P13P14m2. try clear HP2P3P8P9P13P14M4. try clear HP2P3P8P9P13P14m4. 

assert(HP1P2P3P8P9P12P13P15m2 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P12P13P15m1. 

assert(HP1P2P3P8P9P12P13P15m3 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P12P13P15m2. 

assert(HP1P2P3P8P9P12P13P15m4 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P12P13P15m3. 

assert(HP2P3P8P9P12P13P15m2 : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8P9P12P13P15m1. 

assert(HP2P3P8P9P12P13P15m3 : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) >= 3).
{
	assert(HP2P3P12mtmp : rk(P2 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP2P3P12eq HP2P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) 3 3 HP2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8P9P12P13P15m2. 

assert(HP2P3P8P9P12P13P15m4 : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) >= 4).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P2P3P8P9P12P13P15mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P9P12P13P15eq HP1P2P3P8P9P12P13P15m4).
	assert(HP8P12mtmp : rk(P8 :: P12 :: nil) >= 2) by (solve_hyps_min HP8P12eq HP8P12m2).
	assert(Hincl : incl (P8 :: P12 :: nil) (list_inter (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P9P12P13P15mtmp;try rewrite HT2 in HP1P2P3P8P9P12P13P15mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) (P8 :: P12 :: nil) 4 2 2 HP1P2P3P8P9P12P13P15mtmp HP8P12mtmp HP1P8P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P12P13P15m3. 

assert(HP2P3P8P9P13P15m2 : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8P9P13P15m1. 

assert(HP2P3P8P9P13P15m3 : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) >= 3).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P2P3P8P9P12P13P15mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P9P12P13P15eq HP1P2P3P8P9P12P13P15m4).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P9P12P13P15mtmp;try rewrite HT2 in HP1P2P3P8P9P12P13P15mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) (P8 :: nil) 4 1 2 HP1P2P3P8P9P12P13P15mtmp HP8mtmp HP1P8P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P13P15m2. try clear HP1P2P3P8P9P12P13P15M4. try clear HP1P2P3P8P9P12P13P15m4. 

assert(HP2P3P8P9P13P15m4 : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) >= 4).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP2P3P8P9P12P13P15mtmp : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) >= 4) by (solve_hyps_min HP2P3P8P9P12P13P15eq HP2P3P8P9P12P13P15m4).
	assert(HP2P9mtmp : rk(P2 :: P9 :: nil) >= 2) by (solve_hyps_min HP2P9eq HP2P9m2).
	assert(Hincl : incl (P2 :: P9 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P15 :: nil) (P2 :: P9 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P8P9P12P13P15mtmp;try rewrite HT2 in HP2P3P8P9P12P13P15mtmp.
	assert(HT := rule_4 (P2 :: P9 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) (P2 :: P9 :: nil) 4 2 2 HP2P3P8P9P12P13P15mtmp HP2P9mtmp HP2P9P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P13P15m3. try clear HP2P3P8P9P12P13P15M4. try clear HP2P3P8P9P12P13P15m4. 

assert(HP4P5P6P8P9P11P13P15m2 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P11P13P15m1. 

assert(HP4P5P6P8P9P11P13P15m3 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P11P13P15m2. 

assert(HP4P5P6P8P9P11P13P15m4 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil) >= 4).
{
	assert(HP4P5P6P11mtmp : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 4) by (solve_hyps_min HP4P5P6P11eq HP4P5P6P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil) 4 4 HP4P5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P11P13P15m3. 

assert(HP5P6P8P9P13P15m2 : rk(P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P8P9P13P15m1. 

assert(HP5P6P8P9P13P15m3 : rk(P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil) >= 3).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP4P5P6P8P9P11P13P15mtmp : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil) >= 4) by (solve_hyps_min HP4P5P6P8P9P11P13P15eq HP4P5P6P8P9P11P13P15m4).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P15 :: nil) (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8P9P11P13P15mtmp;try rewrite HT2 in HP4P5P6P8P9P11P13P15mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil) (P8 :: nil) 4 1 2 HP4P5P6P8P9P11P13P15mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP5P6P8P9P13P15m2. try clear HP4P5P6P8P9P11P13P15M4. try clear HP4P5P6P8P9P11P13P15m4. 

assert(HP8P9P13P15M3 : rk(P8 :: P9 :: P13 :: P15 :: nil) <= 3).
{
	assert(HP13Mtmp : rk(P13 :: nil) <= 1) by (solve_hyps_max HP13eq HP13M1).
	assert(HP8P9P15Mtmp : rk(P8 :: P9 :: P15 :: nil) <= 2) by (solve_hyps_max HP8P9P15eq HP8P9P15M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P13 :: nil) (P8 :: P9 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P8 :: P9 :: P13 :: P15 :: nil) (P13 :: P8 :: P9 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P13 :: P8 :: P9 :: P15 :: nil) ((P13 :: nil) ++ (P8 :: P9 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P13 :: nil) (P8 :: P9 :: P15 :: nil) (nil) 1 2 0 HP13Mtmp HP8P9P15Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP8P9P15M2. try clear HP8P9P15m2. try clear HP8P9P13P15M4. 

assert(HP8P9P13P15m2 : rk(P8 :: P9 :: P13 :: P15 :: nil) >= 2).
{
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6P8P9P13P15mtmp : rk(P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil) >= 3) by (solve_hyps_min HP5P6P8P9P13P15eq HP5P6P8P9P13P15m3).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P13 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P8 :: P9 :: P13 :: P15 :: nil) (P5 :: P6 :: P13 :: P8 :: P9 :: P13 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P13 :: P8 :: P9 :: P13 :: P15 :: nil) ((P5 :: P6 :: P13 :: nil) ++ (P8 :: P9 :: P13 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P6P8P9P13P15mtmp;try rewrite HT2 in HP5P6P8P9P13P15mtmp.
	assert(HT := rule_4 (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P13 :: P15 :: nil) (P13 :: nil) 3 1 2 HP5P6P8P9P13P15mtmp HP13mtmp HP5P6P13Mtmp Hincl); apply HT.
}
try clear HP8P9P13P15m1. try clear HP5P6P8P9P13P15M4. try clear HP5P6P8P9P13P15m3. 

assert(HP8P9P13P15m3 : rk(P8 :: P9 :: P13 :: P15 :: nil) >= 3).
{
	assert(HP2P3P9P13Mtmp : rk(P2 :: P3 :: P9 :: P13 :: nil) <= 3) by (solve_hyps_max HP2P3P9P13eq HP2P3P9P13M3).
	assert(HP2P3P8P9P13P15mtmp : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) >= 4) by (solve_hyps_min HP2P3P8P9P13P15eq HP2P3P8P9P13P15m4).
	assert(HP9P13mtmp : rk(P9 :: P13 :: nil) >= 2) by (solve_hyps_min HP9P13eq HP9P13m2).
	assert(Hincl : incl (P9 :: P13 :: nil) (list_inter (P2 :: P3 :: P9 :: P13 :: nil) (P8 :: P9 :: P13 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P8 :: P9 :: P13 :: P15 :: nil) (P2 :: P3 :: P9 :: P13 :: P8 :: P9 :: P13 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P9 :: P13 :: P8 :: P9 :: P13 :: P15 :: nil) ((P2 :: P3 :: P9 :: P13 :: nil) ++ (P8 :: P9 :: P13 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P8P9P13P15mtmp;try rewrite HT2 in HP2P3P8P9P13P15mtmp.
	assert(HT := rule_4 (P2 :: P3 :: P9 :: P13 :: nil) (P8 :: P9 :: P13 :: P15 :: nil) (P9 :: P13 :: nil) 4 2 3 HP2P3P8P9P13P15mtmp HP9P13mtmp HP2P3P9P13Mtmp Hincl); apply HT.
}
try clear HP8P9P13P15m2. try clear HP2P3P8P9P13P15M4. try clear HP2P3P8P9P13P15m4. 

assert(HP1P2P3P8P9P10P12P13m2 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P10P12P13m1. 

assert(HP1P2P3P8P9P10P12P13m3 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P10P12P13m2. 

assert(HP1P2P3P8P9P10P12P13m4 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P10P12P13m3. 

assert(HP2P3P8P9P10P12P13m2 : rk(P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8P9P10P12P13m1. 

assert(HP2P3P8P9P10P12P13m3 : rk(P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP2P3P12mtmp : rk(P2 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP2P3P12eq HP2P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) 3 3 HP2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8P9P10P12P13m2. 

assert(HP2P3P8P9P10P12P13m4 : rk(P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P2P3P8P9P10P12P13mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P9P10P12P13eq HP1P2P3P8P9P10P12P13m4).
	assert(HP8P12mtmp : rk(P8 :: P12 :: nil) >= 2) by (solve_hyps_min HP8P12eq HP8P12m2).
	assert(Hincl : incl (P8 :: P12 :: nil) (list_inter (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P9P10P12P13mtmp;try rewrite HT2 in HP1P2P3P8P9P10P12P13mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P8 :: P12 :: nil) 4 2 2 HP1P2P3P8P9P10P12P13mtmp HP8P12mtmp HP1P8P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P10P12P13m3. try clear HP1P2P3P8P9P10P12P13M4. try clear HP1P2P3P8P9P10P12P13m4. 

assert(HP1P3P8P9P10P12P13m2 : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P9P10P12P13m1. 

assert(HP1P3P8P9P10P12P13m3 : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P3P12mtmp : rk(P1 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P12eq HP1P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) 3 3 HP1P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P8P9P10P12P13m2. 

assert(HP3P6P8P9P10P11P12P13m2 : rk(P3 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: nil) (P3 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: nil) (P3 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) 2 2 HP3P6mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6M2. try clear HP3P6m2. try clear HP3P6P8P9P10P11P12P13m1. 

assert(HP3P6P8P9P10P11P12P13m3 : rk(P3 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP3P6P11mtmp : rk(P3 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP3P6P11eq HP3P6P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P6 :: P11 :: nil) (P3 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) 3 3 HP3P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP3P6P11M3. try clear HP3P6P11m3. try clear HP3P6P8P9P10P11P12P13m2. 

assert(HP3P8P9P10P12P13m2 : rk(P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP6P10P11Mtmp : rk(P6 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP6P10P11eq HP6P10P11M2).
	assert(HP3P6P8P9P10P11P12P13mtmp : rk(P3 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP3P6P8P9P10P11P12P13eq HP3P6P8P9P10P11P12P13m3).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P6 :: P10 :: P11 :: nil) (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: nil) (P6 :: P10 :: P11 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P10 :: P11 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) ((P6 :: P10 :: P11 :: nil) ++ (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP3P6P8P9P10P11P12P13mtmp;try rewrite HT2 in HP3P6P8P9P10P11P12P13mtmp.
	assert(HT := rule_4 (P6 :: P10 :: P11 :: nil) (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P10 :: nil) 3 1 2 HP3P6P8P9P10P11P12P13mtmp HP10mtmp HP6P10P11Mtmp Hincl); apply HT.
}
try clear HP6P10P11M2. try clear HP6P10P11m2. try clear HP3P8P9P10P12P13m1. try clear HP3P6P8P9P10P11P12P13M4. try clear HP3P6P8P9P10P11P12P13m3. 

assert(HP3P8P9P10P12P13m3 : rk(P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P3P8P9P10P12P13mtmp : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P3P8P9P10P12P13eq HP1P3P8P9P10P12P13m3).
	assert(HP8P12mtmp : rk(P8 :: P12 :: nil) >= 2) by (solve_hyps_min HP8P12eq HP8P12m2).
	assert(Hincl : incl (P8 :: P12 :: nil) (list_inter (P1 :: P8 :: P12 :: nil) (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P1 :: P8 :: P12 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P8P9P10P12P13mtmp;try rewrite HT2 in HP1P3P8P9P10P12P13mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: nil) (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P8 :: P12 :: nil) 3 2 2 HP1P3P8P9P10P12P13mtmp HP8P12mtmp HP1P8P12Mtmp Hincl); apply HT.
}
try clear HP3P8P9P10P12P13m2. try clear HP1P3P8P9P10P12P13M4. try clear HP1P3P8P9P10P12P13m3. 

assert(HP3P8P9P10P12P13m4 : rk(P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP2P3P8P9P10P12P13mtmp : rk(P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP2P3P8P9P10P12P13eq HP2P3P8P9P10P12P13m4).
	assert(HP9P12mtmp : rk(P9 :: P12 :: nil) >= 2) by (solve_hyps_min HP9P12eq HP9P12m2).
	assert(Hincl : incl (P9 :: P12 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P2 :: P9 :: P12 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P8P9P10P12P13mtmp;try rewrite HT2 in HP2P3P8P9P10P12P13mtmp.
	assert(HT := rule_4 (P2 :: P9 :: P12 :: nil) (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P9 :: P12 :: nil) 4 2 2 HP2P3P8P9P10P12P13mtmp HP9P12mtmp HP2P9P12Mtmp Hincl); apply HT.
}
try clear HP3P8P9P10P12P13m3. try clear HP2P3P8P9P10P12P13M4. try clear HP2P3P8P9P10P12P13m4. 

assert(HP4P5P6P8P9P10P11P13m2 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P10P11P13m1. 

assert(HP4P5P6P8P9P10P11P13m3 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P10P11P13m2. 

assert(HP4P5P6P8P9P10P11P13m4 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil) >= 4).
{
	assert(HP4P5P6P11mtmp : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 4) by (solve_hyps_min HP4P5P6P11eq HP4P5P6P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil) 4 4 HP4P5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P10P11P13m3. 

assert(HP5P6P8P9P10P13m2 : rk(P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P8P9P10P13m1. 

assert(HP5P6P8P9P10P13m3 : rk(P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil) >= 3).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP4P5P6P8P9P10P11P13mtmp : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP4P5P6P8P9P10P11P13eq HP4P5P6P8P9P10P11P13m4).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P13 :: nil) (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8P9P10P11P13mtmp;try rewrite HT2 in HP4P5P6P8P9P10P11P13mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil) (P8 :: nil) 4 1 2 HP4P5P6P8P9P10P11P13mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP5P6P8P9P10P13m2. try clear HP4P5P6P8P9P10P11P13M4. try clear HP4P5P6P8P9P10P11P13m4. 

assert(HP8P9P10P13M3 : rk(P8 :: P9 :: P10 :: P13 :: nil) <= 3).
{
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(HP9P10P13Mtmp : rk(P9 :: P10 :: P13 :: nil) <= 2) by (solve_hyps_max HP9P10P13eq HP9P10P13M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P8 :: nil) (P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P8 :: P9 :: P10 :: P13 :: nil) (P8 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P9 :: P10 :: P13 :: nil) ((P8 :: nil) ++ (P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P8 :: nil) (P9 :: P10 :: P13 :: nil) (nil) 1 2 0 HP8Mtmp HP9P10P13Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP8P9P10P13M4. 

assert(HP8P9P10P13m2 : rk(P8 :: P9 :: P10 :: P13 :: nil) >= 2).
{
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6P8P9P10P13mtmp : rk(P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil) >= 3) by (solve_hyps_min HP5P6P8P9P10P13eq HP5P6P8P9P10P13m3).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P8 :: P9 :: P10 :: P13 :: nil) (P5 :: P6 :: P13 :: P8 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P13 :: P8 :: P9 :: P10 :: P13 :: nil) ((P5 :: P6 :: P13 :: nil) ++ (P8 :: P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P6P8P9P10P13mtmp;try rewrite HT2 in HP5P6P8P9P10P13mtmp.
	assert(HT := rule_4 (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P10 :: P13 :: nil) (P13 :: nil) 3 1 2 HP5P6P8P9P10P13mtmp HP13mtmp HP5P6P13Mtmp Hincl); apply HT.
}
try clear HP8P9P10P13m1. try clear HP5P6P8P9P10P13M4. try clear HP5P6P8P9P10P13m3. 

assert(HP8P9P10P13m3 : rk(P8 :: P9 :: P10 :: P13 :: nil) >= 3).
{
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(HP3P8P9P10P12P13mtmp : rk(P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP3P8P9P10P12P13eq HP3P8P9P10P12P13m4).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P3 :: P10 :: P12 :: nil) (P8 :: P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P3 :: P10 :: P12 :: P8 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P10 :: P12 :: P8 :: P9 :: P10 :: P13 :: nil) ((P3 :: P10 :: P12 :: nil) ++ (P8 :: P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP3P8P9P10P12P13mtmp;try rewrite HT2 in HP3P8P9P10P12P13mtmp.
	assert(HT := rule_4 (P3 :: P10 :: P12 :: nil) (P8 :: P9 :: P10 :: P13 :: nil) (P10 :: nil) 4 1 2 HP3P8P9P10P12P13mtmp HP10mtmp HP3P10P12Mtmp Hincl); apply HT.
}
try clear HP8P9P10P13m2. try clear HP3P8P9P10P12P13M4. try clear HP3P8P9P10P12P13m4. 

assert(HP4P5P6P8P9P11P13m2 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P11P13m1. 

assert(HP4P5P6P8P9P11P13m3 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P11P13m2. 

assert(HP4P5P6P8P9P11P13m4 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil) >= 4).
{
	assert(HP4P5P6P11mtmp : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 4) by (solve_hyps_min HP4P5P6P11eq HP4P5P6P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil) 4 4 HP4P5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P8P9P11P13m3. 

assert(HP5P6P8P9P13m2 : rk(P5 :: P6 :: P8 :: P9 :: P13 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P8P9P13m1. 

assert(HP5P6P8P9P13m3 : rk(P5 :: P6 :: P8 :: P9 :: P13 :: nil) >= 3).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP4P5P6P8P9P11P13mtmp : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil) >= 4) by (solve_hyps_min HP4P5P6P8P9P11P13eq HP4P5P6P8P9P11P13m4).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: nil) (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P13 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P5 :: P6 :: P8 :: P9 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8P9P11P13mtmp;try rewrite HT2 in HP4P5P6P8P9P11P13mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: nil) (P8 :: nil) 4 1 2 HP4P5P6P8P9P11P13mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP5P6P8P9P13m2. try clear HP4P5P6P8P9P11P13M4. try clear HP4P5P6P8P9P11P13m4. 

assert(HP8P9P13m2 : rk(P8 :: P9 :: P13 :: nil) >= 2).
{
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6P8P9P13mtmp : rk(P5 :: P6 :: P8 :: P9 :: P13 :: nil) >= 3) by (solve_hyps_min HP5P6P8P9P13eq HP5P6P8P9P13m3).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P8 :: P9 :: P13 :: nil) (P5 :: P6 :: P13 :: P8 :: P9 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P13 :: P8 :: P9 :: P13 :: nil) ((P5 :: P6 :: P13 :: nil) ++ (P8 :: P9 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P6P8P9P13mtmp;try rewrite HT2 in HP5P6P8P9P13mtmp.
	assert(HT := rule_4 (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P13 :: nil) (P13 :: nil) 3 1 2 HP5P6P8P9P13mtmp HP13mtmp HP5P6P13Mtmp Hincl); apply HT.
}
try clear HP8P9P13m1. try clear HP5P6P8P9P13M4. try clear HP5P6P8P9P13m3. 

assert(HP8P9P13m3 : rk(P8 :: P9 :: P13 :: nil) >= 3).
{
	assert(HP9P10P13Mtmp : rk(P9 :: P10 :: P13 :: nil) <= 2) by (solve_hyps_max HP9P10P13eq HP9P10P13M2).
	assert(HP8P9P10P13mtmp : rk(P8 :: P9 :: P10 :: P13 :: nil) >= 3) by (solve_hyps_min HP8P9P10P13eq HP8P9P10P13m3).
	assert(HP9P13mtmp : rk(P9 :: P13 :: nil) >= 2) by (solve_hyps_min HP9P13eq HP9P13m2).
	assert(Hincl : incl (P9 :: P13 :: nil) (list_inter (P8 :: P9 :: P13 :: nil) (P9 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P8 :: P9 :: P10 :: P13 :: nil) (P8 :: P9 :: P13 :: P9 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P9 :: P13 :: P9 :: P10 :: P13 :: nil) ((P8 :: P9 :: P13 :: nil) ++ (P9 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP8P9P10P13mtmp;try rewrite HT2 in HP8P9P10P13mtmp.
	assert(HT := rule_2 (P8 :: P9 :: P13 :: nil) (P9 :: P10 :: P13 :: nil) (P9 :: P13 :: nil) 3 2 2 HP8P9P10P13mtmp HP9P13mtmp HP9P10P13Mtmp Hincl);apply HT.
}
try clear HP8P9P13m2. try clear HP8P9P10P13M3. try clear HP8P9P10P13m3. 

assert(HP1P2P3P8P9P12P13P14P15m2 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P12P13P14P15m1. 

assert(HP1P2P3P8P9P12P13P14P15m3 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P12P13P14P15m2. 

assert(HP1P2P3P8P9P12P13P14P15m4 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P12P13P14P15m3. 

assert(HP2P3P8P9P12P13P14P15m2 : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8P9P12P13P14P15m1. 

assert(HP2P3P8P9P12P13P14P15m3 : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP2P3P12mtmp : rk(P2 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP2P3P12eq HP2P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) 3 3 HP2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P12M3. try clear HP2P3P12m3. try clear HP2P3P8P9P12P13P14P15m2. 

assert(HP2P3P8P9P12P13P14P15m4 : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P2P3P8P9P12P13P14P15mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P9P12P13P14P15eq HP1P2P3P8P9P12P13P14P15m4).
	assert(HP8P12mtmp : rk(P8 :: P12 :: nil) >= 2) by (solve_hyps_min HP8P12eq HP8P12m2).
	assert(Hincl : incl (P8 :: P12 :: nil) (list_inter (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P9P12P13P14P15mtmp;try rewrite HT2 in HP1P2P3P8P9P12P13P14P15mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) (P8 :: P12 :: nil) 4 2 2 HP1P2P3P8P9P12P13P14P15mtmp HP8P12mtmp HP1P8P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P12P13P14P15m3. try clear HP8P12M2. try clear HP8P12m2. 

assert(HP2P3P8P9P13P14P15m2 : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3M2. try clear HP2P3m2. try clear HP2P3P8P9P13P14P15m1. 

assert(HP2P3P8P9P13P14P15m3 : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(HP1P2P3P8P9P12P13P14P15mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P9P12P13P14P15eq HP1P2P3P8P9P12P13P14P15m4).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) ((P1 :: P8 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P9P12P13P14P15mtmp;try rewrite HT2 in HP1P2P3P8P9P12P13P14P15mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P8 :: nil) 4 1 2 HP1P2P3P8P9P12P13P14P15mtmp HP8mtmp HP1P8P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P13P14P15m2. try clear HP1P2P3P8P9P12P13P14P15M4. try clear HP1P2P3P8P9P12P13P14P15m4. 

assert(HP2P3P8P9P13P14P15m4 : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP2P3P8P9P12P13P14P15mtmp : rk(P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP2P3P8P9P12P13P14P15eq HP2P3P8P9P12P13P14P15m4).
	assert(HP2P9mtmp : rk(P2 :: P9 :: nil) >= 2) by (solve_hyps_min HP2P9eq HP2P9m2).
	assert(Hincl : incl (P2 :: P9 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) (P2 :: P9 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P8P9P12P13P14P15mtmp;try rewrite HT2 in HP2P3P8P9P12P13P14P15mtmp.
	assert(HT := rule_4 (P2 :: P9 :: P12 :: nil) (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P2 :: P9 :: nil) 4 2 2 HP2P3P8P9P12P13P14P15mtmp HP2P9mtmp HP2P9P12Mtmp Hincl); apply HT.
}
try clear HP2P3P8P9P13P14P15m3. try clear HP2P9M2. try clear HP2P9m2. try clear HP2P3P8P9P12P13P14P15M4. try clear HP2P3P8P9P12P13P14P15m4. 

assert(HP4P5P6P8P9P11P13P14P15m2 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5M2. try clear HP4P5m2. try clear HP4P5P6P8P9P11P13P14P15m1. 

assert(HP4P5P6P8P9P11P13P14P15m3 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6M3. try clear HP4P5P6m3. try clear HP4P5P6P8P9P11P13P14P15m2. 

assert(HP4P5P6P8P9P11P13P14P15m4 : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP4P5P6P11mtmp : rk(P4 :: P5 :: P6 :: P11 :: nil) >= 4) by (solve_hyps_min HP4P5P6P11eq HP4P5P6P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: P11 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) 4 4 HP4P5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P11M4. try clear HP4P5P6P11m4. try clear HP4P5P6P8P9P11P13P14P15m3.

assert(HP5P6P8P9P13P14P15m2 : rk(P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P8P9P13P14P15m1. 

assert(HP5P6P8P9P13P14P15m3 : rk(P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP4P5P6P8P9P11P13P14P15mtmp : rk(P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP4P5P6P8P9P11P13P14P15eq HP4P5P6P8P9P11P13P14P15m4).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8P9P11P13P14P15mtmp;try rewrite HT2 in HP4P5P6P8P9P11P13P14P15mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P8 :: nil) 4 1 2 HP4P5P6P8P9P11P13P14P15mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP5P6P8P9P13P14P15m2. try clear HP4P5P6P8P9P11P13P14P15M4. try clear HP4P5P6P8P9P11P13P14P15m4. 

assert(HP8P9P13P14P15m2 : rk(P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP5P6P13Mtmp : rk(P5 :: P6 :: P13 :: nil) <= 2) by (solve_hyps_max HP5P6P13eq HP5P6P13M2).
	assert(HP5P6P8P9P13P14P15mtmp : rk(P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 3) by (solve_hyps_min HP5P6P8P9P13P14P15eq HP5P6P8P9P13P14P15m3).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P5 :: P6 :: P13 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P13 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) ((P5 :: P6 :: P13 :: nil) ++ (P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P6P8P9P13P14P15mtmp;try rewrite HT2 in HP5P6P8P9P13P14P15mtmp.
	assert(HT := rule_4 (P5 :: P6 :: P13 :: nil) (P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P13 :: nil) 3 1 2 HP5P6P8P9P13P14P15mtmp HP13mtmp HP5P6P13Mtmp Hincl); apply HT.
}
try clear HP5P6P13M2. try clear HP5P6P13m2. try clear HP8P9P13P14P15m1. try clear HP13M1. try clear HP13m1. try clear HP5P6P8P9P13P14P15M4. try clear HP5P6P8P9P13P14P15m3. 

assert(HP8P9P13P14P15m3 : rk(P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP2P3P9P13Mtmp : rk(P2 :: P3 :: P9 :: P13 :: nil) <= 3) by (solve_hyps_max HP2P3P9P13eq HP2P3P9P13M3).
	assert(HP2P3P8P9P13P14P15mtmp : rk(P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP2P3P8P9P13P14P15eq HP2P3P8P9P13P14P15m4).
	assert(HP9P13mtmp : rk(P9 :: P13 :: nil) >= 2) by (solve_hyps_min HP9P13eq HP9P13m2).
	assert(Hincl : incl (P9 :: P13 :: nil) (list_inter (P2 :: P3 :: P9 :: P13 :: nil) (P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P2 :: P3 :: P9 :: P13 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P9 :: P13 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) ((P2 :: P3 :: P9 :: P13 :: nil) ++ (P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P8P9P13P14P15mtmp;try rewrite HT2 in HP2P3P8P9P13P14P15mtmp.
	assert(HT := rule_4 (P2 :: P3 :: P9 :: P13 :: nil) (P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P9 :: P13 :: nil) 4 2 3 HP2P3P8P9P13P14P15mtmp HP9P13mtmp HP2P3P9P13Mtmp Hincl); apply HT.
}
try clear HP2P3P9P13M3. try clear HP2P3P9P13m3. try clear HP8P9P13P14P15m2. try clear HP2P3P8P9P13P14P15M4. try clear HP2P3P8P9P13P14P15m4. 

assert(HP8P9P13P14P15M3 : rk(P8 :: P9 :: P13 :: P14 :: P15 :: nil) <= 3).
{
	assert(HP8P9P13P14Mtmp : rk(P8 :: P9 :: P13 :: P14 :: nil) <= 3) by (solve_hyps_max HP8P9P13P14eq HP8P9P13P14M3).
	assert(HP8P9P13P15Mtmp : rk(P8 :: P9 :: P13 :: P15 :: nil) <= 3) by (solve_hyps_max HP8P9P13P15eq HP8P9P13P15M3).
	assert(HP8P9P13mtmp : rk(P8 :: P9 :: P13 :: nil) >= 3) by (solve_hyps_min HP8P9P13eq HP8P9P13m3).
	assert(Hincl : incl (P8 :: P9 :: P13 :: nil) (list_inter (P8 :: P9 :: P13 :: P14 :: nil) (P8 :: P9 :: P13 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P8 :: P9 :: P13 :: P14 :: P8 :: P9 :: P13 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P9 :: P13 :: P14 :: P8 :: P9 :: P13 :: P15 :: nil) ((P8 :: P9 :: P13 :: P14 :: nil) ++ (P8 :: P9 :: P13 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P8 :: P9 :: P13 :: P14 :: nil) (P8 :: P9 :: P13 :: P15 :: nil) (P8 :: P9 :: P13 :: nil) 3 3 3 HP8P9P13P14Mtmp HP8P9P13P15Mtmp HP8P9P13mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP8P9P13P14M3. try clear HP8P9P13P14m3. try clear HP8P9P13P15M3. try clear HP8P9P13P15m3. try clear HP8P9P13M3. try clear HP8P9P13m3. try clear HP8P9P13P14P15M4. 

assert(HP1P2P3P8P9P10P12P13P14P15m2 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P10P12P13P14P15m1. 

assert(HP1P2P3P8P9P10P12P13P14P15m3 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9P10P12P13P14P15m2. 

assert(HP1P2P3P8P9P10P12P13P14P15m4 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP1P2P3P12mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P12eq HP1P2P3P12m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) 4 4 HP1P2P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P12M4. try clear HP1P2P3P12m4. try clear HP1P2P3P8P9P10P12P13P14P15m3. 

assert(HP1P3P8P9P10P12P13P14P15m2 : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3M2. try clear HP1P3m2. try clear HP1P3P8P9P10P12P13P14P15m1. 

assert(HP1P3P8P9P10P12P13P14P15m3 : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P3P12mtmp : rk(P1 :: P3 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P3P12eq HP1P3P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P3P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P12M3. try clear HP1P3P12m3. try clear HP1P3P8P9P10P12P13P14P15m2. 

assert(HP1P3P8P9P10P12P13P14P15m4 : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP1P2P3P8P9P10P12P13P14P15mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P9P10P12P13P14P15eq HP1P2P3P8P9P10P12P13P14P15m4).
	assert(HP9P12mtmp : rk(P9 :: P12 :: nil) >= 2) by (solve_hyps_min HP9P12eq HP9P12m2).
	assert(Hincl : incl (P9 :: P12 :: nil) (list_inter (P2 :: P9 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) (P2 :: P9 :: P12 :: P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P12 :: P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) ((P2 :: P9 :: P12 :: nil) ++ (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P9P10P12P13P14P15mtmp;try rewrite HT2 in HP1P2P3P8P9P10P12P13P14P15mtmp.
	assert(HT := rule_4 (P2 :: P9 :: P12 :: nil) (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) (P9 :: P12 :: nil) 4 2 2 HP1P2P3P8P9P10P12P13P14P15mtmp HP9P12mtmp HP2P9P12Mtmp Hincl); apply HT.
}
try clear HP1P3P8P9P10P12P13P14P15m3. try clear HP1P2P3P8P9P10P12P13P14P15M4. try clear HP1P2P3P8P9P10P12P13P14P15m4. 

assert(HP1P2P5P6P8P9P10P11P12P13P14P15m2 : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P6P8P9P10P11P12P13P14P15m1. 

assert(HP1P2P5P6P8P9P10P11P12P13P14P15m3 : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P2P11mtmp : rk(P1 :: P2 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P2P11eq HP1P2P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P2P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P11M3. try clear HP1P2P11m3. try clear HP1P2P5P6P8P9P10P11P12P13P14P15m2. 

assert(HP1P2P5P6P8P9P10P11P12P13P14P15m4 : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP1P2P5P6P8P11mtmp : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P5P6P8P11eq HP1P2P5P6P8P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: P6 :: P8 :: P11 :: nil) (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 4 4 HP1P2P5P6P8P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P6P8P11M4. try clear HP1P2P5P6P8P11m4. try clear HP1P2P5P6P8P9P10P11P12P13P14P15m3. 

assert(HP1P5P6P8P9P10P11P12P13P14P15m2 : rk(P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 2 2 HP5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6M2. try clear HP5P6m2. try clear HP1P5P6P8P9P10P11P12P13P14P15m1. 

assert(HP1P5P6P8P9P10P11P12P13P14P15m3 : rk(P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP5P6P11mtmp : rk(P5 :: P6 :: P11 :: nil) >= 3) by (solve_hyps_min HP5P6P11eq HP5P6P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: P11 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: P11 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 3 3 HP5P6P11mtmp Hcomp Hincl);apply HT.
}
try clear HP5P6P11M3. try clear HP5P6P11m3. try clear HP1P5P6P8P9P10P11P12P13P14P15m2. 

assert(HP1P5P6P8P9P10P11P12P13P14P15m4 : rk(P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP2P5P11P12Mtmp : rk(P2 :: P5 :: P11 :: P12 :: nil) <= 3) by (solve_hyps_max HP2P5P11P12eq HP2P5P11P12M3).
	assert(HP1P2P5P6P8P9P10P11P12P13P14P15mtmp : rk(P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P2P5P6P8P9P10P11P12P13P14P15eq HP1P2P5P6P8P9P10P11P12P13P14P15m4).
	assert(HP5P11P12mtmp : rk(P5 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP5P11P12eq HP5P11P12m3).
	assert(Hincl : incl (P5 :: P11 :: P12 :: nil) (list_inter (P2 :: P5 :: P11 :: P12 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P2 :: P5 :: P11 :: P12 :: P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P11 :: P12 :: P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) ((P2 :: P5 :: P11 :: P12 :: nil) ++ (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P6P8P9P10P11P12P13P14P15mtmp;try rewrite HT2 in HP1P2P5P6P8P9P10P11P12P13P14P15mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P11 :: P12 :: nil) (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P5 :: P11 :: P12 :: nil) 4 3 3 HP1P2P5P6P8P9P10P11P12P13P14P15mtmp HP5P11P12mtmp HP2P5P11P12Mtmp Hincl); apply HT.
}
try clear HP2P5P11P12M3. try clear HP2P5P11P12m3. try clear HP1P5P6P8P9P10P11P12P13P14P15m3. try clear HP5P11P12M3. try clear HP5P11P12m3. try clear HP1P2P5P6P8P9P10P11P12P13P14P15M4. try clear HP1P2P5P6P8P9P10P11P12P13P14P15m4. 

assert(HP1P4P8P9P10P11P12P13P14P15m2 : rk(P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P9P10P11P12P13P14P15m1. 

assert(HP1P4P8P9P10P11P12P13P14P15m3 : rk(P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P4P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P9P10P11P12P13P14P15m2. 

assert(HP1P8P9P10P12P13P14P15m2 : rk(P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P9P10P11P12P13P14P15mtmp : rk(P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3) by (solve_hyps_min HP1P4P8P9P10P11P12P13P14P15eq HP1P4P8P9P10P11P12P13P14P15m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P4 :: P8 :: P11 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P9P10P11P12P13P14P15mtmp;try rewrite HT2 in HP1P4P8P9P10P11P12P13P14P15mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P9P10P11P12P13P14P15mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP1P8P9P10P12P13P14P15m1. try clear HP1P4P8P9P10P11P12P13P14P15M4. try clear HP1P4P8P9P10P11P12P13P14P15m3. 

assert(HP1P8P9P10P12P13P14P15m3 : rk(P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP5P6P9P10P11P13Mtmp : rk(P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) <= 3) by (solve_hyps_max HP5P6P9P10P11P13eq HP5P6P9P10P11P13M3).
	assert(HP1P5P6P8P9P10P11P12P13P14P15mtmp : rk(P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P5P6P8P9P10P11P12P13P14P15eq HP1P5P6P8P9P10P11P12P13P14P15m4).
	assert(HP9P10P13mtmp : rk(P9 :: P10 :: P13 :: nil) >= 2) by (solve_hyps_min HP9P10P13eq HP9P10P13m2).
	assert(Hincl : incl (P9 :: P10 :: P13 :: nil) (list_inter (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P6 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) ((P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) ++ (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P5P6P8P9P10P11P12P13P14P15mtmp;try rewrite HT2 in HP1P5P6P8P9P10P11P12P13P14P15mtmp.
	assert(HT := rule_4 (P5 :: P6 :: P9 :: P10 :: P11 :: P13 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) (P9 :: P10 :: P13 :: nil) 4 2 3 HP1P5P6P8P9P10P11P12P13P14P15mtmp HP9P10P13mtmp HP5P6P9P10P11P13Mtmp Hincl); apply HT.
}
try clear HP5P6P9P10P11P13M3. try clear HP5P6P9P10P11P13m3. try clear HP1P8P9P10P12P13P14P15m2. try clear HP1P5P6P8P9P10P11P12P13P14P15M4. try clear HP1P5P6P8P9P10P11P12P13P14P15m4. 

assert(HP1P8P9P10P12P13P14P15m4 : rk(P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP3P10P12Mtmp : rk(P3 :: P10 :: P12 :: nil) <= 2) by (solve_hyps_max HP3P10P12eq HP3P10P12M2).
	assert(HP1P3P8P9P10P12P13P14P15mtmp : rk(P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P3P8P9P10P12P13P14P15eq HP1P3P8P9P10P12P13P14P15m4).
	assert(HP10P12mtmp : rk(P10 :: P12 :: nil) >= 2) by (solve_hyps_min HP10P12eq HP10P12m2).
	assert(Hincl : incl (P10 :: P12 :: nil) (list_inter (P3 :: P10 :: P12 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) (P3 :: P10 :: P12 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P10 :: P12 :: P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) ((P3 :: P10 :: P12 :: nil) ++ (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P8P9P10P12P13P14P15mtmp;try rewrite HT2 in HP1P3P8P9P10P12P13P14P15mtmp.
	assert(HT := rule_4 (P3 :: P10 :: P12 :: nil) (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) (P10 :: P12 :: nil) 4 2 2 HP1P3P8P9P10P12P13P14P15mtmp HP10P12mtmp HP3P10P12Mtmp Hincl); apply HT.
}
try clear HP3P10P12M2. try clear HP3P10P12m2. try clear HP1P8P9P10P12P13P14P15m3. try clear HP10P12M2. try clear HP10P12m2. try clear HP1P3P8P9P10P12P13P14P15M4. try clear HP1P3P8P9P10P12P13P14P15m4. 

assert(HP1P2P9P12M3 : rk(P1 :: P2 :: P9 :: P12 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P9 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P9 :: P12 :: nil) (P1 :: P2 :: P9 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P9 :: P12 :: nil) ((P1 :: nil) ++ (P2 :: P9 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P2 :: P9 :: P12 :: nil) (nil) 1 2 0 HP1Mtmp HP2P9P12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1M1. try clear HP1m1. try clear HP1P2P9P12M4. 

assert(HP1P2P9P12m2 : rk(P1 :: P2 :: P9 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P9 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P9P12m1. 

assert(HP1P2P9P12m3 : rk(P1 :: P2 :: P9 :: P12 :: nil) >= 3).
{
	assert(HP1P2P12mtmp : rk(P1 :: P2 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P2P12eq HP1P2P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P12 :: nil) (P1 :: P2 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P12 :: nil) (P1 :: P2 :: P9 :: P12 :: nil) 3 3 HP1P2P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P12M3. try clear HP1P2P12m3. try clear HP1P2P9P12m2. 

assert(HP1P9P12m2 : rk(P1 :: P9 :: P12 :: nil) >= 2).
{
	assert(HP1P12mtmp : rk(P1 :: P12 :: nil) >= 2) by (solve_hyps_min HP1P12eq HP1P12m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P12 :: nil) (P1 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P12 :: nil) (P1 :: P9 :: P12 :: nil) 2 2 HP1P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P12M2. try clear HP1P12m2. try clear HP1P9P12m1. 

assert(HP1P9P12m3 : rk(P1 :: P9 :: P12 :: nil) >= 3).
{
	assert(HP2P9P12Mtmp : rk(P2 :: P9 :: P12 :: nil) <= 2) by (solve_hyps_max HP2P9P12eq HP2P9P12M2).
	assert(HP1P2P9P12mtmp : rk(P1 :: P2 :: P9 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P2P9P12eq HP1P2P9P12m3).
	assert(HP9P12mtmp : rk(P9 :: P12 :: nil) >= 2) by (solve_hyps_min HP9P12eq HP9P12m2).
	assert(Hincl : incl (P9 :: P12 :: nil) (list_inter (P1 :: P9 :: P12 :: nil) (P2 :: P9 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P9 :: P12 :: nil) (P1 :: P9 :: P12 :: P2 :: P9 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P9 :: P12 :: P2 :: P9 :: P12 :: nil) ((P1 :: P9 :: P12 :: nil) ++ (P2 :: P9 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P9P12mtmp;try rewrite HT2 in HP1P2P9P12mtmp.
	assert(HT := rule_2 (P1 :: P9 :: P12 :: nil) (P2 :: P9 :: P12 :: nil) (P9 :: P12 :: nil) 3 2 2 HP1P2P9P12mtmp HP9P12mtmp HP2P9P12Mtmp Hincl);apply HT.
}
try clear HP1P9P12m2. try clear HP2P9P12M2. try clear HP2P9P12m2. try clear HP9P12M2. try clear HP9P12m2. try clear HP1P2P9P12M3. try clear HP1P2P9P12m3. 

assert(HP1P4P8P9P11P12P13P14P15m2 : rk(P1 :: P4 :: P8 :: P9 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P9P11P12P13P14P15m1. 

assert(HP1P4P8P9P11P12P13P14P15m3 : rk(P1 :: P4 :: P8 :: P9 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P9 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P9 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P4P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P9P11P12P13P14P15m2. 

assert(HP1P8P9P12P13P14P15m2 : rk(P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P9P11P12P13P14P15mtmp : rk(P1 :: P4 :: P8 :: P9 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3) by (solve_hyps_min HP1P4P8P9P11P12P13P14P15eq HP1P4P8P9P11P12P13P14P15m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P9 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P4 :: P8 :: P11 :: P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P9P11P12P13P14P15mtmp;try rewrite HT2 in HP1P4P8P9P11P12P13P14P15mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P9P11P12P13P14P15mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP1P8P9P12P13P14P15m1. try clear HP1P4P8P9P11P12P13P14P15M4. try clear HP1P4P8P9P11P12P13P14P15m3. 

assert(HP1P8P9P12P13P14P15m3 : rk(P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P9P12mtmp : rk(P1 :: P9 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P9P12eq HP1P9P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P9 :: P12 :: nil) (P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P9 :: P12 :: nil) (P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P9P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P9P12M3. try clear HP1P9P12m3. try clear HP1P8P9P12P13P14P15m2. 

assert(HP1P8P9P12P13P14P15m4 : rk(P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP9P10P13Mtmp : rk(P9 :: P10 :: P13 :: nil) <= 2) by (solve_hyps_max HP9P10P13eq HP9P10P13M2).
	assert(HP1P8P9P10P12P13P14P15mtmp : rk(P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P8P9P10P12P13P14P15eq HP1P8P9P10P12P13P14P15m4).
	assert(HP9P13mtmp : rk(P9 :: P13 :: nil) >= 2) by (solve_hyps_min HP9P13eq HP9P13m2).
	assert(Hincl : incl (P9 :: P13 :: nil) (list_inter (P9 :: P10 :: P13 :: nil) (P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) (P9 :: P10 :: P13 :: P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P9 :: P10 :: P13 :: P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) ((P9 :: P10 :: P13 :: nil) ++ (P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P8P9P10P12P13P14P15mtmp;try rewrite HT2 in HP1P8P9P10P12P13P14P15mtmp.
	assert(HT := rule_4 (P9 :: P10 :: P13 :: nil) (P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) (P9 :: P13 :: nil) 4 2 2 HP1P8P9P10P12P13P14P15mtmp HP9P13mtmp HP9P10P13Mtmp Hincl); apply HT.
}
try clear HP9P10P13M2. try clear HP9P10P13m2. try clear HP1P8P9P12P13P14P15m3. try clear HP9P13M2. try clear HP9P13m2. 

assert(HP1P2P3P8P13m2 : rk(P1 :: P2 :: P3 :: P8 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P13m1. 

assert(HP1P2P3P8P13m3 : rk(P1 :: P2 :: P3 :: P8 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P13m2. 

assert(HP1P2P3P8P13m4 : rk(P1 :: P2 :: P3 :: P8 :: P13 :: nil) >= 4).
{
	assert(HP1P2P3P8mtmp : rk(P1 :: P2 :: P3 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8eq HP1P2P3P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P13 :: nil) 4 4 HP1P2P3P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8M4. try clear HP1P2P3P8m4. try clear HP1P2P3P8P13m3. 

assert(HP1P4P8P11P13m2 : rk(P1 :: P4 :: P8 :: P11 :: P13 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P13m1. 

assert(HP1P4P8P11P13m3 : rk(P1 :: P4 :: P8 :: P11 :: P13 :: nil) >= 3).
{
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: nil) 3 3 HP1P4P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P13m2. 

assert(HP1P8P13m2 : rk(P1 :: P8 :: P13 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P11P13mtmp : rk(P1 :: P4 :: P8 :: P11 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P4P8P11P13eq HP1P4P8P11P13m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P11 :: P13 :: nil) (P4 :: P8 :: P11 :: P1 :: P8 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P1 :: P8 :: P13 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P1 :: P8 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P11P13mtmp;try rewrite HT2 in HP1P4P8P11P13mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P13 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P11P13mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP1P8P13m1. try clear HP1P4P8P11P13M4. try clear HP1P4P8P11P13m3. 

assert(HP1P8P13m3 : rk(P1 :: P8 :: P13 :: nil) >= 3).
{
	assert(HP1P2P3P13Mtmp : rk(P1 :: P2 :: P3 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P13eq HP1P2P3P13M3).
	assert(HP1P2P3P8P13mtmp : rk(P1 :: P2 :: P3 :: P8 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P8P13eq HP1P2P3P8P13m4).
	assert(HP1P13mtmp : rk(P1 :: P13 :: nil) >= 2) by (solve_hyps_min HP1P13eq HP1P13m2).
	assert(Hincl : incl (P1 :: P13 :: nil) (list_inter (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P8 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P13 :: nil) (P1 :: P2 :: P3 :: P13 :: P1 :: P8 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P13 :: P1 :: P8 :: P13 :: nil) ((P1 :: P2 :: P3 :: P13 :: nil) ++ (P1 :: P8 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P13mtmp;try rewrite HT2 in HP1P2P3P8P13mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P8 :: P13 :: nil) (P1 :: P13 :: nil) 4 2 3 HP1P2P3P8P13mtmp HP1P13mtmp HP1P2P3P13Mtmp Hincl); apply HT.
}
try clear HP1P2P3P13M3. try clear HP1P2P3P13m3. try clear HP1P8P13m2. try clear HP1P13M2. try clear HP1P13m2. try clear HP1P2P3P8P13M4. try clear HP1P2P3P8P13m4. 

assert(HP1P2P3P4P8P10P11P12m2 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2M2. try clear HP1P2m2. try clear HP1P2P3P4P8P10P11P12m1. 

assert(HP1P2P3P4P8P10P11P12m3 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3M3. try clear HP1P2P3m3. try clear HP1P2P3P4P8P10P11P12m2. 

assert(HP1P2P3P4P8P10P11P12m4 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) >= 4).
{
	assert(HP1P2P3P11mtmp : rk(P1 :: P2 :: P3 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P3P11eq HP1P2P3P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) 4 4 HP1P2P3P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P11M4. try clear HP1P2P3P11m4. try clear HP1P2P3P4P8P10P11P12m3. 

assert(HP1P4P8P10P11P12m2 : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P10P11P12m1. 

assert(HP1P4P8P10P11P12m3 : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) >= 3).
{
	assert(HP1P2P3P4P11Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P11eq HP1P2P3P4P11M4).
	assert(HP1P2P3P4P8P10P11P12mtmp : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P8P10P11P12eq HP1P2P3P4P8P10P11P12m4).
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P4 :: P11 :: nil) ++ (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P8P10P11P12mtmp;try rewrite HT2 in HP1P2P3P4P8P10P11P12mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) (P1 :: P4 :: P11 :: nil) 4 3 4 HP1P2P3P4P8P10P11P12mtmp HP1P4P11mtmp HP1P2P3P4P11Mtmp Hincl); apply HT.
}
try clear HP1P2P3P4P11M4. try clear HP1P2P3P4P11m4. try clear HP1P4P8P10P11P12m2. try clear HP1P2P3P4P8P10P11P12M4. try clear HP1P2P3P4P8P10P11P12m4. 

assert(HP1P8P10P12M3 : rk(P1 :: P8 :: P10 :: P12 :: nil) <= 3).
{
	assert(HP10Mtmp : rk(P10 :: nil) <= 1) by (solve_hyps_max HP10eq HP10M1).
	assert(HP1P8P12Mtmp : rk(P1 :: P8 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P8P12eq HP1P8P12M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P10 :: nil) (P1 :: P8 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P10 :: P12 :: nil) (P10 :: P1 :: P8 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P10 :: P1 :: P8 :: P12 :: nil) ((P10 :: nil) ++ (P1 :: P8 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P10 :: nil) (P1 :: P8 :: P12 :: nil) (nil) 1 2 0 HP10Mtmp HP1P8P12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP10M1. try clear HP10m1. try clear HP1P8P12M2. try clear HP1P8P12m2. try clear HP1P8P10P12M4. 

assert(HP1P8P10P12m2 : rk(P1 :: P8 :: P10 :: P12 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P10P11P12mtmp : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P4P8P10P11P12eq HP1P4P8P10P11P12m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P10 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P10 :: P11 :: P12 :: nil) (P4 :: P8 :: P11 :: P1 :: P8 :: P10 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P1 :: P8 :: P10 :: P12 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P1 :: P8 :: P10 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P10P11P12mtmp;try rewrite HT2 in HP1P4P8P10P11P12mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P10 :: P12 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P10P11P12mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP1P8P10P12m1. try clear HP1P4P8P10P11P12M4. try clear HP1P4P8P10P11P12m3. 

assert(HP1P8P10P12m3 : rk(P1 :: P8 :: P10 :: P12 :: nil) >= 3).
{
	assert(HP1P10P12mtmp : rk(P1 :: P10 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P10P12eq HP1P10P12m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P10 :: P12 :: nil) (P1 :: P8 :: P10 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P10 :: P12 :: nil) (P1 :: P8 :: P10 :: P12 :: nil) 3 3 HP1P10P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P10P12M3. try clear HP1P10P12m3. try clear HP1P8P10P12m2. 

assert(HP1P4P8P9P11P13P14P15m2 : rk(P1 :: P4 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4M2. try clear HP1P4m2. try clear HP1P4P8P9P11P13P14P15m1. 

assert(HP1P4P8P9P11P13P14P15m3 : rk(P1 :: P4 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P4P11mtmp : rk(P1 :: P4 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P4P11eq HP1P4P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P11 :: nil) (P1 :: P4 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) 3 3 HP1P4P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P11M3. try clear HP1P4P11m3. try clear HP1P4P8P9P11P13P14P15m2. 

assert(HP1P8P9P13P14P15m2 : rk(P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP4P8P11Mtmp : rk(P4 :: P8 :: P11 :: nil) <= 2) by (solve_hyps_max HP4P8P11eq HP4P8P11M2).
	assert(HP1P4P8P9P11P13P14P15mtmp : rk(P1 :: P4 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) >= 3) by (solve_hyps_min HP1P4P8P9P11P13P14P15eq HP1P4P8P9P11P13P14P15m3).
	assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m1).
	assert(Hincl : incl (P8 :: nil) (list_inter (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P9 :: P11 :: P13 :: P14 :: P15 :: nil) (P4 :: P8 :: P11 :: P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P8 :: P11 :: P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) ((P4 :: P8 :: P11 :: nil) ++ (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P9P11P13P14P15mtmp;try rewrite HT2 in HP1P4P8P9P11P13P14P15mtmp.
	assert(HT := rule_4 (P4 :: P8 :: P11 :: nil) (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P8 :: nil) 3 1 2 HP1P4P8P9P11P13P14P15mtmp HP8mtmp HP4P8P11Mtmp Hincl); apply HT.
}
try clear HP4P8P11M2. try clear HP4P8P11m2. try clear HP1P8P9P13P14P15m1. try clear HP8M1. try clear HP8m1. try clear HP1P4P8P9P11P13P14P15M4. try clear HP1P4P8P9P11P13P14P15m3. 

assert(HP1P8P9P13P14P15m3 : rk(P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 3).
{
	assert(HP1P8P10P12Mtmp : rk(P1 :: P8 :: P10 :: P12 :: nil) <= 3) by (solve_hyps_max HP1P8P10P12eq HP1P8P10P12M3).
	assert(HP1P8P9P10P12P13P14P15mtmp : rk(P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P8P9P10P12P13P14P15eq HP1P8P9P10P12P13P14P15m4).
	assert(HP1P8mtmp : rk(P1 :: P8 :: nil) >= 2) by (solve_hyps_min HP1P8eq HP1P8m2).
	assert(Hincl : incl (P1 :: P8 :: nil) (list_inter (P1 :: P8 :: P10 :: P12 :: nil) (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P9 :: P10 :: P12 :: P13 :: P14 :: P15 :: nil) (P1 :: P8 :: P10 :: P12 :: P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P10 :: P12 :: P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) ((P1 :: P8 :: P10 :: P12 :: nil) ++ (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P8P9P10P12P13P14P15mtmp;try rewrite HT2 in HP1P8P9P10P12P13P14P15mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P10 :: P12 :: nil) (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P1 :: P8 :: nil) 4 2 3 HP1P8P9P10P12P13P14P15mtmp HP1P8mtmp HP1P8P10P12Mtmp Hincl); apply HT.
}
try clear HP1P8P10P12M3. try clear HP1P8P10P12m3. try clear HP1P8P9P13P14P15m2. try clear HP1P8M2. try clear HP1P8m2. try clear HP1P8P9P10P12P13P14P15M4. try clear HP1P8P9P10P12P13P14P15m4. 

assert(HP1P8P9P13P14P15m4 : rk(P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	assert(HP1P8P12P13Mtmp : rk(P1 :: P8 :: P12 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P8P12P13eq HP1P8P12P13M3).
	assert(HP1P8P9P12P13P14P15mtmp : rk(P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P8P9P12P13P14P15eq HP1P8P9P12P13P14P15m4).
	assert(HP1P8P13mtmp : rk(P1 :: P8 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P8P13eq HP1P8P13m3).
	assert(Hincl : incl (P1 :: P8 :: P13 :: nil) (list_inter (P1 :: P8 :: P12 :: P13 :: nil) (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P9 :: P12 :: P13 :: P14 :: P15 :: nil) (P1 :: P8 :: P12 :: P13 :: P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P12 :: P13 :: P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) ((P1 :: P8 :: P12 :: P13 :: nil) ++ (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P8P9P12P13P14P15mtmp;try rewrite HT2 in HP1P8P9P12P13P14P15mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P12 :: P13 :: nil) (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P1 :: P8 :: P13 :: nil) 4 3 3 HP1P8P9P12P13P14P15mtmp HP1P8P13mtmp HP1P8P12P13Mtmp Hincl); apply HT.
}
try clear HP1P8P12P13M3. try clear HP1P8P12P13m3. try clear HP1P8P9P13P14P15m3. try clear HP1P8P13M3. try clear HP1P8P13m3. try clear HP1P8P9P12P13P14P15M4. try clear HP1P8P9P12P13P14P15m4. 

assert(HP13P14P15m2 : rk(P13 :: P14 :: P15 :: nil) >= 2).
{
	assert(HP1P3P8P14Mtmp : rk(P1 :: P3 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P3P8P14eq HP1P3P8P14M3).
	assert(HP1P3P8P13P14P15mtmp : rk(P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P3P8P13P14P15eq HP1P3P8P13P14P15m4).
	assert(HP14mtmp : rk(P14 :: nil) >= 1) by (solve_hyps_min HP14eq HP14m1).
	assert(Hincl : incl (P14 :: nil) (list_inter (P1 :: P3 :: P8 :: P14 :: nil) (P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P8 :: P13 :: P14 :: P15 :: nil) (P1 :: P3 :: P8 :: P14 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P8 :: P14 :: P13 :: P14 :: P15 :: nil) ((P1 :: P3 :: P8 :: P14 :: nil) ++ (P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P8P13P14P15mtmp;try rewrite HT2 in HP1P3P8P13P14P15mtmp.
	assert(HT := rule_4 (P1 :: P3 :: P8 :: P14 :: nil) (P13 :: P14 :: P15 :: nil) (P14 :: nil) 4 1 3 HP1P3P8P13P14P15mtmp HP14mtmp HP1P3P8P14Mtmp Hincl); apply HT.
}
try clear HP1P3P8P14M3. try clear HP1P3P8P14m3. try clear HP13P14P15m1. try clear HP14M1. try clear HP14m1. try clear HP1P3P8P13P14P15M4. try clear HP1P3P8P13P14P15m4. 

assert(HP13P14P15M2 : rk(P13 :: P14 :: P15 :: nil) <= 2).
{
	assert(HP1P13P14P15Mtmp : rk(P1 :: P13 :: P14 :: P15 :: nil) <= 3) by (solve_hyps_max HP1P13P14P15eq HP1P13P14P15M3).
	assert(HP8P9P13P14P15Mtmp : rk(P8 :: P9 :: P13 :: P14 :: P15 :: nil) <= 3) by (solve_hyps_max HP8P9P13P14P15eq HP8P9P13P14P15M3).
	assert(HP1P8P9P13P14P15mtmp : rk(P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) >= 4) by (solve_hyps_min HP1P8P9P13P14P15eq HP1P8P9P13P14P15m4).
	assert(Hincl : incl (P13 :: P14 :: P15 :: nil) (list_inter (P1 :: P13 :: P14 :: P15 :: nil) (P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P1 :: P13 :: P14 :: P15 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P13 :: P14 :: P15 :: P8 :: P9 :: P13 :: P14 :: P15 :: nil) ((P1 :: P13 :: P14 :: P15 :: nil) ++ (P8 :: P9 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P8P9P13P14P15mtmp;try rewrite HT2 in HP1P8P9P13P14P15mtmp.
	assert(HT := rule_3 (P1 :: P13 :: P14 :: P15 :: nil) (P8 :: P9 :: P13 :: P14 :: P15 :: nil) (P13 :: P14 :: P15 :: nil) 3 3 4 HP1P13P14P15Mtmp HP8P9P13P14P15Mtmp HP1P8P9P13P14P15mtmp Hincl);apply HT.
}
try clear HP1P13P14P15M3. try clear HP1P13P14P15m3. try clear HP8P9P13P14P15M3. try clear HP8P9P13P14P15m3. try clear HP13P14P15M3. try clear HP1P8P9P13P14P15M4. try clear HP1P8P9P13P14P15m4. 

assert(rk(P13 :: P14 :: P15 ::  nil) <= 3) by (solve[apply matroid1_b_useful;simpl;repeat constructor|apply rk_upper_dim]).
assert(rk(P13 :: P14 :: P15 ::  nil) >= 1) by (solve[apply matroid1_b_useful2;simpl;repeat constructor|apply matroid1_a]).
omega.
Qed.