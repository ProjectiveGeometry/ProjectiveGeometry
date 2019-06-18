Require Export ProjectiveGeometry.Dev.lemmas_automation_g.

Lemma harmonic_conjugate : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14,
rk(P1 :: P2 :: P3 :: nil) = 2 ->
rk(P1 :: P2 :: nil) = 2 -> rk(P1 :: P3 :: nil) = 2 -> rk(P2 :: P3 :: nil) = 2 ->
rk(P4 :: P5 :: P6 :: nil) = 3 -> rk(P8 :: P9 :: P10 :: nil) = 3 ->
rk(P1 :: P2 :: P4 :: P8 :: nil) = 4 ->
rk(P1 :: P2 :: P4 :: nil) = 3 -> rk(P1 :: P2 :: P5 :: nil) = 3 -> 
rk(P1 :: P4 :: P5 :: nil) = 2 -> rk(P2 :: P4 :: P6 :: nil) = 2 -> rk(P3 :: P5 :: P6 :: nil) = 2 -> 
rk(P1 :: P6 :: P7 :: nil) = 2 -> rk(P2 :: P5 :: P7 :: nil) = 2 -> rk(P4 :: P7 :: P12 :: nil) = 2 ->
rk(P1 :: P2 :: P8 :: nil) = 3 -> rk(P1 :: P2 :: P9 :: nil) = 3 -> 
rk(P1 :: P8 :: P9 :: nil) = 2 -> rk(P2 :: P8 :: P10 :: nil) = 2 -> rk(P3 :: P9 :: P10 :: nil) = 2 -> 
rk(P1 :: P10 :: P11 :: nil) = 2 -> rk(P2 :: P9 :: P11 :: nil) = 2 -> rk(P8 :: P11 :: P13 :: nil) = 2 ->
rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) = 2 ->
rk(P6 :: P10 :: P14 :: nil) = 2 -> rk(P5 :: P9 :: P14 :: nil) = 2 ->
rk(P12 :: P13 :: nil) = 1.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 
HP1P2P3eq HP1P2eq HP1P3eq HP2P3eq HP4P5P6eq HP8P9P10eq HP1P2P4P8eq HP1P2P4eq 
HP1P2P5eq HP1P4P5eq HP2P4P6eq HP3P5P6eq HP1P6P7eq HP2P5P7eq HP4P7P12eq HP1P2P8eq HP1P2P9eq HP1P8P9eq HP2P8P10eq HP3P9P10eq HP1P10P11eq HP2P9P11eq HP8P11P13eq HP1P2P3P12P13eq HP6P10P14eq HP5P9P14eq.

assert(HP1P2P4P6M3 : rk(P1 :: P2 :: P4 :: P6 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP2P4P6Mtmp : rk(P2 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP2P4P6eq HP2P4P6M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P4 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P6 :: nil) (P1 :: P2 :: P4 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P4 :: P6 :: nil) ((P1 :: nil) ++ (P2 :: P4 :: P6 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P2 :: P4 :: P6 :: nil) (nil) 1 2 0 HP1Mtmp HP2P4P6Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P4P6M4. 

assert(HP1P2P4P6m2 : rk(P1 :: P2 :: P4 :: P6 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P6 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6m1. 

assert(HP1P2P4P6m3 : rk(P1 :: P2 :: P4 :: P6 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P6 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6m2. 

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
try clear HP4P6m1. 

assert(HP1P4m2 : rk(P1 :: P4 :: nil) >= 2).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: nil) (P2 :: P1 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P4 :: nil) ((P2 :: nil) ++ (P1 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4mtmp;try rewrite HT2 in HP1P2P4mtmp.
	assert(HT := rule_4 (P2 :: nil) (P1 :: P4 :: nil) (nil) 3 0 1 HP1P2P4mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}
try clear HP1P4m1. 

assert(HP1P4P6m2 : rk(P1 :: P4 :: P6 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P6 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P6m1. 

assert(HP1P4P6m3 : rk(P1 :: P4 :: P6 :: nil) >= 3).
{
	assert(HP2P4P6Mtmp : rk(P2 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP2P4P6eq HP2P4P6M2).
	assert(HP1P2P4P6mtmp : rk(P1 :: P2 :: P4 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P4P6eq HP1P2P4P6m3).
	assert(HP4P6mtmp : rk(P4 :: P6 :: nil) >= 2) by (solve_hyps_min HP4P6eq HP4P6m2).
	assert(Hincl : incl (P4 :: P6 :: nil) (list_inter (P1 :: P4 :: P6 :: nil) (P2 :: P4 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P6 :: nil) (P1 :: P4 :: P6 :: P2 :: P4 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P6 :: P2 :: P4 :: P6 :: nil) ((P1 :: P4 :: P6 :: nil) ++ (P2 :: P4 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P6mtmp;try rewrite HT2 in HP1P2P4P6mtmp.
	assert(HT := rule_2 (P1 :: P4 :: P6 :: nil) (P2 :: P4 :: P6 :: nil) (P4 :: P6 :: nil) 3 2 2 HP1P2P4P6mtmp HP4P6mtmp HP2P4P6Mtmp Hincl);apply HT.
}
try clear HP1P4P6m2. 

assert(HP1P4P6P7M3 : rk(P1 :: P4 :: P6 :: P7 :: nil) <= 3).
{
	assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M1).
	assert(HP1P6P7Mtmp : rk(P1 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P6P7eq HP1P6P7M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: nil) (P1 :: P6 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P6 :: P7 :: nil) (P4 :: P1 :: P6 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P1 :: P6 :: P7 :: nil) ((P4 :: nil) ++ (P1 :: P6 :: P7 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: nil) (P1 :: P6 :: P7 :: nil) (nil) 1 2 0 HP4Mtmp HP1P6P7Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P6P7M4. 

assert(HP1P4P6P7m2 : rk(P1 :: P4 :: P6 :: P7 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P6 :: P7 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P6P7m1. 

assert(HP1P4P6P7m3 : rk(P1 :: P4 :: P6 :: P7 :: nil) >= 3).
{
	assert(HP1P4P6mtmp : rk(P1 :: P4 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P4P6eq HP1P4P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P6 :: nil) (P1 :: P4 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P6 :: nil) (P1 :: P4 :: P6 :: P7 :: nil) 3 3 HP1P4P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P6P7m2. 

assert(HP1P2P5P7M3 : rk(P1 :: P2 :: P5 :: P7 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P5 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P7 :: nil) (P1 :: P2 :: P5 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P5 :: P7 :: nil) ((P1 :: nil) ++ (P2 :: P5 :: P7 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P2 :: P5 :: P7 :: nil) (nil) 1 2 0 HP1Mtmp HP2P5P7Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P5P7M4. 

assert(HP1P2P5P7m2 : rk(P1 :: P2 :: P5 :: P7 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P7 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P7m1. 

assert(HP1P2P5P7m3 : rk(P1 :: P2 :: P5 :: P7 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P7 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P7m2. 

assert(HP1P7m2 : rk(P1 :: P7 :: nil) >= 2).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP1P2P5P7mtmp : rk(P1 :: P2 :: P5 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P5P7eq HP1P2P5P7m3).
	assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m1).
	assert(Hincl : incl (P7 :: nil) (list_inter (P1 :: P7 :: nil) (P2 :: P5 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P7 :: nil) (P1 :: P7 :: P2 :: P5 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P7 :: P2 :: P5 :: P7 :: nil) ((P1 :: P7 :: nil) ++ (P2 :: P5 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P7mtmp;try rewrite HT2 in HP1P2P5P7mtmp.
	assert(HT := rule_2 (P1 :: P7 :: nil) (P2 :: P5 :: P7 :: nil) (P7 :: nil) 3 1 2 HP1P2P5P7mtmp HP7mtmp HP2P5P7Mtmp Hincl);apply HT.
}
try clear HP1P7m1. 

assert(HP1P4P7m2 : rk(P1 :: P4 :: P7 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P7 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P7m1. 

assert(HP1P4P7m3 : rk(P1 :: P4 :: P7 :: nil) >= 3).
{
	assert(HP1P6P7Mtmp : rk(P1 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P6P7eq HP1P6P7M2).
	assert(HP1P4P6P7mtmp : rk(P1 :: P4 :: P6 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P4P6P7eq HP1P4P6P7m3).
	assert(HP1P7mtmp : rk(P1 :: P7 :: nil) >= 2) by (solve_hyps_min HP1P7eq HP1P7m2).
	assert(Hincl : incl (P1 :: P7 :: nil) (list_inter (P1 :: P4 :: P7 :: nil) (P1 :: P6 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P6 :: P7 :: nil) (P1 :: P4 :: P7 :: P1 :: P6 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P7 :: P1 :: P6 :: P7 :: nil) ((P1 :: P4 :: P7 :: nil) ++ (P1 :: P6 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P6P7mtmp;try rewrite HT2 in HP1P4P6P7mtmp.
	assert(HT := rule_2 (P1 :: P4 :: P7 :: nil) (P1 :: P6 :: P7 :: nil) (P1 :: P7 :: nil) 3 2 2 HP1P4P6P7mtmp HP1P7mtmp HP1P6P7Mtmp Hincl);apply HT.
}
try clear HP1P4P7m2. try clear HP1P4P6P7M3. try clear HP1P4P6P7m3. 

assert(HP1P4P7P12M3 : rk(P1 :: P4 :: P7 :: P12 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP4P7P12Mtmp : rk(P4 :: P7 :: P12 :: nil) <= 2) by (solve_hyps_max HP4P7P12eq HP4P7P12M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P4 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P7 :: P12 :: nil) (P1 :: P4 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P7 :: P12 :: nil) ((P1 :: nil) ++ (P4 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P4 :: P7 :: P12 :: nil) (nil) 1 2 0 HP1Mtmp HP4P7P12Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P7P12M4. 

assert(HP1P4P7P12m2 : rk(P1 :: P4 :: P7 :: P12 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P7 :: P12 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P7P12m1. 

assert(HP1P4P7P12m3 : rk(P1 :: P4 :: P7 :: P12 :: nil) >= 3).
{
	assert(HP1P4P7mtmp : rk(P1 :: P4 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P4P7eq HP1P4P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P7 :: nil) (P1 :: P4 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P7 :: nil) (P1 :: P4 :: P7 :: P12 :: nil) 3 3 HP1P4P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P7P12m2. 

assert(HP1P12m2 : rk(P1 :: P12 :: nil) >= 2).
{
	assert(HP4P7P12Mtmp : rk(P4 :: P7 :: P12 :: nil) <= 2) by (solve_hyps_max HP4P7P12eq HP4P7P12M2).
	assert(HP1P4P7P12mtmp : rk(P1 :: P4 :: P7 :: P12 :: nil) >= 3) by (solve_hyps_min HP1P4P7P12eq HP1P4P7P12m3).
	assert(HP12mtmp : rk(P12 :: nil) >= 1) by (solve_hyps_min HP12eq HP12m1).
	assert(Hincl : incl (P12 :: nil) (list_inter (P1 :: P12 :: nil) (P4 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P7 :: P12 :: nil) (P1 :: P12 :: P4 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P12 :: P4 :: P7 :: P12 :: nil) ((P1 :: P12 :: nil) ++ (P4 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P7P12mtmp;try rewrite HT2 in HP1P4P7P12mtmp.
	assert(HT := rule_2 (P1 :: P12 :: nil) (P4 :: P7 :: P12 :: nil) (P12 :: nil) 3 1 2 HP1P4P7P12mtmp HP12mtmp HP4P7P12Mtmp Hincl);apply HT.
}
try clear HP1P12m1. try clear HP1P4P7P12M3. try clear HP1P4P7P12m3. 

assert(HP1P12P13m2 : rk(P1 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P12mtmp : rk(P1 :: P12 :: nil) >= 2) by (solve_hyps_min HP1P12eq HP1P12m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P12 :: nil) (P1 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P12 :: nil) (P1 :: P12 :: P13 :: nil) 2 2 HP1P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P12P13m1. 

assert(HP1P12P13M2 : rk(P1 :: P12 :: P13 :: nil) <= 2).
{
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P12 :: P13 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P12 :: P13 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) 2 2 HP1P2P3P12P13Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P12P13M3. 

assert(HP1P2P4P8P12P13P14m2 : rk(P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P12P13P14m1. 

assert(HP1P2P4P8P12P13P14m3 : rk(P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P12P13P14m2. 

assert(HP1P2P4P8P12P13P14m4 : rk(P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P12P13P14m3. 

assert(HP1P2P12m2 : rk(P1 :: P2 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P12m1. 

assert(HP1P2P12M2 : rk(P1 :: P2 :: P12 :: nil) <= 2).
{
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P12 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P2 :: P12 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) 2 2 HP1P2P3P12P13Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P12M3. 

assert(HP1P4P8m3 : rk(P1 :: P4 :: P8 :: nil) >= 3).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P4 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: nil) (P2 :: P1 :: P4 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P4 :: P8 :: nil) ((P2 :: nil) ++ (P1 :: P4 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8mtmp;try rewrite HT2 in HP1P2P4P8mtmp.
	assert(HT := rule_4 (P2 :: nil) (P1 :: P4 :: P8 :: nil) (nil) 4 0 1 HP1P2P4P8mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}
try clear HP1P4P8m1. 

assert(HP1P4P8P12P13P14m2 : rk(P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P12P13P14m1. 

assert(HP1P4P8P12P13P14m3 : rk(P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P12P13P14m2. 

assert(HP1P4P8P12P13P14m4 : rk(P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P2P12Mtmp : rk(P1 :: P2 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P2P12eq HP1P2P12M2).
	assert(HP1P2P4P8P12P13P14mtmp : rk(P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8P12P13P14eq HP1P2P4P8P12P13P14m4).
	assert(HP1P12mtmp : rk(P1 :: P12 :: nil) >= 2) by (solve_hyps_min HP1P12eq HP1P12m2).
	assert(Hincl : incl (P1 :: P12 :: nil) (list_inter (P1 :: P2 :: P12 :: nil) (P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) (P1 :: P2 :: P12 :: P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P12 :: P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) ((P1 :: P2 :: P12 :: nil) ++ (P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8P12P13P14mtmp;try rewrite HT2 in HP1P2P4P8P12P13P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P12 :: nil) (P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) (P1 :: P12 :: nil) 4 2 2 HP1P2P4P8P12P13P14mtmp HP1P12mtmp HP1P2P12Mtmp Hincl); apply HT.
}
try clear HP1P4P8P12P13P14m3. try clear HP1P2P4P8P12P13P14M4. try clear HP1P2P4P8P12P13P14m4. 

assert(HP1P2P4P5P8m2 : rk(P1 :: P2 :: P4 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P8m1. 

assert(HP1P2P4P5P8m3 : rk(P1 :: P2 :: P4 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P8 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P8m2. 

assert(HP1P2P4P5P8m4 : rk(P1 :: P2 :: P4 :: P5 :: P8 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P8 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P8m3. 

assert(HP1P2P4P5P7P8P12m2 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P8P12m1. 

assert(HP1P2P4P5P7P8P12m3 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P8P12m2. 

assert(HP1P2P4P5P7P8P12m4 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P8P12m3. 

assert(HP1P5m2 : rk(P1 :: P5 :: nil) >= 2).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: nil) (P2 :: P1 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P5 :: nil) ((P2 :: nil) ++ (P1 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5mtmp;try rewrite HT2 in HP1P2P5mtmp.
	assert(HT := rule_4 (P2 :: nil) (P1 :: P5 :: nil) (nil) 3 0 1 HP1P2P5mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}
try clear HP1P5m1. 

assert(HP1P2P4P5P7m2 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7m1. 

assert(HP1P2P4P5P7m3 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7m2. 

assert(HP1P2P4P5P7M3 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: nil) <= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m1).
	assert(Hincl : incl (P5 :: nil) (list_inter (P1 :: P4 :: P5 :: nil) (P2 :: P5 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: nil) (P1 :: P4 :: P5 :: P2 :: P5 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P2 :: P5 :: P7 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P2 :: P5 :: P7 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P5 :: nil) (P2 :: P5 :: P7 :: nil) (P5 :: nil) 2 2 1 HP1P4P5Mtmp HP2P5P7Mtmp HP5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P4P5P7M4. 

assert(HP1P2P4P7m2 : rk(P1 :: P2 :: P4 :: P7 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P7 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P7m1. 

assert(HP1P2P4P7m3 : rk(P1 :: P2 :: P4 :: P7 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P7 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P7m2. 

assert(HP1P2P4P7M3 : rk(P1 :: P2 :: P4 :: P7 :: nil) <= 3).
{
	assert(HP1P2P4P5P7Mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P4P5P7eq HP1P2P4P5P7M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P7 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P2 :: P4 :: P7 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: nil) 3 3 HP1P2P4P5P7Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P7M4. 

assert(HP1P4P5P7P12m2 : rk(P1 :: P4 :: P5 :: P7 :: P12 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P7 :: P12 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P7P12m1. 

assert(HP1P4P5P7P12M3 : rk(P1 :: P4 :: P5 :: P7 :: P12 :: nil) <= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP4P7P12Mtmp : rk(P4 :: P7 :: P12 :: nil) <= 2) by (solve_hyps_max HP4P7P12eq HP4P7P12M2).
	assert(HP4mtmp : rk(P4 :: nil) >= 1) by (solve_hyps_min HP4eq HP4m1).
	assert(Hincl : incl (P4 :: nil) (list_inter (P1 :: P4 :: P5 :: nil) (P4 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P7 :: P12 :: nil) (P1 :: P4 :: P5 :: P4 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P4 :: P7 :: P12 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P4 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P5 :: nil) (P4 :: P7 :: P12 :: nil) (P4 :: nil) 2 2 1 HP1P4P5Mtmp HP4P7P12Mtmp HP4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P7P12M4. 

assert(HP1P4P5P7P12m3 : rk(P1 :: P4 :: P5 :: P7 :: P12 :: nil) >= 3).
{
	assert(HP1P4P7mtmp : rk(P1 :: P4 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P4P7eq HP1P4P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P7 :: nil) (P1 :: P4 :: P5 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P7 :: nil) (P1 :: P4 :: P5 :: P7 :: P12 :: nil) 3 3 HP1P4P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P7P12m2. 

assert(HP1P2P4P5P7P12m2 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P12m1. 

assert(HP1P2P4P5P7P12m3 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P12m2. 

assert(HP1P2P4P5P7P12M3 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) <= 3).
{
	assert(HP1P2P4P7Mtmp : rk(P1 :: P2 :: P4 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P4P7eq HP1P2P4P7M3).
	assert(HP1P4P5P7P12Mtmp : rk(P1 :: P4 :: P5 :: P7 :: P12 :: nil) <= 3) by (solve_hyps_max HP1P4P5P7P12eq HP1P4P5P7P12M3).
	assert(HP1P4P7mtmp : rk(P1 :: P4 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P4P7eq HP1P4P7m3).
	assert(Hincl : incl (P1 :: P4 :: P7 :: nil) (list_inter (P1 :: P2 :: P4 :: P7 :: nil) (P1 :: P4 :: P5 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) (P1 :: P2 :: P4 :: P7 :: P1 :: P4 :: P5 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P4 :: P7 :: P1 :: P4 :: P5 :: P7 :: P12 :: nil) ((P1 :: P2 :: P4 :: P7 :: nil) ++ (P1 :: P4 :: P5 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P4 :: P7 :: nil) (P1 :: P4 :: P5 :: P7 :: P12 :: nil) (P1 :: P4 :: P7 :: nil) 3 3 3 HP1P2P4P7Mtmp HP1P4P5P7P12Mtmp HP1P4P7mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P7P12M3. try clear HP1P4P5P7P12m3. try clear HP1P4P7M3. try clear HP1P4P7m3. try clear HP1P2P4P5P7P12M4. 

assert(HP1P5P8m2 : rk(P1 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P8 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P8m1. 

assert(HP1P5P8m3 : rk(P1 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P2P4P5P7P12Mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) <= 3) by (solve_hyps_max HP1P2P4P5P7P12eq HP1P2P4P5P7P12M3).
	assert(HP1P2P4P5P7P8P12mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P4P5P7P8P12eq HP1P2P4P5P7P8P12m4).
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hincl : incl (P1 :: P5 :: nil) (list_inter (P1 :: P5 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) (P1 :: P5 :: P8 :: P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P5 :: P8 :: P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) ((P1 :: P5 :: P8 :: nil) ++ (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P7P8P12mtmp;try rewrite HT2 in HP1P2P4P5P7P8P12mtmp.
	assert(HT := rule_2 (P1 :: P5 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) (P1 :: P5 :: nil) 4 2 3 HP1P2P4P5P7P8P12mtmp HP1P5mtmp HP1P2P4P5P7P12Mtmp Hincl);apply HT.
}
try clear HP1P5P8m2. 

assert(HP1P4P5P8m2 : rk(P1 :: P4 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P8 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P8m1. 

assert(HP1P4P5P8M3 : rk(P1 :: P4 :: P5 :: P8 :: nil) <= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P4 :: P5 :: nil) (P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P8 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P5 :: nil) (P8 :: nil) (nil) 2 1 0 HP1P4P5Mtmp HP8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P8M4. 

assert(HP1P4P5P8m3 : rk(P1 :: P4 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P8m2. 

assert(HP1P2P5P8m2 : rk(P1 :: P2 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P8m1. 

assert(HP1P2P5P8m3 : rk(P1 :: P2 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P8 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P8m2. 

assert(HP1P2P5P8m4 : rk(P1 :: P2 :: P5 :: P8 :: nil) >= 4).
{
	assert(HP1P4P5P8Mtmp : rk(P1 :: P4 :: P5 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P4P5P8eq HP1P4P5P8M3).
	assert(HP1P2P4P5P8mtmp : rk(P1 :: P2 :: P4 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P5P8eq HP1P2P4P5P8m4).
	assert(HP1P5P8mtmp : rk(P1 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P5P8eq HP1P5P8m3).
	assert(Hincl : incl (P1 :: P5 :: P8 :: nil) (list_inter (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P8 :: nil) (P1 :: P2 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil) ((P1 :: P2 :: P5 :: P8 :: nil) ++ (P1 :: P4 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P8mtmp;try rewrite HT2 in HP1P2P4P5P8mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil) (P1 :: P5 :: P8 :: nil) 4 3 3 HP1P2P4P5P8mtmp HP1P5P8mtmp HP1P4P5P8Mtmp Hincl);apply HT.
}
try clear HP1P2P5P8m3. 

assert(HP1P2P3P5P8P9m2 : rk(P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P8P9m1. 

assert(HP1P2P3P5P8P9m3 : rk(P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P8P9m2. 

assert(HP1P2P3P5P8P9m4 : rk(P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) >= 4).
{
	assert(HP1P2P5P8mtmp : rk(P1 :: P2 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P5P8eq HP1P2P5P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) 4 4 HP1P2P5P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P8P9m3. 

assert(HP1P2P3P4P5P8m2 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P8m1. 

assert(HP1P2P3P4P5P8m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P8m2. 

assert(HP1P2P3P4P5P8m4 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P5P8m2 : rk(P1 :: P2 :: P3 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P8m1. 

assert(HP1P2P3P5P8m3 : rk(P1 :: P2 :: P3 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P8m2. 

assert(HP1P2P3P5P8m4 : rk(P1 :: P2 :: P3 :: P5 :: P8 :: nil) >= 4).
{
	assert(HP1P4P5P8Mtmp : rk(P1 :: P4 :: P5 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P4P5P8eq HP1P4P5P8M3).
	assert(HP1P2P3P4P5P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P8eq HP1P2P3P4P5P8m4).
	assert(HP1P5P8mtmp : rk(P1 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P5P8eq HP1P5P8m3).
	assert(Hincl : incl (P1 :: P5 :: P8 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil) ((P1 :: P2 :: P3 :: P5 :: P8 :: nil) ++ (P1 :: P4 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P8mtmp;try rewrite HT2 in HP1P2P3P4P5P8mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil) (P1 :: P5 :: P8 :: nil) 4 3 3 HP1P2P3P4P5P8mtmp HP1P5P8mtmp HP1P4P5P8Mtmp Hincl);apply HT.
}


assert(HP1P5P8P9M3 : rk(P1 :: P5 :: P8 :: P9 :: nil) <= 3).
{
	assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M1).
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P8 :: P9 :: nil) (P5 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P1 :: P8 :: P9 :: nil) ((P5 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: nil) (P1 :: P8 :: P9 :: nil) (nil) 1 2 0 HP5Mtmp HP1P8P9Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P5P8P9M4. 

assert(HP1P5P8P9m2 : rk(P1 :: P5 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P8 :: P9 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P8P9m1. 

assert(HP1P5P8P9m3 : rk(P1 :: P5 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P2P3P5P8Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P8 :: nil) <= 4) by (solve_hyps_max HP1P2P3P5P8eq HP1P2P3P5P8M4).
	assert(HP1P2P3P5P8P9mtmp : rk(P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P8P9eq HP1P2P3P5P8P9m4).
	assert(HP1P5P8mtmp : rk(P1 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P5P8eq HP1P5P8m3).
	assert(Hincl : incl (P1 :: P5 :: P8 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P8 :: nil) (P1 :: P5 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: P1 :: P5 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P8 :: P1 :: P5 :: P8 :: P9 :: nil) ((P1 :: P2 :: P3 :: P5 :: P8 :: nil) ++ (P1 :: P5 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P8P9mtmp;try rewrite HT2 in HP1P2P3P5P8P9mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: P8 :: nil) (P1 :: P5 :: P8 :: P9 :: nil) (P1 :: P5 :: P8 :: nil) 4 3 4 HP1P2P3P5P8P9mtmp HP1P5P8mtmp HP1P2P3P5P8Mtmp Hincl); apply HT.
}
try clear HP1P5P8P9m2. 

assert(HP1P9m2 : rk(P1 :: P9 :: nil) >= 2).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP1P2P9mtmp : rk(P1 :: P2 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P2P9eq HP1P2P9m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P9 :: nil) (P2 :: P1 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P9 :: nil) ((P2 :: nil) ++ (P1 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P9mtmp;try rewrite HT2 in HP1P2P9mtmp.
	assert(HT := rule_4 (P2 :: nil) (P1 :: P9 :: nil) (nil) 3 0 1 HP1P2P9mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}
try clear HP1P9m1. 

assert(HP1P5P9m2 : rk(P1 :: P5 :: P9 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P9 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P9m1. 

assert(HP1P5P9m3 : rk(P1 :: P5 :: P9 :: nil) >= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P5P8P9mtmp : rk(P1 :: P5 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P5P8P9eq HP1P5P8P9m3).
	assert(HP1P9mtmp : rk(P1 :: P9 :: nil) >= 2) by (solve_hyps_min HP1P9eq HP1P9m2).
	assert(Hincl : incl (P1 :: P9 :: nil) (list_inter (P1 :: P5 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P8 :: P9 :: nil) (P1 :: P5 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P5 :: P9 :: P1 :: P8 :: P9 :: nil) ((P1 :: P5 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P5P8P9mtmp;try rewrite HT2 in HP1P5P8P9mtmp.
	assert(HT := rule_2 (P1 :: P5 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P1 :: P9 :: nil) 3 2 2 HP1P5P8P9mtmp HP1P9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP1P5P9m2. try clear HP1P5P8P9M3. try clear HP1P5P8P9m3. 

assert(HP1P5P9P14M3 : rk(P1 :: P5 :: P9 :: P14 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P9 :: P14 :: nil) (P1 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P5 :: P9 :: P14 :: nil) ((P1 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P5 :: P9 :: P14 :: nil) (nil) 1 2 0 HP1Mtmp HP5P9P14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P5P9P14M4. 

assert(HP1P5P9P14m2 : rk(P1 :: P5 :: P9 :: P14 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P9 :: P14 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P9P14m1. 

assert(HP1P5P9P14m3 : rk(P1 :: P5 :: P9 :: P14 :: nil) >= 3).
{
	assert(HP1P5P9mtmp : rk(P1 :: P5 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P5P9eq HP1P5P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: P9 :: nil) (P1 :: P5 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: P9 :: nil) (P1 :: P5 :: P9 :: P14 :: nil) 3 3 HP1P5P9mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P9M3. try clear HP1P5P9m3. try clear HP1P5P9P14m2. 

assert(HP1P14m2 : rk(P1 :: P14 :: nil) >= 2).
{
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(HP1P5P9P14mtmp : rk(P1 :: P5 :: P9 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P5P9P14eq HP1P5P9P14m3).
	assert(HP14mtmp : rk(P14 :: nil) >= 1) by (solve_hyps_min HP14eq HP14m1).
	assert(Hincl : incl (P14 :: nil) (list_inter (P1 :: P14 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P9 :: P14 :: nil) (P1 :: P14 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P14 :: P5 :: P9 :: P14 :: nil) ((P1 :: P14 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P5P9P14mtmp;try rewrite HT2 in HP1P5P9P14mtmp.
	assert(HT := rule_2 (P1 :: P14 :: nil) (P5 :: P9 :: P14 :: nil) (P14 :: nil) 3 1 2 HP1P5P9P14mtmp HP14mtmp HP5P9P14Mtmp Hincl);apply HT.
}
try clear HP1P14m1. try clear HP1P5P9P14M3. try clear HP1P5P9P14m3. 

assert(HP1P4P8P9M3 : rk(P1 :: P4 :: P8 :: P9 :: nil) <= 3).
{
	assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M1).
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P9 :: nil) (P4 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P1 :: P8 :: P9 :: nil) ((P4 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: nil) (P1 :: P8 :: P9 :: nil) (nil) 1 2 0 HP4Mtmp HP1P8P9Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P8P9M4. 

assert(HP1P4P8P9m2 : rk(P1 :: P4 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P9 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P9m1. 

assert(HP1P4P8P9m3 : rk(P1 :: P4 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P9 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P9m2. 

assert(HP1P4P9m2 : rk(P1 :: P4 :: P9 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P9 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P9m1. 

assert(HP1P4P9m3 : rk(P1 :: P4 :: P9 :: nil) >= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P4P8P9mtmp : rk(P1 :: P4 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P4P8P9eq HP1P4P8P9m3).
	assert(HP1P9mtmp : rk(P1 :: P9 :: nil) >= 2) by (solve_hyps_min HP1P9eq HP1P9m2).
	assert(Hincl : incl (P1 :: P9 :: nil) (list_inter (P1 :: P4 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P9 :: nil) (P1 :: P4 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P9 :: P1 :: P8 :: P9 :: nil) ((P1 :: P4 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P9mtmp;try rewrite HT2 in HP1P4P8P9mtmp.
	assert(HT := rule_2 (P1 :: P4 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P1 :: P9 :: nil) 3 2 2 HP1P4P8P9mtmp HP1P9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP1P4P9m2. try clear HP1P4P8P9M3. try clear HP1P4P8P9m3. 

assert(HP1P4P5P9P14m2 : rk(P1 :: P4 :: P5 :: P9 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P9 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P9P14m1. 

assert(HP1P4P5P9P14M3 : rk(P1 :: P4 :: P5 :: P9 :: P14 :: nil) <= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m1).
	assert(Hincl : incl (P5 :: nil) (list_inter (P1 :: P4 :: P5 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P9 :: P14 :: nil) (P1 :: P4 :: P5 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P5 :: P9 :: P14 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P5 :: nil) (P5 :: P9 :: P14 :: nil) (P5 :: nil) 2 2 1 HP1P4P5Mtmp HP5P9P14Mtmp HP5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P9P14M4. 

assert(HP1P4P5P9P14m3 : rk(P1 :: P4 :: P5 :: P9 :: P14 :: nil) >= 3).
{
	assert(HP1P4P9mtmp : rk(P1 :: P4 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P4P9eq HP1P4P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P9 :: nil) (P1 :: P4 :: P5 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P9 :: nil) (P1 :: P4 :: P5 :: P9 :: P14 :: nil) 3 3 HP1P4P9mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P9M3. try clear HP1P4P9m3. try clear HP1P4P5P9P14m2. 

assert(HP1P4P5P8P9P14m2 : rk(P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P8P9P14m1. 

assert(HP1P4P5P8P9P14m3 : rk(P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P8P9P14m2. 

assert(HP1P4P5P8P9P14M3 : rk(P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil) <= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P4P5P9P14Mtmp : rk(P1 :: P4 :: P5 :: P9 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P5P9P14eq HP1P4P5P9P14M3).
	assert(HP1P9mtmp : rk(P1 :: P9 :: nil) >= 2) by (solve_hyps_min HP1P9eq HP1P9m2).
	assert(Hincl : incl (P1 :: P9 :: nil) (list_inter (P1 :: P8 :: P9 :: nil) (P1 :: P4 :: P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil) (P1 :: P8 :: P9 :: P1 :: P4 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P9 :: P1 :: P4 :: P5 :: P9 :: P14 :: nil) ((P1 :: P8 :: P9 :: nil) ++ (P1 :: P4 :: P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P8 :: P9 :: nil) (P1 :: P4 :: P5 :: P9 :: P14 :: nil) (P1 :: P9 :: nil) 2 3 2 HP1P8P9Mtmp HP1P4P5P9P14Mtmp HP1P9mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P9P14M3. try clear HP1P4P5P9P14m3. try clear HP1P4P5P8P9P14M4. 

assert(HP1P4P8P14m2 : rk(P1 :: P4 :: P8 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P14m1. 

assert(HP1P4P8P14m3 : rk(P1 :: P4 :: P8 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P14 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P14m2. 

assert(HP1P4P8P14M3 : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3).
{
	assert(HP1P4P5P8P9P14Mtmp : rk(P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P5P8P9P14eq HP1P4P5P8P9P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: P14 :: nil) 3 3 HP1P4P5P8P9P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P14M4. try clear HP1P4P5P8P9P14M3. try clear HP1P4P5P8P9P14m3. 

assert(HP1P12P13P14m2 : rk(P1 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P12mtmp : rk(P1 :: P12 :: nil) >= 2) by (solve_hyps_min HP1P12eq HP1P12m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P12 :: nil) (P1 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P12 :: nil) (P1 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P12mtmp Hcomp Hincl);apply HT.
}
try clear HP1P12M2. try clear HP1P12m2. try clear HP1P12P13P14m1. 

assert(HP1P12P13P14M3 : rk(P1 :: P12 :: P13 :: P14 :: nil) <= 3).
{
	assert(HP1P12P13Mtmp : rk(P1 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P12P13eq HP1P12P13M2).
	assert(HP14Mtmp : rk(P14 :: nil) <= 1) by (solve_hyps_max HP14eq HP14M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P12 :: P13 :: nil) (P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P12 :: P13 :: P14 :: nil) (P1 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P12 :: P13 :: P14 :: nil) ((P1 :: P12 :: P13 :: nil) ++ (P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P12 :: P13 :: nil) (P14 :: nil) (nil) 2 1 0 HP1P12P13Mtmp HP14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P12P13P14M4. 

assert(HP1P12P13P14m3 : rk(P1 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP1P4P8P12P13P14mtmp : rk(P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P8P12P13P14eq HP1P4P8P12P13P14m4).
	assert(HP1P14mtmp : rk(P1 :: P14 :: nil) >= 2) by (solve_hyps_min HP1P14eq HP1P14m2).
	assert(Hincl : incl (P1 :: P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P1 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P1 :: P12 :: P13 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P1 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P12P13P14mtmp;try rewrite HT2 in HP1P4P8P12P13P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P12 :: P13 :: P14 :: nil) (P1 :: P14 :: nil) 4 2 3 HP1P4P8P12P13P14mtmp HP1P14mtmp HP1P4P8P14Mtmp Hincl); apply HT.
}
try clear HP1P12P13P14m2. 

assert(HP2P4P8m3 : rk(P2 :: P4 :: P8 :: nil) >= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P4 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P4 :: P8 :: nil) ((P1 :: nil) ++ (P2 :: P4 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8mtmp;try rewrite HT2 in HP1P2P4P8mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P4 :: P8 :: nil) (nil) 4 0 1 HP1P2P4P8mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}
try clear HP2P4P8m1. 

assert(HP2P4m2 : rk(P2 :: P4 :: nil) >= 2).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P4 :: nil) ((P1 :: nil) ++ (P2 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4mtmp;try rewrite HT2 in HP1P2P4mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P4 :: nil) (nil) 3 0 1 HP1P2P4mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}
try clear HP2P4m1. 

assert(HP2P4P6P8P10m2 : rk(P2 :: P4 :: P6 :: P8 :: P10 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P6P8P10m1. 

assert(HP2P4P6P8P10M3 : rk(P2 :: P4 :: P6 :: P8 :: P10 :: nil) <= 3).
{
	assert(HP2P4P6Mtmp : rk(P2 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP2P4P6eq HP2P4P6M2).
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP2mtmp : rk(P2 :: nil) >= 1) by (solve_hyps_min HP2eq HP2m1).
	assert(Hincl : incl (P2 :: nil) (list_inter (P2 :: P4 :: P6 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P6 :: P8 :: P10 :: nil) (P2 :: P4 :: P6 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P6 :: P2 :: P8 :: P10 :: nil) ((P2 :: P4 :: P6 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P4 :: P6 :: nil) (P2 :: P8 :: P10 :: nil) (P2 :: nil) 2 2 1 HP2P4P6Mtmp HP2P8P10Mtmp HP2mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P4P6P8P10M4. 

assert(HP2P4P6P8P10m3 : rk(P2 :: P4 :: P6 :: P8 :: P10 :: nil) >= 3).
{
	assert(HP2P4P8mtmp : rk(P2 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P4P8eq HP2P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: nil) 3 3 HP2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P6P8P10m2. 

assert(HP1P2P3P4P5P6P8m2 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6P8m1. 

assert(HP1P2P3P4P5P6P8m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6P8m2. 

assert(HP1P2P3P4P5P6P8m4 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P8P9m2 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8P9m1. 

assert(HP1P2P3P4P8P9m3 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8P9m2. 

assert(HP1P2P3P4P8P9m4 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8P9m3. 

assert(HP1P2P3P8P12P13m2 : rk(P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P12P13m1. 

assert(HP1P2P3P8P12P13M3 : rk(P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) <= 3).
{
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P8 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) (P8 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P8 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P8 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (nil) 1 2 0 HP8Mtmp HP1P2P3P12P13Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P8P12P13M4. 

assert(HP1P2P3P8P12P13m3 : rk(P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P8mtmp : rk(P1 :: P2 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P8eq HP1P2P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) 3 3 HP1P2P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P12P13m2. 

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
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(HP1P2P3P8P12P13mtmp : rk(P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P3P8P12P13eq HP1P2P3P8P12P13m3).
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hincl : incl (P1 :: P3 :: nil) (list_inter (P1 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) (P1 :: P3 :: P8 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P8 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P1 :: P3 :: P8 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P12P13mtmp;try rewrite HT2 in HP1P2P3P8P12P13mtmp.
	assert(HT := rule_2 (P1 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (P1 :: P3 :: nil) 3 2 2 HP1P2P3P8P12P13mtmp HP1P3mtmp HP1P2P3P12P13Mtmp Hincl);apply HT.
}
try clear HP1P3P8m2. 

assert(HP1P2P3P8P9m2 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9m1. 

assert(HP1P2P3P8P9M3 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: nil) <= 3).
{
	assert(HP1P2P3Mtmp : rk(P1 :: P2 :: P3 :: nil) <= 2) by (solve_hyps_max HP1P2P3eq HP1P2P3M2).
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1mtmp : rk(P1 :: nil) >= 1) by (solve_hyps_min HP1eq HP1m1).
	assert(Hincl : incl (P1 :: nil) (list_inter (P1 :: P2 :: P3 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: nil) (P1 :: P2 :: P3 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P1 :: P8 :: P9 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: nil) (P1 :: P8 :: P9 :: nil) (P1 :: nil) 2 2 1 HP1P2P3Mtmp HP1P8P9Mtmp HP1mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P8P9M4. 

assert(HP1P2P3P8P9m3 : rk(P1 :: P2 :: P3 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P2P8mtmp : rk(P1 :: P2 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P8eq HP1P2P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: nil) 3 3 HP1P2P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P8P9m2. 

assert(HP1P2P3P4P8m2 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8m1. 

assert(HP1P2P3P4P8m3 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8m2. 

assert(HP1P2P3P4P12P13m2 : rk(P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P12P13m1. 

assert(HP1P2P3P4P12P13M3 : rk(P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) <= 3).
{
	assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M1).
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) (P4 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P4 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (nil) 1 2 0 HP4Mtmp HP1P2P3P12P13Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4P12P13M4. 

assert(HP1P2P3P4P12P13m3 : rk(P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P12P13m2. 

assert(HP1P3P4m2 : rk(P1 :: P3 :: P4 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P4m1. 

assert(HP1P3P4m3 : rk(P1 :: P3 :: P4 :: nil) >= 3).
{
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(HP1P2P3P4P12P13mtmp : rk(P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P12P13eq HP1P2P3P4P12P13m3).
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hincl : incl (P1 :: P3 :: nil) (list_inter (P1 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) (P1 :: P3 :: P4 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P4 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P1 :: P3 :: P4 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P12P13mtmp;try rewrite HT2 in HP1P2P3P4P12P13mtmp.
	assert(HT := rule_2 (P1 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (P1 :: P3 :: nil) 3 2 2 HP1P2P3P4P12P13mtmp HP1P3mtmp HP1P2P3P12P13Mtmp Hincl);apply HT.
}
try clear HP1P3P4m2. 

assert(HP1P2P3P4m2 : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4m1. 

assert(HP1P2P3P4M3 : rk(P1 :: P2 :: P3 :: P4 :: nil) <= 3).
{
	assert(HP1P2P3Mtmp : rk(P1 :: P2 :: P3 :: nil) <= 2) by (solve_hyps_max HP1P2P3eq HP1P2P3M2).
	assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: P3 :: nil) (P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P4 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: nil) (P4 :: nil) (nil) 2 1 0 HP1P2P3Mtmp HP4Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4M4. 

assert(HP1P2P3P4m3 : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4m2. 

assert(HP1P3P4P8m2 : rk(P1 :: P3 :: P4 :: P8 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: P8 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P4P8m1. 

assert(HP1P3P4P8m3 : rk(P1 :: P3 :: P4 :: P8 :: nil) >= 3).
{
	assert(HP1P2P3P4Mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4eq HP1P2P3P4M3).
	assert(HP1P2P3P4P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P8eq HP1P2P3P4P8m3).
	assert(HP1P3P4mtmp : rk(P1 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P3P4eq HP1P3P4m3).
	assert(Hincl : incl (P1 :: P3 :: P4 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P3 :: P4 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P1 :: P3 :: P4 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P1 :: P3 :: P4 :: P8 :: nil) ((P1 :: P2 :: P3 :: P4 :: nil) ++ (P1 :: P3 :: P4 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P8mtmp;try rewrite HT2 in HP1P2P3P4P8mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P3 :: P4 :: P8 :: nil) (P1 :: P3 :: P4 :: nil) 3 3 3 HP1P2P3P4P8mtmp HP1P3P4mtmp HP1P2P3P4Mtmp Hincl); apply HT.
}
try clear HP1P3P4P8m2. 

assert(HP1P3P4P8m4 : rk(P1 :: P3 :: P4 :: P8 :: nil) >= 4).
{
	assert(HP1P2P3P8P9Mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: nil) <= 3) by (solve_hyps_max HP1P2P3P8P9eq HP1P2P3P8P9M3).
	assert(HP1P2P3P4P8P9mtmp : rk(P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P8P9eq HP1P2P3P4P8P9m4).
	assert(HP1P3P8mtmp : rk(P1 :: P3 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P3P8eq HP1P3P8m3).
	assert(Hincl : incl (P1 :: P3 :: P8 :: nil) (list_inter (P1 :: P3 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P8 :: P9 :: nil) (P1 :: P3 :: P4 :: P8 :: P1 :: P2 :: P3 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P4 :: P8 :: P1 :: P2 :: P3 :: P8 :: P9 :: nil) ((P1 :: P3 :: P4 :: P8 :: nil) ++ (P1 :: P2 :: P3 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P8P9mtmp;try rewrite HT2 in HP1P2P3P4P8P9mtmp.
	assert(HT := rule_2 (P1 :: P3 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: nil) (P1 :: P3 :: P8 :: nil) 4 3 3 HP1P2P3P4P8P9mtmp HP1P3P8mtmp HP1P2P3P8P9Mtmp Hincl);apply HT.
}
try clear HP1P3P4P8m3. try clear HP1P3P8M3. try clear HP1P3P8m3. try clear HP1P2P3P4P8P9M4. try clear HP1P2P3P4P8P9m4. 

assert(HP1P2P3P4P8m4 : rk(P1 :: P2 :: P3 :: P4 :: P8 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P8m3. 

assert(HP1P3P4P5P6P8m2 : rk(P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P4P5P6P8m1. 

assert(HP1P3P4P5P6P8m3 : rk(P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P2P3P4Mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4eq HP1P2P3P4M3).
	assert(HP1P2P3P4P5P6P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P5P6P8eq HP1P2P3P4P5P6P8m3).
	assert(HP1P3P4mtmp : rk(P1 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P3P4eq HP1P3P4m3).
	assert(Hincl : incl (P1 :: P3 :: P4 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) ((P1 :: P2 :: P3 :: P4 :: nil) ++ (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P8mtmp;try rewrite HT2 in HP1P2P3P4P5P6P8mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P1 :: P3 :: P4 :: nil) 3 3 3 HP1P2P3P4P5P6P8mtmp HP1P3P4mtmp HP1P2P3P4Mtmp Hincl); apply HT.
}
try clear HP1P3P4P5P6P8m2. 

assert(HP1P3P4P5P6P8m4 : rk(P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP1P2P3P4P8Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P8 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P8eq HP1P2P3P4P8M4).
	assert(HP1P2P3P4P5P6P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P8eq HP1P2P3P4P5P6P8m4).
	assert(HP1P3P4P8mtmp : rk(P1 :: P3 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P3P4P8eq HP1P3P4P8m4).
	assert(Hincl : incl (P1 :: P3 :: P4 :: P8 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P8 :: nil) (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P8 :: P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) ((P1 :: P2 :: P3 :: P4 :: P8 :: nil) ++ (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P8mtmp;try rewrite HT2 in HP1P2P3P4P5P6P8mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: P8 :: nil) (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P1 :: P3 :: P4 :: P8 :: nil) 4 4 4 HP1P2P3P4P5P6P8mtmp HP1P3P4P8mtmp HP1P2P3P4P8Mtmp Hincl); apply HT.
}
try clear HP1P2P3P4P5P6P8M4. try clear HP1P2P3P4P5P6P8m4. 

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

assert(HP4P5P8m2 : rk(P4 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P8m1. 

assert(HP4P5P8m3 : rk(P4 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P2P4P5P7P12Mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) <= 3) by (solve_hyps_max HP1P2P4P5P7P12eq HP1P2P4P5P7P12M3).
	assert(HP1P2P4P5P7P8P12mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P4P5P7P8P12eq HP1P2P4P5P7P8P12m4).
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P4 :: P5 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) (P4 :: P5 :: P8 :: P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P8 :: P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) ((P4 :: P5 :: P8 :: nil) ++ (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P7P8P12mtmp;try rewrite HT2 in HP1P2P4P5P7P8P12mtmp.
	assert(HT := rule_2 (P4 :: P5 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) (P4 :: P5 :: nil) 4 2 3 HP1P2P4P5P7P8P12mtmp HP4P5mtmp HP1P2P4P5P7P12Mtmp Hincl);apply HT.
}
try clear HP4P5P8m2. 

assert(HP3P4m2 : rk(P3 :: P4 :: nil) >= 2).
{
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(HP1P2P3P4P12P13mtmp : rk(P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P12P13eq HP1P2P3P4P12P13m3).
	assert(HP3mtmp : rk(P3 :: nil) >= 1) by (solve_hyps_min HP3eq HP3m1).
	assert(Hincl : incl (P3 :: nil) (list_inter (P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P12 :: P13 :: nil) (P3 :: P4 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P4 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P3 :: P4 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P12P13mtmp;try rewrite HT2 in HP1P2P3P4P12P13mtmp.
	assert(HT := rule_2 (P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (P3 :: nil) 3 1 2 HP1P2P3P4P12P13mtmp HP3mtmp HP1P2P3P12P13Mtmp Hincl);apply HT.
}
try clear HP3P4m1. try clear HP1P2P3P4P12P13M3. try clear HP1P2P3P4P12P13m3. 

assert(HP3P4P5P6P8m2 : rk(P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P2P3P4Mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4eq HP1P2P3P4M3).
	assert(HP1P2P3P4P5P6P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P5P6P8eq HP1P2P3P4P5P6P8m3).
	assert(HP3P4mtmp : rk(P3 :: P4 :: nil) >= 2) by (solve_hyps_min HP3P4eq HP3P4m2).
	assert(Hincl : incl (P3 :: P4 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: nil) (P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) ((P1 :: P2 :: P3 :: P4 :: nil) ++ (P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P8mtmp;try rewrite HT2 in HP1P2P3P4P5P6P8mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: nil) (P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P3 :: P4 :: nil) 3 2 3 HP1P2P3P4P5P6P8mtmp HP3P4mtmp HP1P2P3P4Mtmp Hincl); apply HT.
}
try clear HP3P4P5P6P8m1. try clear HP3P4M2. try clear HP3P4m2. try clear HP1P2P3P4P5P6P8M4. try clear HP1P2P3P4P5P6P8m3. 

assert(HP3P4P5P6P8m3 : rk(P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP1P3P4P5P6P8mtmp : rk(P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P3P4P5P6P8eq HP1P3P4P5P6P8m3).
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P1 :: P4 :: P5 :: nil) (P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P1 :: P4 :: P5 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P4P5P6P8mtmp;try rewrite HT2 in HP1P3P4P5P6P8mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P5 :: nil) (P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: nil) 3 2 2 HP1P3P4P5P6P8mtmp HP4P5mtmp HP1P4P5Mtmp Hincl); apply HT.
}
try clear HP3P4P5P6P8m2. try clear HP1P3P4P5P6P8M4. try clear HP1P3P4P5P6P8m3. 

assert(HP3P4P5P6P8m4 : rk(P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP1P4P5P8Mtmp : rk(P1 :: P4 :: P5 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P4P5P8eq HP1P4P5P8M3).
	assert(HP1P3P4P5P6P8mtmp : rk(P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P3P4P5P6P8eq HP1P3P4P5P6P8m4).
	assert(HP4P5P8mtmp : rk(P4 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P8eq HP4P5P8m3).
	assert(Hincl : incl (P4 :: P5 :: P8 :: nil) (list_inter (P1 :: P4 :: P5 :: P8 :: nil) (P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P8 :: P3 :: P4 :: P5 :: P6 :: P8 :: nil) ((P1 :: P4 :: P5 :: P8 :: nil) ++ (P3 :: P4 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P4P5P6P8mtmp;try rewrite HT2 in HP1P3P4P5P6P8mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P5 :: P8 :: nil) (P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: P8 :: nil) 4 3 3 HP1P3P4P5P6P8mtmp HP4P5P8mtmp HP1P4P5P8Mtmp Hincl); apply HT.
}
try clear HP3P4P5P6P8m3. try clear HP1P3P4P5P6P8M4. try clear HP1P3P4P5P6P8m4. 

assert(HP1P2P4P6P7P8P12m2 : rk(P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6P7P8P12m1. 

assert(HP1P2P4P6P7P8P12m3 : rk(P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6P7P8P12m2. 

assert(HP1P2P4P6P7P8P12m4 : rk(P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6P7P8P12m3. 

assert(HP2P4P5P7M3 : rk(P2 :: P4 :: P5 :: P7 :: nil) <= 3).
{
	assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M1).
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: nil) (P2 :: P5 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P5 :: P7 :: nil) (P4 :: P2 :: P5 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P2 :: P5 :: P7 :: nil) ((P4 :: nil) ++ (P2 :: P5 :: P7 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: nil) (P2 :: P5 :: P7 :: nil) (nil) 1 2 0 HP4Mtmp HP2P5P7Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P4P5P7M4. 

assert(HP2P4P5P7m2 : rk(P2 :: P4 :: P5 :: P7 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P5 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P5 :: P7 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P5P7m1. 

assert(HP2P4P5P7m3 : rk(P2 :: P4 :: P5 :: P7 :: nil) >= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP1P2P4P5P7mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P4P5P7eq HP1P2P4P5P7m3).
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P1 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: nil) (P1 :: P4 :: P5 :: P2 :: P4 :: P5 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P2 :: P4 :: P5 :: P7 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P2 :: P4 :: P5 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P7mtmp;try rewrite HT2 in HP1P2P4P5P7mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P7 :: nil) (P4 :: P5 :: nil) 3 2 2 HP1P2P4P5P7mtmp HP4P5mtmp HP1P4P5Mtmp Hincl); apply HT.
}
try clear HP2P4P5P7m2. try clear HP1P2P4P5P7M3. try clear HP1P2P4P5P7m3. 

assert(HP1P2P3P5P6m2 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6m1. 

assert(HP1P2P3P5P6M3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: nil) <= 3).
{
	assert(HP1P2P3Mtmp : rk(P1 :: P2 :: P3 :: nil) <= 2) by (solve_hyps_max HP1P2P3eq HP1P2P3M2).
	assert(HP3P5P6Mtmp : rk(P3 :: P5 :: P6 :: nil) <= 2) by (solve_hyps_max HP3P5P6eq HP3P5P6M2).
	assert(HP3mtmp : rk(P3 :: nil) >= 1) by (solve_hyps_min HP3eq HP3m1).
	assert(Hincl : incl (P3 :: nil) (list_inter (P1 :: P2 :: P3 :: nil) (P3 :: P5 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P3 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P3 :: P5 :: P6 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P3 :: P5 :: P6 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: nil) (P3 :: P5 :: P6 :: nil) (P3 :: nil) 2 2 1 HP1P2P3Mtmp HP3P5P6Mtmp HP3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P5P6M4. 

assert(HP1P2P3P5P6m3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6m2. 

assert(HP1P2P3P5P12P13m2 : rk(P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P12P13m1. 

assert(HP1P2P3P5P12P13M3 : rk(P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil) <= 3).
{
	assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M1).
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil) (P5 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P5 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (nil) 1 2 0 HP5Mtmp HP1P2P3P12P13Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P5P12P13M4. 

assert(HP1P2P3P5P12P13m3 : rk(P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P12P13m2. 

assert(HP2P3P5m2 : rk(P2 :: P3 :: P5 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P5m1. 

assert(HP2P3P5m3 : rk(P2 :: P3 :: P5 :: nil) >= 3).
{
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(HP1P2P3P5P12P13mtmp : rk(P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P3P5P12P13eq HP1P2P3P5P12P13m3).
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hincl : incl (P2 :: P3 :: nil) (list_inter (P2 :: P3 :: P5 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P12 :: P13 :: nil) (P2 :: P3 :: P5 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P5 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P2 :: P3 :: P5 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P12P13mtmp;try rewrite HT2 in HP1P2P3P5P12P13mtmp.
	assert(HT := rule_2 (P2 :: P3 :: P5 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (P2 :: P3 :: nil) 3 2 2 HP1P2P3P5P12P13mtmp HP2P3mtmp HP1P2P3P12P13Mtmp Hincl);apply HT.
}
try clear HP2P3P5m2. try clear HP1P2P3P5P12P13M3. try clear HP1P2P3P5P12P13m3. 

assert(HP1P2P3P5m2 : rk(P1 :: P2 :: P3 :: P5 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5m1. 

assert(HP1P2P3P5M3 : rk(P1 :: P2 :: P3 :: P5 :: nil) <= 3).
{
	assert(HP1P2P3Mtmp : rk(P1 :: P2 :: P3 :: nil) <= 2) by (solve_hyps_max HP1P2P3eq HP1P2P3M2).
	assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: P3 :: nil) (P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: nil) (P5 :: nil) (nil) 2 1 0 HP1P2P3Mtmp HP5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P5M4. 

assert(HP1P2P3P5m3 : rk(P1 :: P2 :: P3 :: P5 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5m2. 

assert(HP2P3P5P6M3 : rk(P2 :: P3 :: P5 :: P6 :: nil) <= 3).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP3P5P6Mtmp : rk(P3 :: P5 :: P6 :: nil) <= 2) by (solve_hyps_max HP3P5P6eq HP3P5P6M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P3 :: P5 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P6 :: nil) (P2 :: P3 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P5 :: P6 :: nil) ((P2 :: nil) ++ (P3 :: P5 :: P6 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: nil) (P3 :: P5 :: P6 :: nil) (nil) 1 2 0 HP2Mtmp HP3P5P6Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P3P5P6M4. 

assert(HP2P3P5P6m2 : rk(P2 :: P3 :: P5 :: P6 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P6 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P5P6m1. 

assert(HP2P3P5P6m3 : rk(P2 :: P3 :: P5 :: P6 :: nil) >= 3).
{
	assert(HP1P2P3P5Mtmp : rk(P1 :: P2 :: P3 :: P5 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5eq HP1P2P3P5M3).
	assert(HP1P2P3P5P6mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P3P5P6eq HP1P2P3P5P6m3).
	assert(HP2P3P5mtmp : rk(P2 :: P3 :: P5 :: nil) >= 3) by (solve_hyps_min HP2P3P5eq HP2P3P5m3).
	assert(Hincl : incl (P2 :: P3 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: nil) (P2 :: P3 :: P5 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P5 :: P2 :: P3 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P2 :: P3 :: P5 :: P6 :: nil) ((P1 :: P2 :: P3 :: P5 :: nil) ++ (P2 :: P3 :: P5 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6mtmp;try rewrite HT2 in HP1P2P3P5P6mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: nil) (P2 :: P3 :: P5 :: P6 :: nil) (P2 :: P3 :: P5 :: nil) 3 3 3 HP1P2P3P5P6mtmp HP2P3P5mtmp HP1P2P3P5Mtmp Hincl); apply HT.
}
try clear HP2P3P5P6m2. try clear HP1P2P3P5P6M3. try clear HP1P2P3P5P6m3. 

assert(HP2P6m2 : rk(P2 :: P6 :: nil) >= 2).
{
	assert(HP3P5P6Mtmp : rk(P3 :: P5 :: P6 :: nil) <= 2) by (solve_hyps_max HP3P5P6eq HP3P5P6M2).
	assert(HP2P3P5P6mtmp : rk(P2 :: P3 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP2P3P5P6eq HP2P3P5P6m3).
	assert(HP6mtmp : rk(P6 :: nil) >= 1) by (solve_hyps_min HP6eq HP6m1).
	assert(Hincl : incl (P6 :: nil) (list_inter (P2 :: P6 :: nil) (P3 :: P5 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P6 :: nil) (P2 :: P6 :: P3 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P6 :: P3 :: P5 :: P6 :: nil) ((P2 :: P6 :: nil) ++ (P3 :: P5 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P5P6mtmp;try rewrite HT2 in HP2P3P5P6mtmp.
	assert(HT := rule_2 (P2 :: P6 :: nil) (P3 :: P5 :: P6 :: nil) (P6 :: nil) 3 1 2 HP2P3P5P6mtmp HP6mtmp HP3P5P6Mtmp Hincl);apply HT.
}
try clear HP2P6m1. try clear HP2P3P5P6M3. try clear HP2P3P5P6m3. 

assert(HP1P2P6m2 : rk(P1 :: P2 :: P6 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6m1. 

assert(HP1P2P6m3 : rk(P1 :: P2 :: P6 :: nil) >= 3).
{
	assert(HP2P4P6Mtmp : rk(P2 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP2P4P6eq HP2P4P6M2).
	assert(HP1P2P4P6mtmp : rk(P1 :: P2 :: P4 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P4P6eq HP1P2P4P6m3).
	assert(HP2P6mtmp : rk(P2 :: P6 :: nil) >= 2) by (solve_hyps_min HP2P6eq HP2P6m2).
	assert(Hincl : incl (P2 :: P6 :: nil) (list_inter (P1 :: P2 :: P6 :: nil) (P2 :: P4 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P6 :: nil) (P1 :: P2 :: P6 :: P2 :: P4 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P6 :: P2 :: P4 :: P6 :: nil) ((P1 :: P2 :: P6 :: nil) ++ (P2 :: P4 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P6mtmp;try rewrite HT2 in HP1P2P4P6mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P6 :: nil) (P2 :: P4 :: P6 :: nil) (P2 :: P6 :: nil) 3 2 2 HP1P2P4P6mtmp HP2P6mtmp HP2P4P6Mtmp Hincl);apply HT.
}
try clear HP1P2P6m2. 

assert(HP1P2P6P7M3 : rk(P1 :: P2 :: P6 :: P7 :: nil) <= 3).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP1P6P7Mtmp : rk(P1 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P6P7eq HP1P6P7M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P6 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P6 :: P7 :: nil) (P2 :: P1 :: P6 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P6 :: P7 :: nil) ((P2 :: nil) ++ (P1 :: P6 :: P7 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: nil) (P1 :: P6 :: P7 :: nil) (nil) 1 2 0 HP2Mtmp HP1P6P7Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P6P7M4. 

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
	assert(HP1P2P6mtmp : rk(P1 :: P2 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P6eq HP1P2P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P7 :: nil) 3 3 HP1P2P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7m2. 

assert(HP2P7m2 : rk(P2 :: P7 :: nil) >= 2).
{
	assert(HP1P6P7Mtmp : rk(P1 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P6P7eq HP1P6P7M2).
	assert(HP1P2P6P7mtmp : rk(P1 :: P2 :: P6 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P6P7eq HP1P2P6P7m3).
	assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m1).
	assert(Hincl : incl (P7 :: nil) (list_inter (P2 :: P7 :: nil) (P1 :: P6 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P6 :: P7 :: nil) (P2 :: P7 :: P1 :: P6 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P7 :: P1 :: P6 :: P7 :: nil) ((P2 :: P7 :: nil) ++ (P1 :: P6 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P6P7mtmp;try rewrite HT2 in HP1P2P6P7mtmp.
	assert(HT := rule_2 (P2 :: P7 :: nil) (P1 :: P6 :: P7 :: nil) (P7 :: nil) 3 1 2 HP1P2P6P7mtmp HP7mtmp HP1P6P7Mtmp Hincl);apply HT.
}
try clear HP2P7m1. try clear HP1P2P6P7M3. try clear HP1P2P6P7m3. 

assert(HP2P4P7m2 : rk(P2 :: P4 :: P7 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P7 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P7m1. 

assert(HP2P4P7m3 : rk(P2 :: P4 :: P7 :: nil) >= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP2P4P5P7mtmp : rk(P2 :: P4 :: P5 :: P7 :: nil) >= 3) by (solve_hyps_min HP2P4P5P7eq HP2P4P5P7m3).
	assert(HP2P7mtmp : rk(P2 :: P7 :: nil) >= 2) by (solve_hyps_min HP2P7eq HP2P7m2).
	assert(Hincl : incl (P2 :: P7 :: nil) (list_inter (P2 :: P4 :: P7 :: nil) (P2 :: P5 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P5 :: P7 :: nil) (P2 :: P4 :: P7 :: P2 :: P5 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P7 :: P2 :: P5 :: P7 :: nil) ((P2 :: P4 :: P7 :: nil) ++ (P2 :: P5 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P5P7mtmp;try rewrite HT2 in HP2P4P5P7mtmp.
	assert(HT := rule_2 (P2 :: P4 :: P7 :: nil) (P2 :: P5 :: P7 :: nil) (P2 :: P7 :: nil) 3 2 2 HP2P4P5P7mtmp HP2P7mtmp HP2P5P7Mtmp Hincl);apply HT.
}
try clear HP2P4P7m2. 

assert(HP2P4P6P7P12m2 : rk(P2 :: P4 :: P6 :: P7 :: P12 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P7 :: P12 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P6P7P12m1. 

assert(HP2P4P6P7P12M3 : rk(P2 :: P4 :: P6 :: P7 :: P12 :: nil) <= 3).
{
	assert(HP2P4P6Mtmp : rk(P2 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP2P4P6eq HP2P4P6M2).
	assert(HP4P7P12Mtmp : rk(P4 :: P7 :: P12 :: nil) <= 2) by (solve_hyps_max HP4P7P12eq HP4P7P12M2).
	assert(HP4mtmp : rk(P4 :: nil) >= 1) by (solve_hyps_min HP4eq HP4m1).
	assert(Hincl : incl (P4 :: nil) (list_inter (P2 :: P4 :: P6 :: nil) (P4 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P6 :: P7 :: P12 :: nil) (P2 :: P4 :: P6 :: P4 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P6 :: P4 :: P7 :: P12 :: nil) ((P2 :: P4 :: P6 :: nil) ++ (P4 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P4 :: P6 :: nil) (P4 :: P7 :: P12 :: nil) (P4 :: nil) 2 2 1 HP2P4P6Mtmp HP4P7P12Mtmp HP4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P4P6P7P12M4. 

assert(HP2P4P6P7P12m3 : rk(P2 :: P4 :: P6 :: P7 :: P12 :: nil) >= 3).
{
	assert(HP2P4P7mtmp : rk(P2 :: P4 :: P7 :: nil) >= 3) by (solve_hyps_min HP2P4P7eq HP2P4P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P7 :: nil) (P2 :: P4 :: P6 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: P7 :: nil) (P2 :: P4 :: P6 :: P7 :: P12 :: nil) 3 3 HP2P4P7mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P6P7P12m2. 

assert(HP1P2P4P6P7P12m2 : rk(P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6P7P12m1. 

assert(HP1P2P4P6P7P12m3 : rk(P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6P7P12m2. 

assert(HP1P2P4P6P7P12M3 : rk(P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) <= 3).
{
	assert(HP1P2P4P7Mtmp : rk(P1 :: P2 :: P4 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P4P7eq HP1P2P4P7M3).
	assert(HP2P4P6P7P12Mtmp : rk(P2 :: P4 :: P6 :: P7 :: P12 :: nil) <= 3) by (solve_hyps_max HP2P4P6P7P12eq HP2P4P6P7P12M3).
	assert(HP2P4P7mtmp : rk(P2 :: P4 :: P7 :: nil) >= 3) by (solve_hyps_min HP2P4P7eq HP2P4P7m3).
	assert(Hincl : incl (P2 :: P4 :: P7 :: nil) (list_inter (P1 :: P2 :: P4 :: P7 :: nil) (P2 :: P4 :: P6 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) (P1 :: P2 :: P4 :: P7 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P4 :: P7 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) ((P1 :: P2 :: P4 :: P7 :: nil) ++ (P2 :: P4 :: P6 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P4 :: P7 :: nil) (P2 :: P4 :: P6 :: P7 :: P12 :: nil) (P2 :: P4 :: P7 :: nil) 3 3 3 HP1P2P4P7Mtmp HP2P4P6P7P12Mtmp HP2P4P7mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P4P6P7P12M3. try clear HP2P4P6P7P12m3. try clear HP2P4P7M3. try clear HP2P4P7m3. try clear HP1P2P4P6P7P12M4. 

assert(HP6P8m2 : rk(P6 :: P8 :: nil) >= 2).
{
	assert(HP1P2P4P6P7P12Mtmp : rk(P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) <= 3) by (solve_hyps_max HP1P2P4P6P7P12eq HP1P2P4P6P7P12M3).
	assert(HP1P2P4P6P7P8P12mtmp : rk(P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P4P6P7P8P12eq HP1P2P4P6P7P8P12m4).
	assert(HP6mtmp : rk(P6 :: nil) >= 1) by (solve_hyps_min HP6eq HP6m1).
	assert(Hincl : incl (P6 :: nil) (list_inter (P6 :: P8 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P6 :: P7 :: P8 :: P12 :: nil) (P6 :: P8 :: P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P8 :: P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) ((P6 :: P8 :: nil) ++ (P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P6P7P8P12mtmp;try rewrite HT2 in HP1P2P4P6P7P8P12mtmp.
	assert(HT := rule_2 (P6 :: P8 :: nil) (P1 :: P2 :: P4 :: P6 :: P7 :: P12 :: nil) (P6 :: nil) 4 1 3 HP1P2P4P6P7P8P12mtmp HP6mtmp HP1P2P4P6P7P12Mtmp Hincl);apply HT.
}
try clear HP6P8m1. try clear HP1P2P4P6P7P12M3. try clear HP1P2P4P6P7P12m3. try clear HP1P2P4P6P7P8P12M4. try clear HP1P2P4P6P7P8P12m4. 

assert(HP1P3P4P5P8m2 : rk(P1 :: P3 :: P4 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: P5 :: P8 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P4P5P8m1. 

assert(HP1P3P4P5P8m3 : rk(P1 :: P3 :: P4 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P2P3P4Mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4eq HP1P2P3P4M3).
	assert(HP1P2P3P4P5P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P5P8eq HP1P2P3P4P5P8m3).
	assert(HP1P3P4mtmp : rk(P1 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P3P4eq HP1P3P4m3).
	assert(Hincl : incl (P1 :: P3 :: P4 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P3 :: P4 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P1 :: P3 :: P4 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P1 :: P3 :: P4 :: P5 :: P8 :: nil) ((P1 :: P2 :: P3 :: P4 :: nil) ++ (P1 :: P3 :: P4 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P8mtmp;try rewrite HT2 in HP1P2P3P4P5P8mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P3 :: P4 :: P5 :: P8 :: nil) (P1 :: P3 :: P4 :: nil) 3 3 3 HP1P2P3P4P5P8mtmp HP1P3P4mtmp HP1P2P3P4Mtmp Hincl); apply HT.
}
try clear HP1P3P4P5P8m2. try clear HP1P2P3P4P5P8M4. try clear HP1P2P3P4P5P8m3. 

assert(HP1P3P4P5P8m4 : rk(P1 :: P3 :: P4 :: P5 :: P8 :: nil) >= 4).
{
	assert(HP1P2P3P4P8Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P8 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P8eq HP1P2P3P4P8M4).
	assert(HP1P2P3P4P5P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P8eq HP1P2P3P4P5P8m4).
	assert(HP1P3P4P8mtmp : rk(P1 :: P3 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P3P4P8eq HP1P3P4P8m4).
	assert(Hincl : incl (P1 :: P3 :: P4 :: P8 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P8 :: nil) (P1 :: P3 :: P4 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P8 :: P1 :: P3 :: P4 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P8 :: P1 :: P3 :: P4 :: P5 :: P8 :: nil) ((P1 :: P2 :: P3 :: P4 :: P8 :: nil) ++ (P1 :: P3 :: P4 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P8mtmp;try rewrite HT2 in HP1P2P3P4P5P8mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: P8 :: nil) (P1 :: P3 :: P4 :: P5 :: P8 :: nil) (P1 :: P3 :: P4 :: P8 :: nil) 4 4 4 HP1P2P3P4P5P8mtmp HP1P3P4P8mtmp HP1P2P3P4P8Mtmp Hincl); apply HT.
}
try clear HP1P2P3P4P8M4. try clear HP1P2P3P4P8m4. try clear HP1P3P4P5P8m3. try clear HP1P3P4P8M4. try clear HP1P3P4P8m4. try clear HP1P2P3P4P5P8M4. try clear HP1P2P3P4P5P8m4. 

assert(HP5P8m2 : rk(P5 :: P8 :: nil) >= 2).
{
	assert(HP1P2P4P5P7P12Mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) <= 3) by (solve_hyps_max HP1P2P4P5P7P12eq HP1P2P4P5P7P12M3).
	assert(HP1P2P4P5P7P8P12mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P4P5P7P8P12eq HP1P2P4P5P7P8P12m4).
	assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m1).
	assert(Hincl : incl (P5 :: nil) (list_inter (P5 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: P12 :: nil) (P5 :: P8 :: P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P8 :: P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) ((P5 :: P8 :: nil) ++ (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P7P8P12mtmp;try rewrite HT2 in HP1P2P4P5P7P8P12mtmp.
	assert(HT := rule_2 (P5 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) (P5 :: nil) 4 1 3 HP1P2P4P5P7P8P12mtmp HP5mtmp HP1P2P4P5P7P12Mtmp Hincl);apply HT.
}
try clear HP5P8m1. try clear HP1P2P4P5P7P8P12M4. try clear HP1P2P4P5P7P8P12m4. 

assert(HP1P2P3P4P5m2 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5m1. 

assert(HP1P2P3P4P5M3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) <= 3).
{
	assert(HP1P2P3Mtmp : rk(P1 :: P2 :: P3 :: nil) <= 2) by (solve_hyps_max HP1P2P3eq HP1P2P3M2).
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP1mtmp : rk(P1 :: nil) >= 1) by (solve_hyps_min HP1eq HP1m1).
	assert(Hincl : incl (P1 :: nil) (list_inter (P1 :: P2 :: P3 :: nil) (P1 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P1 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P1 :: P4 :: P5 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P1 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: nil) (P1 :: P4 :: P5 :: nil) (P1 :: nil) 2 2 1 HP1P2P3Mtmp HP1P4P5Mtmp HP1mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4P5M4. 

assert(HP1P2P3P4P5m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5m2. 

assert(HP1P3P4P5M3 : rk(P1 :: P3 :: P4 :: P5 :: nil) <= 3).
{
	assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M1).
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: nil) (P1 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P4 :: P5 :: nil) (P3 :: P1 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P1 :: P4 :: P5 :: nil) ((P3 :: nil) ++ (P1 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: nil) (P1 :: P4 :: P5 :: nil) (nil) 1 2 0 HP3Mtmp HP1P4P5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P3P4P5M4. 

assert(HP1P3P4P5m2 : rk(P1 :: P3 :: P4 :: P5 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P4 :: P5 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P4P5m1. 

assert(HP1P3P4P5m3 : rk(P1 :: P3 :: P4 :: P5 :: nil) >= 3).
{
	assert(HP1P2P3P4Mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4eq HP1P2P3P4M3).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m3).
	assert(HP1P3P4mtmp : rk(P1 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P3P4eq HP1P3P4m3).
	assert(Hincl : incl (P1 :: P3 :: P4 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P3 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P1 :: P3 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P1 :: P3 :: P4 :: P5 :: nil) ((P1 :: P2 :: P3 :: P4 :: nil) ++ (P1 :: P3 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5mtmp;try rewrite HT2 in HP1P2P3P4P5mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P3 :: P4 :: P5 :: nil) (P1 :: P3 :: P4 :: nil) 3 3 3 HP1P2P3P4P5mtmp HP1P3P4mtmp HP1P2P3P4Mtmp Hincl); apply HT.
}
try clear HP1P2P3P4M3. try clear HP1P2P3P4m3. try clear HP1P3P4P5m2. try clear HP1P3P4M3. try clear HP1P3P4m3. try clear HP1P2P3P4P5M3. try clear HP1P2P3P4P5m3. 

assert(HP3P5m2 : rk(P3 :: P5 :: nil) >= 2).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP1P3P4P5mtmp : rk(P1 :: P3 :: P4 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P3P4P5eq HP1P3P4P5m3).
	assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m1).
	assert(Hincl : incl (P5 :: nil) (list_inter (P3 :: P5 :: nil) (P1 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P4 :: P5 :: nil) (P3 :: P5 :: P1 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P5 :: P1 :: P4 :: P5 :: nil) ((P3 :: P5 :: nil) ++ (P1 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P4P5mtmp;try rewrite HT2 in HP1P3P4P5mtmp.
	assert(HT := rule_2 (P3 :: P5 :: nil) (P1 :: P4 :: P5 :: nil) (P5 :: nil) 3 1 2 HP1P3P4P5mtmp HP5mtmp HP1P4P5Mtmp Hincl);apply HT.
}
try clear HP3P5m1. 

assert(HP3P5P8m2 : rk(P3 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP3P5mtmp : rk(P3 :: P5 :: nil) >= 2) by (solve_hyps_min HP3P5eq HP3P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P5 :: nil) (P3 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P5 :: nil) (P3 :: P5 :: P8 :: nil) 2 2 HP3P5mtmp Hcomp Hincl);apply HT.
}
try clear HP3P5P8m1. 

assert(HP3P5P8m3 : rk(P3 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P4P5P8Mtmp : rk(P1 :: P4 :: P5 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P4P5P8eq HP1P4P5P8M3).
	assert(HP1P3P4P5P8mtmp : rk(P1 :: P3 :: P4 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P3P4P5P8eq HP1P3P4P5P8m4).
	assert(HP5P8mtmp : rk(P5 :: P8 :: nil) >= 2) by (solve_hyps_min HP5P8eq HP5P8m2).
	assert(Hincl : incl (P5 :: P8 :: nil) (list_inter (P3 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P4 :: P5 :: P8 :: nil) (P3 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil) ((P3 :: P5 :: P8 :: nil) ++ (P1 :: P4 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P4P5P8mtmp;try rewrite HT2 in HP1P3P4P5P8mtmp.
	assert(HT := rule_2 (P3 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil) (P5 :: P8 :: nil) 4 2 3 HP1P3P4P5P8mtmp HP5P8mtmp HP1P4P5P8Mtmp Hincl);apply HT.
}
try clear HP3P5P8m2. 

assert(HP3P5P6P8m2 : rk(P3 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP3P5mtmp : rk(P3 :: P5 :: nil) >= 2) by (solve_hyps_min HP3P5eq HP3P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P5 :: nil) (P3 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P5 :: nil) (P3 :: P5 :: P6 :: P8 :: nil) 2 2 HP3P5mtmp Hcomp Hincl);apply HT.
}
try clear HP3P5M2. try clear HP3P5m2. try clear HP3P5P6P8m1. 

assert(HP3P5P6P8M3 : rk(P3 :: P5 :: P6 :: P8 :: nil) <= 3).
{
	assert(HP3P5P6Mtmp : rk(P3 :: P5 :: P6 :: nil) <= 2) by (solve_hyps_max HP3P5P6eq HP3P5P6M2).
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: P5 :: P6 :: nil) (P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P5 :: P6 :: P8 :: nil) (P3 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P5 :: P6 :: P8 :: nil) ((P3 :: P5 :: P6 :: nil) ++ (P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P5 :: P6 :: nil) (P8 :: nil) (nil) 2 1 0 HP3P5P6Mtmp HP8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P5P6P8M4. 

assert(HP3P5P6P8m3 : rk(P3 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP3P5P8mtmp : rk(P3 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP3P5P8eq HP3P5P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P3 :: P5 :: P8 :: nil) (P3 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P5 :: P8 :: nil) (P3 :: P5 :: P6 :: P8 :: nil) 3 3 HP3P5P8mtmp Hcomp Hincl);apply HT.
}
try clear HP3P5P8M3. try clear HP3P5P8m3. try clear HP3P5P6P8m2. 

assert(HP4P6P8m2 : rk(P4 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP4P6mtmp : rk(P4 :: P6 :: nil) >= 2) by (solve_hyps_min HP4P6eq HP4P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: nil) 2 2 HP4P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P6P8m1. 

assert(HP4P6P8m3 : rk(P4 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP3P5P6P8Mtmp : rk(P3 :: P5 :: P6 :: P8 :: nil) <= 3) by (solve_hyps_max HP3P5P6P8eq HP3P5P6P8M3).
	assert(HP3P4P5P6P8mtmp : rk(P3 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP3P4P5P6P8eq HP3P4P5P6P8m4).
	assert(HP6P8mtmp : rk(P6 :: P8 :: nil) >= 2) by (solve_hyps_min HP6P8eq HP6P8m2).
	assert(Hincl : incl (P6 :: P8 :: nil) (list_inter (P4 :: P6 :: P8 :: nil) (P3 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P3 :: P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P3 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P6 :: P8 :: P3 :: P5 :: P6 :: P8 :: nil) ((P4 :: P6 :: P8 :: nil) ++ (P3 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP3P4P5P6P8mtmp;try rewrite HT2 in HP3P4P5P6P8mtmp.
	assert(HT := rule_2 (P4 :: P6 :: P8 :: nil) (P3 :: P5 :: P6 :: P8 :: nil) (P6 :: P8 :: nil) 4 2 3 HP3P4P5P6P8mtmp HP6P8mtmp HP3P5P6P8Mtmp Hincl);apply HT.
}
try clear HP4P6P8m2. try clear HP3P4P5P6P8M4. try clear HP3P4P5P6P8m4. 

assert(HP4P6P8P10m2 : rk(P4 :: P6 :: P8 :: P10 :: nil) >= 2).
{
	assert(HP4P6mtmp : rk(P4 :: P6 :: nil) >= 2) by (solve_hyps_min HP4P6eq HP4P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: P10 :: nil) 2 2 HP4P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P6P8P10m1. 

assert(HP4P6P8P10m3 : rk(P4 :: P6 :: P8 :: P10 :: nil) >= 3).
{
	assert(HP4P6P8mtmp : rk(P4 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P6P8eq HP4P6P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P10 :: nil) 3 3 HP4P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP4P6P8P10m2. 

assert(HP4P6P8P10M3 : rk(P4 :: P6 :: P8 :: P10 :: nil) <= 3).
{
	assert(HP2P4P6P8P10Mtmp : rk(P2 :: P4 :: P6 :: P8 :: P10 :: nil) <= 3) by (solve_hyps_max HP2P4P6P8P10eq HP2P4P6P8P10M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: P8 :: P10 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P4 :: P6 :: P8 :: P10 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: nil) 3 3 HP2P4P6P8P10Mtmp Hcomp Hincl);apply HT.
}
try clear HP4P6P8P10M4. try clear HP2P4P6P8P10M3. try clear HP2P4P6P8P10m3. 

assert(HP1P2P3P5P6P8m2 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P8m1. 

assert(HP1P2P3P5P6P8m3 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P5P6P8m2. 

assert(HP1P2P3P5P6P8m4 : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP1P2P5P8mtmp : rk(P1 :: P2 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P5P8eq HP1P2P5P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) 4 4 HP1P2P5P8mtmp Hcomp Hincl);apply HT.
}


assert(HP2P3P8m2 : rk(P2 :: P3 :: P8 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P8m1. 

assert(HP2P3P8m3 : rk(P2 :: P3 :: P8 :: nil) >= 3).
{
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(HP1P2P3P8P12P13mtmp : rk(P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P3P8P12P13eq HP1P2P3P8P12P13m3).
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hincl : incl (P2 :: P3 :: nil) (list_inter (P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P12 :: P13 :: nil) (P2 :: P3 :: P8 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P8 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P2 :: P3 :: P8 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P8P12P13mtmp;try rewrite HT2 in HP1P2P3P8P12P13mtmp.
	assert(HT := rule_2 (P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (P2 :: P3 :: nil) 3 2 2 HP1P2P3P8P12P13mtmp HP2P3mtmp HP1P2P3P12P13Mtmp Hincl);apply HT.
}
try clear HP2P3P8m2. try clear HP1P2P3P8P12P13M3. try clear HP1P2P3P8P12P13m3. 

assert(HP2P3P5P8m2 : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P5P8m1. 

assert(HP2P3P5P8m3 : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P2P3P5Mtmp : rk(P1 :: P2 :: P3 :: P5 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5eq HP1P2P3P5M3).
	assert(HP1P2P3P5P8mtmp : rk(P1 :: P2 :: P3 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P3P5P8eq HP1P2P3P5P8m3).
	assert(HP2P3P5mtmp : rk(P2 :: P3 :: P5 :: nil) >= 3) by (solve_hyps_min HP2P3P5eq HP2P3P5m3).
	assert(Hincl : incl (P2 :: P3 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: nil) (P2 :: P3 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P5 :: P2 :: P3 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P2 :: P3 :: P5 :: P8 :: nil) ((P1 :: P2 :: P3 :: P5 :: nil) ++ (P2 :: P3 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P8mtmp;try rewrite HT2 in HP1P2P3P5P8mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: nil) (P2 :: P3 :: P5 :: P8 :: nil) (P2 :: P3 :: P5 :: nil) 3 3 3 HP1P2P3P5P8mtmp HP2P3P5mtmp HP1P2P3P5Mtmp Hincl); apply HT.
}
try clear HP2P3P5P8m2. try clear HP1P2P3P5P8M4. try clear HP1P2P3P5P8m3. 

assert(HP2P3P5P8m4 : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 4).
{
	assert(HP1P2P3P8P9Mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: nil) <= 3) by (solve_hyps_max HP1P2P3P8P9eq HP1P2P3P8P9M3).
	assert(HP1P2P3P5P8P9mtmp : rk(P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P8P9eq HP1P2P3P5P8P9m4).
	assert(HP2P3P8mtmp : rk(P2 :: P3 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P3P8eq HP2P3P8m3).
	assert(Hincl : incl (P2 :: P3 :: P8 :: nil) (list_inter (P2 :: P3 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P8 :: P9 :: nil) (P2 :: P3 :: P5 :: P8 :: P1 :: P2 :: P3 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P5 :: P8 :: P1 :: P2 :: P3 :: P8 :: P9 :: nil) ((P2 :: P3 :: P5 :: P8 :: nil) ++ (P1 :: P2 :: P3 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P8P9mtmp;try rewrite HT2 in HP1P2P3P5P8P9mtmp.
	assert(HT := rule_2 (P2 :: P3 :: P5 :: P8 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: nil) (P2 :: P3 :: P8 :: nil) 4 3 3 HP1P2P3P5P8P9mtmp HP2P3P8mtmp HP1P2P3P8P9Mtmp Hincl);apply HT.
}
try clear HP2P3P5P8m3. try clear HP1P2P3P8P9M3. try clear HP1P2P3P8P9m3. try clear HP2P3P8M3. try clear HP2P3P8m3. try clear HP1P2P3P5P8P9M4. try clear HP1P2P3P5P8P9m4. 

assert(HP2P3P5P6P8m2 : rk(P2 :: P3 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P6 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3P5P6P8m1. 

assert(HP2P3P5P6P8m3 : rk(P2 :: P3 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P2P3P5Mtmp : rk(P1 :: P2 :: P3 :: P5 :: nil) <= 3) by (solve_hyps_max HP1P2P3P5eq HP1P2P3P5M3).
	assert(HP1P2P3P5P6P8mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P3P5P6P8eq HP1P2P3P5P6P8m3).
	assert(HP2P3P5mtmp : rk(P2 :: P3 :: P5 :: nil) >= 3) by (solve_hyps_min HP2P3P5eq HP2P3P5m3).
	assert(Hincl : incl (P2 :: P3 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: nil) (P2 :: P3 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) (P1 :: P2 :: P3 :: P5 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) ((P1 :: P2 :: P3 :: P5 :: nil) ++ (P2 :: P3 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P8mtmp;try rewrite HT2 in HP1P2P3P5P6P8mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: nil) (P2 :: P3 :: P5 :: P6 :: P8 :: nil) (P2 :: P3 :: P5 :: nil) 3 3 3 HP1P2P3P5P6P8mtmp HP2P3P5mtmp HP1P2P3P5Mtmp Hincl); apply HT.
}
try clear HP1P2P3P5M3. try clear HP1P2P3P5m3. try clear HP2P3P5P6P8m2. try clear HP2P3P5M3. try clear HP2P3P5m3. try clear HP1P2P3P5P6P8M4. try clear HP1P2P3P5P6P8m3. 

assert(HP2P3P5P6P8m4 : rk(P2 :: P3 :: P5 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP1P2P3P5P8Mtmp : rk(P1 :: P2 :: P3 :: P5 :: P8 :: nil) <= 4) by (solve_hyps_max HP1P2P3P5P8eq HP1P2P3P5P8M4).
	assert(HP1P2P3P5P6P8mtmp : rk(P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P5P6P8eq HP1P2P3P5P6P8m4).
	assert(HP2P3P5P8mtmp : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP2P3P5P8eq HP2P3P5P8m4).
	assert(Hincl : incl (P2 :: P3 :: P5 :: P8 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: P8 :: nil) (P2 :: P3 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) (P1 :: P2 :: P3 :: P5 :: P8 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P8 :: P2 :: P3 :: P5 :: P6 :: P8 :: nil) ((P1 :: P2 :: P3 :: P5 :: P8 :: nil) ++ (P2 :: P3 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P5P6P8mtmp;try rewrite HT2 in HP1P2P3P5P6P8mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P5 :: P8 :: nil) (P2 :: P3 :: P5 :: P6 :: P8 :: nil) (P2 :: P3 :: P5 :: P8 :: nil) 4 4 4 HP1P2P3P5P6P8mtmp HP2P3P5P8mtmp HP1P2P3P5P8Mtmp Hincl); apply HT.
}
try clear HP1P2P3P5P8M4. try clear HP1P2P3P5P8m4. try clear HP2P3P5P6P8m3. try clear HP2P3P5P8M4. try clear HP2P3P5P8m4. try clear HP1P2P3P5P6P8M4. try clear HP1P2P3P5P6P8m4. 

assert(HP2P6P8m2 : rk(P2 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP2P6mtmp : rk(P2 :: P6 :: nil) >= 2) by (solve_hyps_min HP2P6eq HP2P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P6 :: nil) (P2 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P6 :: nil) (P2 :: P6 :: P8 :: nil) 2 2 HP2P6mtmp Hcomp Hincl);apply HT.
}
try clear HP2P6P8m1. 

assert(HP2P6P8m3 : rk(P2 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP3P5P6P8Mtmp : rk(P3 :: P5 :: P6 :: P8 :: nil) <= 3) by (solve_hyps_max HP3P5P6P8eq HP3P5P6P8M3).
	assert(HP2P3P5P6P8mtmp : rk(P2 :: P3 :: P5 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP2P3P5P6P8eq HP2P3P5P6P8m4).
	assert(HP6P8mtmp : rk(P6 :: P8 :: nil) >= 2) by (solve_hyps_min HP6P8eq HP6P8m2).
	assert(Hincl : incl (P6 :: P8 :: nil) (list_inter (P2 :: P6 :: P8 :: nil) (P3 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P6 :: P8 :: nil) (P2 :: P6 :: P8 :: P3 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P6 :: P8 :: P3 :: P5 :: P6 :: P8 :: nil) ((P2 :: P6 :: P8 :: nil) ++ (P3 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P5P6P8mtmp;try rewrite HT2 in HP2P3P5P6P8mtmp.
	assert(HT := rule_2 (P2 :: P6 :: P8 :: nil) (P3 :: P5 :: P6 :: P8 :: nil) (P6 :: P8 :: nil) 4 2 3 HP2P3P5P6P8mtmp HP6P8mtmp HP3P5P6P8Mtmp Hincl);apply HT.
}
try clear HP2P6P8m2. try clear HP2P3P5P6P8M4. try clear HP2P3P5P6P8m4. 

assert(HP2P6P8P10M3 : rk(P2 :: P6 :: P8 :: P10 :: nil) <= 3).
{
	assert(HP6Mtmp : rk(P6 :: nil) <= 1) by (solve_hyps_max HP6eq HP6M1).
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P6 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P6 :: P8 :: P10 :: nil) (P6 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P2 :: P8 :: P10 :: nil) ((P6 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: nil) (P2 :: P8 :: P10 :: nil) (nil) 1 2 0 HP6Mtmp HP2P8P10Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P6P8P10M4. 

assert(HP2P6P8P10m2 : rk(P2 :: P6 :: P8 :: P10 :: nil) >= 2).
{
	assert(HP2P6mtmp : rk(P2 :: P6 :: nil) >= 2) by (solve_hyps_min HP2P6eq HP2P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P6 :: nil) (P2 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P6 :: nil) (P2 :: P6 :: P8 :: P10 :: nil) 2 2 HP2P6mtmp Hcomp Hincl);apply HT.
}
try clear HP2P6P8P10m1. 

assert(HP2P6P8P10m3 : rk(P2 :: P6 :: P8 :: P10 :: nil) >= 3).
{
	assert(HP2P6P8mtmp : rk(P2 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P6P8eq HP2P6P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P6 :: P8 :: nil) (P2 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P6 :: P8 :: nil) (P2 :: P6 :: P8 :: P10 :: nil) 3 3 HP2P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P6P8P10m2. 

assert(HP6P10m2 : rk(P6 :: P10 :: nil) >= 2).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP2P6P8P10mtmp : rk(P2 :: P6 :: P8 :: P10 :: nil) >= 3) by (solve_hyps_min HP2P6P8P10eq HP2P6P8P10m3).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P6 :: P10 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P6 :: P8 :: P10 :: nil) (P6 :: P10 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P10 :: P2 :: P8 :: P10 :: nil) ((P6 :: P10 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P6P8P10mtmp;try rewrite HT2 in HP2P6P8P10mtmp.
	assert(HT := rule_2 (P6 :: P10 :: nil) (P2 :: P8 :: P10 :: nil) (P10 :: nil) 3 1 2 HP2P6P8P10mtmp HP10mtmp HP2P8P10Mtmp Hincl);apply HT.
}
try clear HP6P10m1. try clear HP2P6P8P10M3. try clear HP2P6P8P10m3. 

assert(HP4P6P8P10P14m2 : rk(P4 :: P6 :: P8 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP4P6mtmp : rk(P4 :: P6 :: nil) >= 2) by (solve_hyps_min HP4P6eq HP4P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: P10 :: P14 :: nil) 2 2 HP4P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P6M2. try clear HP4P6m2. try clear HP4P6P8P10P14m1. 

assert(HP4P6P8P10P14m3 : rk(P4 :: P6 :: P8 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP4P6P8mtmp : rk(P4 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P6P8eq HP4P6P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P10 :: P14 :: nil) 3 3 HP4P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP4P6P8P10P14m2. 

assert(HP4P6P8P10P14M3 : rk(P4 :: P6 :: P8 :: P10 :: P14 :: nil) <= 3).
{
	assert(HP4P6P8P10Mtmp : rk(P4 :: P6 :: P8 :: P10 :: nil) <= 3) by (solve_hyps_max HP4P6P8P10eq HP4P6P8P10M3).
	assert(HP6P10P14Mtmp : rk(P6 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP6P10P14eq HP6P10P14M2).
	assert(HP6P10mtmp : rk(P6 :: P10 :: nil) >= 2) by (solve_hyps_min HP6P10eq HP6P10m2).
	assert(Hincl : incl (P6 :: P10 :: nil) (list_inter (P4 :: P6 :: P8 :: P10 :: nil) (P6 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P6 :: P8 :: P10 :: P14 :: nil) (P4 :: P6 :: P8 :: P10 :: P6 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P6 :: P8 :: P10 :: P6 :: P10 :: P14 :: nil) ((P4 :: P6 :: P8 :: P10 :: nil) ++ (P6 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P6 :: P8 :: P10 :: nil) (P6 :: P10 :: P14 :: nil) (P6 :: P10 :: nil) 3 2 2 HP4P6P8P10Mtmp HP6P10P14Mtmp HP6P10mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P6P8P10M3. try clear HP4P6P8P10m3. try clear HP6P10M2. try clear HP6P10m2. try clear HP4P6P8P10P14M4. 

assert(HP1P2P4P6P8m2 : rk(P1 :: P2 :: P4 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P6 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6P8m1. 

assert(HP1P2P4P6P8m3 : rk(P1 :: P2 :: P4 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P6 :: P8 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6P8m2. 

assert(HP1P2P4P6P8m4 : rk(P1 :: P2 :: P4 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P6 :: P8 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P6P8m3. 

assert(HP2P4P6P8m2 : rk(P2 :: P4 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P8 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P6P8m1. 

assert(HP2P4P6P8M3 : rk(P2 :: P4 :: P6 :: P8 :: nil) <= 3).
{
	assert(HP2P4P6Mtmp : rk(P2 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP2P4P6eq HP2P4P6M2).
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: P4 :: P6 :: nil) (P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P6 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P6 :: P8 :: nil) ((P2 :: P4 :: P6 :: nil) ++ (P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P4 :: P6 :: nil) (P8 :: nil) (nil) 2 1 0 HP2P4P6Mtmp HP8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P4P6P8M4. 

assert(HP2P4P6P8m3 : rk(P2 :: P4 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP2P4P8mtmp : rk(P2 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P4P8eq HP2P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: nil) 3 3 HP2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P6P8m2. 

assert(HP1P4P6P8m2 : rk(P1 :: P4 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P6 :: P8 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P6P8m1. 

assert(HP1P4P6P8m3 : rk(P1 :: P4 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P4P6mtmp : rk(P1 :: P4 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P4P6eq HP1P4P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P6 :: nil) (P1 :: P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P6 :: nil) (P1 :: P4 :: P6 :: P8 :: nil) 3 3 HP1P4P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P6P8m2. 

assert(HP1P4P6P8m4 : rk(P1 :: P4 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP2P4P6P8Mtmp : rk(P2 :: P4 :: P6 :: P8 :: nil) <= 3) by (solve_hyps_max HP2P4P6P8eq HP2P4P6P8M3).
	assert(HP1P2P4P6P8mtmp : rk(P1 :: P2 :: P4 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P6P8eq HP1P2P4P6P8m4).
	assert(HP4P6P8mtmp : rk(P4 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P6P8eq HP4P6P8m3).
	assert(Hincl : incl (P4 :: P6 :: P8 :: nil) (list_inter (P1 :: P4 :: P6 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P6 :: P8 :: nil) (P1 :: P4 :: P6 :: P8 :: P2 :: P4 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P6 :: P8 :: P2 :: P4 :: P6 :: P8 :: nil) ((P1 :: P4 :: P6 :: P8 :: nil) ++ (P2 :: P4 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P6P8mtmp;try rewrite HT2 in HP1P2P4P6P8mtmp.
	assert(HT := rule_2 (P1 :: P4 :: P6 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: nil) 4 3 3 HP1P2P4P6P8mtmp HP4P6P8mtmp HP2P4P6P8Mtmp Hincl);apply HT.
}
try clear HP1P4P6P8m3. try clear HP4P6P8M3. try clear HP4P6P8m3. 

assert(HP1P4P6P8P10P14m2 : rk(P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P6P8P10P14m1. 

assert(HP1P4P6P8P10P14m3 : rk(P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P4P6mtmp : rk(P1 :: P4 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P4P6eq HP1P4P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P6 :: nil) (P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P6 :: nil) (P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) 3 3 HP1P4P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P6M3. try clear HP1P4P6m3. try clear HP1P4P6P8P10P14m2. 

assert(HP1P4P6P8P10P14m4 : rk(P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) >= 4).
{
	assert(HP1P4P6P8mtmp : rk(P1 :: P4 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P4P6P8eq HP1P4P6P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P6 :: P8 :: nil) (P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P6 :: P8 :: nil) (P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) 4 4 HP1P4P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P6P8M4. try clear HP1P4P6P8m4. try clear HP1P4P6P8P10P14m3. 

assert(HP4P8m2 : rk(P4 :: P8 :: nil) >= 2).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP2P4P8mtmp : rk(P2 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P4P8eq HP2P4P8m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P4 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P8 :: nil) ((P2 :: nil) ++ (P4 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P8mtmp;try rewrite HT2 in HP2P4P8mtmp.
	assert(HT := rule_4 (P2 :: nil) (P4 :: P8 :: nil) (nil) 3 0 1 HP2P4P8mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}
try clear HP4P8m1. 

assert(HP4P8P14m2 : rk(P4 :: P8 :: P14 :: nil) >= 2).
{
	assert(HP4P8mtmp : rk(P4 :: P8 :: nil) >= 2) by (solve_hyps_min HP4P8eq HP4P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P8 :: nil) (P4 :: P8 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P8 :: nil) (P4 :: P8 :: P14 :: nil) 2 2 HP4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP4P8M2. try clear HP4P8m2. try clear HP4P8P14m1. 

assert(HP4P8P14M2 : rk(P4 :: P8 :: P14 :: nil) <= 2).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP4P6P8P10P14Mtmp : rk(P4 :: P6 :: P8 :: P10 :: P14 :: nil) <= 3) by (solve_hyps_max HP4P6P8P10P14eq HP4P6P8P10P14M3).
	assert(HP1P4P6P8P10P14mtmp : rk(P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P6P8P10P14eq HP1P4P6P8P10P14m4).
	assert(Hincl : incl (P4 :: P8 :: P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P4 :: P6 :: P8 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P4 :: P6 :: P8 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P6P8P10P14mtmp;try rewrite HT2 in HP1P4P6P8P10P14mtmp.
	assert(HT := rule_3 (P1 :: P4 :: P8 :: P14 :: nil) (P4 :: P6 :: P8 :: P10 :: P14 :: nil) (P4 :: P8 :: P14 :: nil) 3 3 4 HP1P4P8P14Mtmp HP4P6P8P10P14Mtmp HP1P4P6P8P10P14mtmp Hincl);apply HT.
}
try clear HP4P6P8P10P14M3. try clear HP4P6P8P10P14m3. try clear HP4P8P14M3. try clear HP1P4P6P8P10P14M4. try clear HP1P4P6P8P10P14m4. 

assert(HP1P2P4P5P7P8m2 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P8m1. 

assert(HP1P2P4P5P7P8m3 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P8m2. 

assert(HP1P2P4P5P7P8m4 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}


assert(HP2P4P5P7P8m2 : rk(P2 :: P4 :: P5 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P5 :: P7 :: P8 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P5P7P8m1. 

assert(HP2P4P5P7P8m3 : rk(P2 :: P4 :: P5 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP1P2P4P5P7P8mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P4P5P7P8eq HP1P2P4P5P7P8m3).
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P1 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) (P1 :: P4 :: P5 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P2 :: P4 :: P5 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P7P8mtmp;try rewrite HT2 in HP1P2P4P5P7P8mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P7 :: P8 :: nil) (P4 :: P5 :: nil) 3 2 2 HP1P2P4P5P7P8mtmp HP4P5mtmp HP1P4P5Mtmp Hincl); apply HT.
}
try clear HP2P4P5P7P8m2. try clear HP1P2P4P5P7P8M4. try clear HP1P2P4P5P7P8m3. 

assert(HP2P4P5P7P8m4 : rk(P2 :: P4 :: P5 :: P7 :: P8 :: nil) >= 4).
{
	assert(HP1P4P5P8Mtmp : rk(P1 :: P4 :: P5 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P4P5P8eq HP1P4P5P8M3).
	assert(HP1P2P4P5P7P8mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P5P7P8eq HP1P2P4P5P7P8m4).
	assert(HP4P5P8mtmp : rk(P4 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P8eq HP4P5P8m3).
	assert(Hincl : incl (P4 :: P5 :: P8 :: nil) (list_inter (P1 :: P4 :: P5 :: P8 :: nil) (P2 :: P4 :: P5 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P8 :: P2 :: P4 :: P5 :: P7 :: P8 :: nil) ((P1 :: P4 :: P5 :: P8 :: nil) ++ (P2 :: P4 :: P5 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P7P8mtmp;try rewrite HT2 in HP1P2P4P5P7P8mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P5 :: P8 :: nil) (P2 :: P4 :: P5 :: P7 :: P8 :: nil) (P4 :: P5 :: P8 :: nil) 4 3 3 HP1P2P4P5P7P8mtmp HP4P5P8mtmp HP1P4P5P8Mtmp Hincl); apply HT.
}
try clear HP2P4P5P7P8m3. try clear HP1P2P4P5P7P8M4. try clear HP1P2P4P5P7P8m4. 

assert(HP1P2P4P7P8P12m2 : rk(P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P7P8P12m1. 

assert(HP1P2P4P7P8P12m3 : rk(P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P7P8P12m2. 

assert(HP1P2P4P7P8P12m4 : rk(P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P7P8P12m3. 

assert(HP4P7m2 : rk(P4 :: P7 :: nil) >= 2).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP2P4P5P7mtmp : rk(P2 :: P4 :: P5 :: P7 :: nil) >= 3) by (solve_hyps_min HP2P4P5P7eq HP2P4P5P7m3).
	assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m1).
	assert(Hincl : incl (P7 :: nil) (list_inter (P4 :: P7 :: nil) (P2 :: P5 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P5 :: P7 :: nil) (P4 :: P7 :: P2 :: P5 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P7 :: P2 :: P5 :: P7 :: nil) ((P4 :: P7 :: nil) ++ (P2 :: P5 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P5P7mtmp;try rewrite HT2 in HP2P4P5P7mtmp.
	assert(HT := rule_2 (P4 :: P7 :: nil) (P2 :: P5 :: P7 :: nil) (P7 :: nil) 3 1 2 HP2P4P5P7mtmp HP7mtmp HP2P5P7Mtmp Hincl);apply HT.
}
try clear HP4P7m1. try clear HP2P4P5P7M3. try clear HP2P4P5P7m3. 

assert(HP1P2P4P7P12m2 : rk(P1 :: P2 :: P4 :: P7 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P7 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P7P12m1. 

assert(HP1P2P4P7P12m3 : rk(P1 :: P2 :: P4 :: P7 :: P12 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P7 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P7 :: P12 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P7P12m2. 

assert(HP1P2P4P7P12M3 : rk(P1 :: P2 :: P4 :: P7 :: P12 :: nil) <= 3).
{
	assert(HP1P2P4P7Mtmp : rk(P1 :: P2 :: P4 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P4P7eq HP1P2P4P7M3).
	assert(HP4P7P12Mtmp : rk(P4 :: P7 :: P12 :: nil) <= 2) by (solve_hyps_max HP4P7P12eq HP4P7P12M2).
	assert(HP4P7mtmp : rk(P4 :: P7 :: nil) >= 2) by (solve_hyps_min HP4P7eq HP4P7m2).
	assert(Hincl : incl (P4 :: P7 :: nil) (list_inter (P1 :: P2 :: P4 :: P7 :: nil) (P4 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P7 :: P12 :: nil) (P1 :: P2 :: P4 :: P7 :: P4 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P4 :: P7 :: P4 :: P7 :: P12 :: nil) ((P1 :: P2 :: P4 :: P7 :: nil) ++ (P4 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P4 :: P7 :: nil) (P4 :: P7 :: P12 :: nil) (P4 :: P7 :: nil) 3 2 2 HP1P2P4P7Mtmp HP4P7P12Mtmp HP4P7mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P4P7M3. try clear HP1P2P4P7m3. try clear HP1P2P4P7P12M4. 

assert(HP7P8m2 : rk(P7 :: P8 :: nil) >= 2).
{
	assert(HP1P2P4P7P12Mtmp : rk(P1 :: P2 :: P4 :: P7 :: P12 :: nil) <= 3) by (solve_hyps_max HP1P2P4P7P12eq HP1P2P4P7P12M3).
	assert(HP1P2P4P7P8P12mtmp : rk(P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P4P7P8P12eq HP1P2P4P7P8P12m4).
	assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m1).
	assert(Hincl : incl (P7 :: nil) (list_inter (P7 :: P8 :: nil) (P1 :: P2 :: P4 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P7 :: P8 :: P12 :: nil) (P7 :: P8 :: P1 :: P2 :: P4 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P8 :: P1 :: P2 :: P4 :: P7 :: P12 :: nil) ((P7 :: P8 :: nil) ++ (P1 :: P2 :: P4 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P7P8P12mtmp;try rewrite HT2 in HP1P2P4P7P8P12mtmp.
	assert(HT := rule_2 (P7 :: P8 :: nil) (P1 :: P2 :: P4 :: P7 :: P12 :: nil) (P7 :: nil) 4 1 3 HP1P2P4P7P8P12mtmp HP7mtmp HP1P2P4P7P12Mtmp Hincl);apply HT.
}
try clear HP7P8m1. try clear HP1P2P4P7P12M3. try clear HP1P2P4P7P12m3. try clear HP1P2P4P7P8P12M4. try clear HP1P2P4P7P8P12m4. 

assert(HP2P5m2 : rk(P2 :: P5 :: nil) >= 2).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P5 :: nil) ((P1 :: nil) ++ (P2 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5mtmp;try rewrite HT2 in HP1P2P5mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P5 :: nil) (nil) 3 0 1 HP1P2P5mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}
try clear HP2P5m1. 

assert(HP2P5P8m2 : rk(P2 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P8 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P8m1. 

assert(HP2P5P8m3 : rk(P2 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P4P5P8Mtmp : rk(P1 :: P4 :: P5 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P4P5P8eq HP1P4P5P8M3).
	assert(HP1P2P4P5P8mtmp : rk(P1 :: P2 :: P4 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P5P8eq HP1P2P4P5P8m4).
	assert(HP5P8mtmp : rk(P5 :: P8 :: nil) >= 2) by (solve_hyps_min HP5P8eq HP5P8m2).
	assert(Hincl : incl (P5 :: P8 :: nil) (list_inter (P2 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P8 :: nil) (P2 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil) ((P2 :: P5 :: P8 :: nil) ++ (P1 :: P4 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P8mtmp;try rewrite HT2 in HP1P2P4P5P8mtmp.
	assert(HT := rule_2 (P2 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil) (P5 :: P8 :: nil) 4 2 3 HP1P2P4P5P8mtmp HP5P8mtmp HP1P4P5P8Mtmp Hincl);apply HT.
}
try clear HP2P5P8m2. try clear HP1P2P4P5P8M4. try clear HP1P2P4P5P8m4. 

assert(HP2P5P7P8m2 : rk(P2 :: P5 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P8 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P7P8m1. 

assert(HP2P5P7P8M3 : rk(P2 :: P5 :: P7 :: P8 :: nil) <= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: P5 :: P7 :: nil) (P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P8 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P5 :: P7 :: nil) (P8 :: nil) (nil) 2 1 0 HP2P5P7Mtmp HP8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P5P7P8M4. 

assert(HP2P5P7P8m3 : rk(P2 :: P5 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP2P5P8mtmp : rk(P2 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P5P8eq HP2P5P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: P8 :: nil) (P2 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: P8 :: nil) (P2 :: P5 :: P7 :: P8 :: nil) 3 3 HP2P5P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P8M3. try clear HP2P5P8m3. try clear HP2P5P7P8m2. 

assert(HP4P7P8m2 : rk(P4 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP4P7mtmp : rk(P4 :: P7 :: nil) >= 2) by (solve_hyps_min HP4P7eq HP4P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P7 :: nil) (P4 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P7 :: nil) (P4 :: P7 :: P8 :: nil) 2 2 HP4P7mtmp Hcomp Hincl);apply HT.
}
try clear HP4P7P8m1. 

assert(HP4P7P8m3 : rk(P4 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP2P5P7P8Mtmp : rk(P2 :: P5 :: P7 :: P8 :: nil) <= 3) by (solve_hyps_max HP2P5P7P8eq HP2P5P7P8M3).
	assert(HP2P4P5P7P8mtmp : rk(P2 :: P4 :: P5 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP2P4P5P7P8eq HP2P4P5P7P8m4).
	assert(HP7P8mtmp : rk(P7 :: P8 :: nil) >= 2) by (solve_hyps_min HP7P8eq HP7P8m2).
	assert(Hincl : incl (P7 :: P8 :: nil) (list_inter (P4 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P5 :: P7 :: P8 :: nil) (P4 :: P7 :: P8 :: P2 :: P5 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P7 :: P8 :: P2 :: P5 :: P7 :: P8 :: nil) ((P4 :: P7 :: P8 :: nil) ++ (P2 :: P5 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P5P7P8mtmp;try rewrite HT2 in HP2P4P5P7P8mtmp.
	assert(HT := rule_2 (P4 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P8 :: nil) (P7 :: P8 :: nil) 4 2 3 HP2P4P5P7P8mtmp HP7P8mtmp HP2P5P7P8Mtmp Hincl);apply HT.
}
try clear HP4P7P8m2. try clear HP2P4P5P7P8M4. try clear HP2P4P5P7P8m4. 

assert(HP4P7P8P12P14m2 : rk(P4 :: P7 :: P8 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP4P7mtmp : rk(P4 :: P7 :: nil) >= 2) by (solve_hyps_min HP4P7eq HP4P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P7 :: nil) (P4 :: P7 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P7 :: nil) (P4 :: P7 :: P8 :: P12 :: P14 :: nil) 2 2 HP4P7mtmp Hcomp Hincl);apply HT.
}
try clear HP4P7M2. try clear HP4P7m2. try clear HP4P7P8P12P14m1. 

assert(HP4P7P8P12P14m3 : rk(P4 :: P7 :: P8 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP4P7P8mtmp : rk(P4 :: P7 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P7P8eq HP4P7P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P7 :: P8 :: nil) (P4 :: P7 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P7 :: P8 :: nil) (P4 :: P7 :: P8 :: P12 :: P14 :: nil) 3 3 HP4P7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP4P7P8M3. try clear HP4P7P8m3. try clear HP4P7P8P12P14m2. 

assert(HP4P7P8P12P14M3 : rk(P4 :: P7 :: P8 :: P12 :: P14 :: nil) <= 3).
{
	assert(HP4P7P12Mtmp : rk(P4 :: P7 :: P12 :: nil) <= 2) by (solve_hyps_max HP4P7P12eq HP4P7P12M2).
	assert(HP4P8P14Mtmp : rk(P4 :: P8 :: P14 :: nil) <= 2) by (solve_hyps_max HP4P8P14eq HP4P8P14M2).
	assert(HP4mtmp : rk(P4 :: nil) >= 1) by (solve_hyps_min HP4eq HP4m1).
	assert(Hincl : incl (P4 :: nil) (list_inter (P4 :: P7 :: P12 :: nil) (P4 :: P8 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P7 :: P8 :: P12 :: P14 :: nil) (P4 :: P7 :: P12 :: P4 :: P8 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P7 :: P12 :: P4 :: P8 :: P14 :: nil) ((P4 :: P7 :: P12 :: nil) ++ (P4 :: P8 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P7 :: P12 :: nil) (P4 :: P8 :: P14 :: nil) (P4 :: nil) 2 2 1 HP4P7P12Mtmp HP4P8P14Mtmp HP4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P8P14M2. try clear HP4P8P14m2. try clear HP4P7P8P12P14M4. 

assert(HP1P2P5P7P8m2 : rk(P1 :: P2 :: P5 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P7P8m1. 

assert(HP1P2P5P7P8m3 : rk(P1 :: P2 :: P5 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P7P8m2. 

assert(HP1P2P5P7P8m4 : rk(P1 :: P2 :: P5 :: P7 :: P8 :: nil) >= 4).
{
	assert(HP1P2P5P8mtmp : rk(P1 :: P2 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P5P8eq HP1P2P5P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: nil) 4 4 HP1P2P5P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P7P8m3. 

assert(HP1P2P6P8m2 : rk(P1 :: P2 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P8m1. 

assert(HP1P2P6P8m3 : rk(P1 :: P2 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P2P6mtmp : rk(P1 :: P2 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P6eq HP1P2P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P8 :: nil) 3 3 HP1P2P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P8m2. 

assert(HP1P2P6P8m4 : rk(P1 :: P2 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP2P4P6P8Mtmp : rk(P2 :: P4 :: P6 :: P8 :: nil) <= 3) by (solve_hyps_max HP2P4P6P8eq HP2P4P6P8M3).
	assert(HP1P2P4P6P8mtmp : rk(P1 :: P2 :: P4 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P6P8eq HP1P2P4P6P8m4).
	assert(HP2P6P8mtmp : rk(P2 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P6P8eq HP2P6P8m3).
	assert(Hincl : incl (P2 :: P6 :: P8 :: nil) (list_inter (P1 :: P2 :: P6 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P6 :: P8 :: nil) (P1 :: P2 :: P6 :: P8 :: P2 :: P4 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P6 :: P8 :: P2 :: P4 :: P6 :: P8 :: nil) ((P1 :: P2 :: P6 :: P8 :: nil) ++ (P2 :: P4 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P6P8mtmp;try rewrite HT2 in HP1P2P4P6P8mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P6 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: nil) (P2 :: P6 :: P8 :: nil) 4 3 3 HP1P2P4P6P8mtmp HP2P6P8mtmp HP2P4P6P8Mtmp Hincl);apply HT.
}
try clear HP1P2P6P8m3. 

assert(HP1P2P6P7P8m2 : rk(P1 :: P2 :: P6 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P7 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7P8m1. 

assert(HP1P2P6P7P8m3 : rk(P1 :: P2 :: P6 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P2P6mtmp : rk(P1 :: P2 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P6eq HP1P2P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P7 :: P8 :: nil) 3 3 HP1P2P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7P8m2. 

assert(HP1P2P6P7P8m4 : rk(P1 :: P2 :: P6 :: P7 :: P8 :: nil) >= 4).
{
	assert(HP1P2P6P8mtmp : rk(P1 :: P2 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P6P8eq HP1P2P6P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: P8 :: nil) (P1 :: P2 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: P8 :: nil) (P1 :: P2 :: P6 :: P7 :: P8 :: nil) 4 4 HP1P2P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P7P8m3. 

assert(HP1P6m2 : rk(P1 :: P6 :: nil) >= 2).
{
	assert(HP2P4P6Mtmp : rk(P2 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP2P4P6eq HP2P4P6M2).
	assert(HP1P2P4P6mtmp : rk(P1 :: P2 :: P4 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P4P6eq HP1P2P4P6m3).
	assert(HP6mtmp : rk(P6 :: nil) >= 1) by (solve_hyps_min HP6eq HP6m1).
	assert(Hincl : incl (P6 :: nil) (list_inter (P1 :: P6 :: nil) (P2 :: P4 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P6 :: nil) (P1 :: P6 :: P2 :: P4 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P6 :: P2 :: P4 :: P6 :: nil) ((P1 :: P6 :: nil) ++ (P2 :: P4 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P6mtmp;try rewrite HT2 in HP1P2P4P6mtmp.
	assert(HT := rule_2 (P1 :: P6 :: nil) (P2 :: P4 :: P6 :: nil) (P6 :: nil) 3 1 2 HP1P2P4P6mtmp HP6mtmp HP2P4P6Mtmp Hincl);apply HT.
}
try clear HP1P6m1. try clear HP1P2P4P6M3. try clear HP1P2P4P6m3. 

assert(HP1P6P8m2 : rk(P1 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P6mtmp : rk(P1 :: P6 :: nil) >= 2) by (solve_hyps_min HP1P6eq HP1P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: nil) (P1 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: nil) (P1 :: P6 :: P8 :: nil) 2 2 HP1P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6P8m1. 

assert(HP1P6P8m3 : rk(P1 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP2P4P6P8Mtmp : rk(P2 :: P4 :: P6 :: P8 :: nil) <= 3) by (solve_hyps_max HP2P4P6P8eq HP2P4P6P8M3).
	assert(HP1P2P4P6P8mtmp : rk(P1 :: P2 :: P4 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P6P8eq HP1P2P4P6P8m4).
	assert(HP6P8mtmp : rk(P6 :: P8 :: nil) >= 2) by (solve_hyps_min HP6P8eq HP6P8m2).
	assert(Hincl : incl (P6 :: P8 :: nil) (list_inter (P1 :: P6 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P6 :: P8 :: nil) (P1 :: P6 :: P8 :: P2 :: P4 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P6 :: P8 :: P2 :: P4 :: P6 :: P8 :: nil) ((P1 :: P6 :: P8 :: nil) ++ (P2 :: P4 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P6P8mtmp;try rewrite HT2 in HP1P2P4P6P8mtmp.
	assert(HT := rule_2 (P1 :: P6 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: nil) (P6 :: P8 :: nil) 4 2 3 HP1P2P4P6P8mtmp HP6P8mtmp HP2P4P6P8Mtmp Hincl);apply HT.
}
try clear HP1P6P8m2. try clear HP1P2P4P6P8M4. try clear HP1P2P4P6P8m4. 

assert(HP1P6P7P8m2 : rk(P1 :: P6 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP1P6mtmp : rk(P1 :: P6 :: nil) >= 2) by (solve_hyps_min HP1P6eq HP1P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: nil) (P1 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: nil) (P1 :: P6 :: P7 :: P8 :: nil) 2 2 HP1P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6P7P8m1. 

assert(HP1P6P7P8M3 : rk(P1 :: P6 :: P7 :: P8 :: nil) <= 3).
{
	assert(HP1P6P7Mtmp : rk(P1 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P6P7eq HP1P6P7M2).
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P6 :: P7 :: nil) (P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P6 :: P7 :: P8 :: nil) (P1 :: P6 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P6 :: P7 :: P8 :: nil) ((P1 :: P6 :: P7 :: nil) ++ (P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P6 :: P7 :: nil) (P8 :: nil) (nil) 2 1 0 HP1P6P7Mtmp HP8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P6P7P8M4. 

assert(HP1P6P7P8m3 : rk(P1 :: P6 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P6P8mtmp : rk(P1 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P6P8eq HP1P6P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: P8 :: nil) (P1 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: P8 :: nil) (P1 :: P6 :: P7 :: P8 :: nil) 3 3 HP1P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6P7P8m2. 

assert(HP2P7P8m2 : rk(P2 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP2P7mtmp : rk(P2 :: P7 :: nil) >= 2) by (solve_hyps_min HP2P7eq HP2P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: nil) (P2 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: nil) (P2 :: P7 :: P8 :: nil) 2 2 HP2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P8m1. 

assert(HP2P7P8m3 : rk(P2 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P6P7P8Mtmp : rk(P1 :: P6 :: P7 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P6P7P8eq HP1P6P7P8M3).
	assert(HP1P2P6P7P8mtmp : rk(P1 :: P2 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P6P7P8eq HP1P2P6P7P8m4).
	assert(HP7P8mtmp : rk(P7 :: P8 :: nil) >= 2) by (solve_hyps_min HP7P8eq HP7P8m2).
	assert(Hincl : incl (P7 :: P8 :: nil) (list_inter (P2 :: P7 :: P8 :: nil) (P1 :: P6 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P6 :: P7 :: P8 :: nil) (P2 :: P7 :: P8 :: P1 :: P6 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P7 :: P8 :: P1 :: P6 :: P7 :: P8 :: nil) ((P2 :: P7 :: P8 :: nil) ++ (P1 :: P6 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P6P7P8mtmp;try rewrite HT2 in HP1P2P6P7P8mtmp.
	assert(HT := rule_2 (P2 :: P7 :: P8 :: nil) (P1 :: P6 :: P7 :: P8 :: nil) (P7 :: P8 :: nil) 4 2 3 HP1P2P6P7P8mtmp HP7P8mtmp HP1P6P7P8Mtmp Hincl);apply HT.
}
try clear HP2P7P8m2. try clear HP1P2P6P7P8M4. try clear HP1P2P6P7P8m4. 

assert(HP1P2P7m2 : rk(P1 :: P2 :: P7 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7m1. 

assert(HP1P2P7m3 : rk(P1 :: P2 :: P7 :: nil) >= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP1P2P5P7mtmp : rk(P1 :: P2 :: P5 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P5P7eq HP1P2P5P7m3).
	assert(HP2P7mtmp : rk(P2 :: P7 :: nil) >= 2) by (solve_hyps_min HP2P7eq HP2P7m2).
	assert(Hincl : incl (P2 :: P7 :: nil) (list_inter (P1 :: P2 :: P7 :: nil) (P2 :: P5 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P7 :: nil) (P1 :: P2 :: P7 :: P2 :: P5 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P7 :: P2 :: P5 :: P7 :: nil) ((P1 :: P2 :: P7 :: nil) ++ (P2 :: P5 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P7mtmp;try rewrite HT2 in HP1P2P5P7mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P7 :: nil) (P2 :: P5 :: P7 :: nil) (P2 :: P7 :: nil) 3 2 2 HP1P2P5P7mtmp HP2P7mtmp HP2P5P7Mtmp Hincl);apply HT.
}
try clear HP1P2P7m2. 

assert(HP1P2P7P8m2 : rk(P1 :: P2 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8m1. 

assert(HP1P2P7P8m3 : rk(P1 :: P2 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8m2. 

assert(HP1P2P7P8m4 : rk(P1 :: P2 :: P7 :: P8 :: nil) >= 4).
{
	assert(HP2P5P7P8Mtmp : rk(P2 :: P5 :: P7 :: P8 :: nil) <= 3) by (solve_hyps_max HP2P5P7P8eq HP2P5P7P8M3).
	assert(HP1P2P5P7P8mtmp : rk(P1 :: P2 :: P5 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P5P7P8eq HP1P2P5P7P8m4).
	assert(HP2P7P8mtmp : rk(P2 :: P7 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P7P8eq HP2P7P8m3).
	assert(Hincl : incl (P2 :: P7 :: P8 :: nil) (list_inter (P1 :: P2 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P7 :: P8 :: nil) (P1 :: P2 :: P7 :: P8 :: P2 :: P5 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P7 :: P8 :: P2 :: P5 :: P7 :: P8 :: nil) ((P1 :: P2 :: P7 :: P8 :: nil) ++ (P2 :: P5 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P7P8mtmp;try rewrite HT2 in HP1P2P5P7P8mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P8 :: nil) (P2 :: P7 :: P8 :: nil) 4 3 3 HP1P2P5P7P8mtmp HP2P7P8mtmp HP2P5P7P8Mtmp Hincl);apply HT.
}
try clear HP1P2P7P8m3. try clear HP2P7P8M3. try clear HP2P7P8m3. 

assert(HP1P2P7P8P12P14m2 : rk(P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P12P14m1. 

assert(HP1P2P7P8P12P14m3 : rk(P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P12P14m2. 

assert(HP1P2P7P8P12P14m4 : rk(P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil) >= 4).
{
	assert(HP1P2P7P8mtmp : rk(P1 :: P2 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8eq HP1P2P7P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: P8 :: nil) (P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: P8 :: nil) (P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil) 4 4 HP1P2P7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P12P14m3. 

assert(HP7P8P12P14m2 : rk(P7 :: P8 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP7P8mtmp : rk(P7 :: P8 :: nil) >= 2) by (solve_hyps_min HP7P8eq HP7P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P7 :: P8 :: nil) (P7 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P8 :: nil) (P7 :: P8 :: P12 :: P14 :: nil) 2 2 HP7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP7P8P12P14m1. 

assert(HP7P8P12P14m3 : rk(P7 :: P8 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P2P12Mtmp : rk(P1 :: P2 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P2P12eq HP1P2P12M2).
	assert(HP1P2P7P8P12P14mtmp : rk(P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8P12P14eq HP1P2P7P8P12P14m4).
	assert(HP12mtmp : rk(P12 :: nil) >= 1) by (solve_hyps_min HP12eq HP12m1).
	assert(Hincl : incl (P12 :: nil) (list_inter (P1 :: P2 :: P12 :: nil) (P7 :: P8 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P8 :: P12 :: P14 :: nil) (P1 :: P2 :: P12 :: P7 :: P8 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P12 :: P7 :: P8 :: P12 :: P14 :: nil) ((P1 :: P2 :: P12 :: nil) ++ (P7 :: P8 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P8P12P14mtmp;try rewrite HT2 in HP1P2P7P8P12P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P12 :: nil) (P7 :: P8 :: P12 :: P14 :: nil) (P12 :: nil) 4 1 2 HP1P2P7P8P12P14mtmp HP12mtmp HP1P2P12Mtmp Hincl); apply HT.
}
try clear HP7P8P12P14m2. try clear HP1P2P7P8P12P14M4. try clear HP1P2P7P8P12P14m4. 

assert(HP7P8P12P14M3 : rk(P7 :: P8 :: P12 :: P14 :: nil) <= 3).
{
	assert(HP4P7P8P12P14Mtmp : rk(P4 :: P7 :: P8 :: P12 :: P14 :: nil) <= 3) by (solve_hyps_max HP4P7P8P12P14eq HP4P7P8P12P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P7 :: P8 :: P12 :: P14 :: nil) (P4 :: P7 :: P8 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P7 :: P8 :: P12 :: P14 :: nil) (P4 :: P7 :: P8 :: P12 :: P14 :: nil) 3 3 HP4P7P8P12P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP7P8P12P14M4. try clear HP4P7P8P12P14M3. try clear HP4P7P8P12P14m3. 

assert(HP1P2P5P8P9m2 : rk(P1 :: P2 :: P5 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P8 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P8P9m1. 

assert(HP1P2P5P8P9m3 : rk(P1 :: P2 :: P5 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P8 :: P9 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P8P9m2. 

assert(HP1P2P5P8P9m4 : rk(P1 :: P2 :: P5 :: P8 :: P9 :: nil) >= 4).
{
	assert(HP1P2P5P8mtmp : rk(P1 :: P2 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P5P8eq HP1P2P5P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P5 :: P8 :: P9 :: nil) 4 4 HP1P2P5P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P8P9m3. 

assert(HP2P5P9m2 : rk(P2 :: P5 :: P9 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P9 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P9m1. 

assert(HP2P5P9m3 : rk(P2 :: P5 :: P9 :: nil) >= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P2P5P8P9mtmp : rk(P1 :: P2 :: P5 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P5P8P9eq HP1P2P5P8P9m4).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P2 :: P5 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P8 :: P9 :: nil) (P2 :: P5 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P9 :: P1 :: P8 :: P9 :: nil) ((P2 :: P5 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P8P9mtmp;try rewrite HT2 in HP1P2P5P8P9mtmp.
	assert(HT := rule_2 (P2 :: P5 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P9 :: nil) 4 1 2 HP1P2P5P8P9mtmp HP9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP2P5P9m2. try clear HP1P2P5P8P9M4. try clear HP1P2P5P8P9m4. 

assert(HP2P5P7P9P14m2 : rk(P2 :: P5 :: P7 :: P9 :: P14 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P9 :: P14 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P7P9P14m1. 

assert(HP2P5P7P9P14M3 : rk(P2 :: P5 :: P7 :: P9 :: P14 :: nil) <= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m1).
	assert(Hincl : incl (P5 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P7 :: P9 :: P14 :: nil) (P2 :: P5 :: P7 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P5 :: P9 :: P14 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P5 :: P7 :: nil) (P5 :: P9 :: P14 :: nil) (P5 :: nil) 2 2 1 HP2P5P7Mtmp HP5P9P14Mtmp HP5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P5P7P9P14M4. 

assert(HP2P5P7P9P14m3 : rk(P2 :: P5 :: P7 :: P9 :: P14 :: nil) >= 3).
{
	assert(HP2P5P9mtmp : rk(P2 :: P5 :: P9 :: nil) >= 3) by (solve_hyps_min HP2P5P9eq HP2P5P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: P9 :: nil) (P2 :: P5 :: P7 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: P9 :: nil) (P2 :: P5 :: P7 :: P9 :: P14 :: nil) 3 3 HP2P5P9mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P7P9P14m2. 

assert(HP1P2P7P8P9m2 : rk(P1 :: P2 :: P7 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P9m1. 

assert(HP1P2P7P8P9m3 : rk(P1 :: P2 :: P7 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: P9 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P9m2. 

assert(HP1P2P7P8P9m4 : rk(P1 :: P2 :: P7 :: P8 :: P9 :: nil) >= 4).
{
	assert(HP1P2P7P8mtmp : rk(P1 :: P2 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8eq HP1P2P7P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: P8 :: nil) (P1 :: P2 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: P8 :: nil) (P1 :: P2 :: P7 :: P8 :: P9 :: nil) 4 4 HP1P2P7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P9m3. 

assert(HP2P7P9m2 : rk(P2 :: P7 :: P9 :: nil) >= 2).
{
	assert(HP2P7mtmp : rk(P2 :: P7 :: nil) >= 2) by (solve_hyps_min HP2P7eq HP2P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: nil) (P2 :: P7 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: nil) (P2 :: P7 :: P9 :: nil) 2 2 HP2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P9m1. 

assert(HP2P7P9m3 : rk(P2 :: P7 :: P9 :: nil) >= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P2P7P8P9mtmp : rk(P1 :: P2 :: P7 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8P9eq HP1P2P7P8P9m4).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P2 :: P7 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P8 :: P9 :: nil) (P2 :: P7 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P7 :: P9 :: P1 :: P8 :: P9 :: nil) ((P2 :: P7 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P8P9mtmp;try rewrite HT2 in HP1P2P7P8P9mtmp.
	assert(HT := rule_2 (P2 :: P7 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P9 :: nil) 4 1 2 HP1P2P7P8P9mtmp HP9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP2P7P9m2. 

assert(HP2P7P9P14m2 : rk(P2 :: P7 :: P9 :: P14 :: nil) >= 2).
{
	assert(HP2P7mtmp : rk(P2 :: P7 :: nil) >= 2) by (solve_hyps_min HP2P7eq HP2P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: nil) (P2 :: P7 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: nil) (P2 :: P7 :: P9 :: P14 :: nil) 2 2 HP2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P9P14m1. 

assert(HP2P7P9P14m3 : rk(P2 :: P7 :: P9 :: P14 :: nil) >= 3).
{
	assert(HP2P7P9mtmp : rk(P2 :: P7 :: P9 :: nil) >= 3) by (solve_hyps_min HP2P7P9eq HP2P7P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: P9 :: nil) (P2 :: P7 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: P9 :: nil) (P2 :: P7 :: P9 :: P14 :: nil) 3 3 HP2P7P9mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P9P14m2. 

assert(HP2P7P9P14M3 : rk(P2 :: P7 :: P9 :: P14 :: nil) <= 3).
{
	assert(HP2P5P7P9P14Mtmp : rk(P2 :: P5 :: P7 :: P9 :: P14 :: nil) <= 3) by (solve_hyps_max HP2P5P7P9P14eq HP2P5P7P9P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: P9 :: P14 :: nil) (P2 :: P5 :: P7 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P2 :: P7 :: P9 :: P14 :: nil) (P2 :: P5 :: P7 :: P9 :: P14 :: nil) 3 3 HP2P5P7P9P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P9P14M4. try clear HP2P5P7P9P14M3. try clear HP2P5P7P9P14m3. 

assert(HP1P2P4P8P9P11P14m2 : rk(P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P9P11P14m1. 

assert(HP1P2P4P8P9P11P14m3 : rk(P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P9P11P14m2. 

assert(HP1P2P4P8P9P11P14m4 : rk(P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P9P11P14m3. 

assert(HP8P9m2 : rk(P8 :: P9 :: nil) >= 2).
{
	assert(HP10Mtmp : rk(P10 :: nil) <= 1) by (solve_hyps_max HP10eq HP10M1).
	assert(HP8P9P10mtmp : rk(P8 :: P9 :: P10 :: nil) >= 3) by (solve_hyps_min HP8P9P10eq HP8P9P10m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P8 :: P9 :: nil) (P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P8 :: P9 :: P10 :: nil) (P8 :: P9 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P9 :: P10 :: nil) ((P8 :: P9 :: nil) ++ (P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP8P9P10mtmp;try rewrite HT2 in HP8P9P10mtmp.
	assert(HT := rule_2 (P8 :: P9 :: nil) (P10 :: nil) (nil) 3 0 1 HP8P9P10mtmp Hmtmp HP10Mtmp Hincl);apply HT.
}
try clear HP8P9m1. 

assert(HP2P4P8P9P11P14m2 : rk(P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P8P9P11P14m1. 

assert(HP2P4P8P9P11P14m3 : rk(P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP2P4P8mtmp : rk(P2 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P4P8eq HP2P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) 3 3 HP2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P8P9P11P14m2. 

assert(HP2P4P8P9P11P14m4 : rk(P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) >= 4).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P2P4P8P9P11P14mtmp : rk(P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8P9P11P14eq HP1P2P4P8P9P11P14m4).
	assert(HP8P9mtmp : rk(P8 :: P9 :: nil) >= 2) by (solve_hyps_min HP8P9eq HP8P9m2).
	assert(Hincl : incl (P8 :: P9 :: nil) (list_inter (P1 :: P8 :: P9 :: nil) (P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) (P1 :: P8 :: P9 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P9 :: P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) ((P1 :: P8 :: P9 :: nil) ++ (P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8P9P11P14mtmp;try rewrite HT2 in HP1P2P4P8P9P11P14mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P9 :: nil) (P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) (P8 :: P9 :: nil) 4 2 2 HP1P2P4P8P9P11P14mtmp HP8P9mtmp HP1P8P9Mtmp Hincl); apply HT.
}
try clear HP2P4P8P9P11P14m3. try clear HP1P2P4P8P9P11P14M4. try clear HP1P2P4P8P9P11P14m4. 

assert(HP2P5P9P14M3 : rk(P2 :: P5 :: P9 :: P14 :: nil) <= 3).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P9 :: P14 :: nil) (P2 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P9 :: P14 :: nil) ((P2 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: nil) (P5 :: P9 :: P14 :: nil) (nil) 1 2 0 HP2Mtmp HP5P9P14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P5P9P14M4. 

assert(HP2P5P9P14m2 : rk(P2 :: P5 :: P9 :: P14 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P9 :: P14 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P9P14m1. 

assert(HP2P5P9P14m3 : rk(P2 :: P5 :: P9 :: P14 :: nil) >= 3).
{
	assert(HP2P5P9mtmp : rk(P2 :: P5 :: P9 :: nil) >= 3) by (solve_hyps_min HP2P5P9eq HP2P5P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: P9 :: nil) (P2 :: P5 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: P9 :: nil) (P2 :: P5 :: P9 :: P14 :: nil) 3 3 HP2P5P9mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5P9M3. try clear HP2P5P9m3. try clear HP2P5P9P14m2. 

assert(HP2P14m2 : rk(P2 :: P14 :: nil) >= 2).
{
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(HP2P5P9P14mtmp : rk(P2 :: P5 :: P9 :: P14 :: nil) >= 3) by (solve_hyps_min HP2P5P9P14eq HP2P5P9P14m3).
	assert(HP14mtmp : rk(P14 :: nil) >= 1) by (solve_hyps_min HP14eq HP14m1).
	assert(Hincl : incl (P14 :: nil) (list_inter (P2 :: P14 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P9 :: P14 :: nil) (P2 :: P14 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P14 :: P5 :: P9 :: P14 :: nil) ((P2 :: P14 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P5P9P14mtmp;try rewrite HT2 in HP2P5P9P14mtmp.
	assert(HT := rule_2 (P2 :: P14 :: nil) (P5 :: P9 :: P14 :: nil) (P14 :: nil) 3 1 2 HP2P5P9P14mtmp HP14mtmp HP5P9P14Mtmp Hincl);apply HT.
}
try clear HP2P14m1. 

assert(HP2P4P8P10M3 : rk(P2 :: P4 :: P8 :: P10 :: nil) <= 3).
{
	assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M1).
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P8 :: P10 :: nil) (P4 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P2 :: P8 :: P10 :: nil) ((P4 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: nil) (P2 :: P8 :: P10 :: nil) (nil) 1 2 0 HP4Mtmp HP2P8P10Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P4P8P10M4. 

assert(HP2P4P8P10m2 : rk(P2 :: P4 :: P8 :: P10 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P8 :: P10 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P8P10m1. 

assert(HP2P4P8P10m3 : rk(P2 :: P4 :: P8 :: P10 :: nil) >= 3).
{
	assert(HP2P4P8mtmp : rk(P2 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P4P8eq HP2P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P8 :: P10 :: nil) 3 3 HP2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P8P10m2. 

assert(HP1P2P3P9P10m2 : rk(P1 :: P2 :: P3 :: P9 :: P10 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P10m1. 

assert(HP1P2P3P9P10M3 : rk(P1 :: P2 :: P3 :: P9 :: P10 :: nil) <= 3).
{
	assert(HP1P2P3Mtmp : rk(P1 :: P2 :: P3 :: nil) <= 2) by (solve_hyps_max HP1P2P3eq HP1P2P3M2).
	assert(HP3P9P10Mtmp : rk(P3 :: P9 :: P10 :: nil) <= 2) by (solve_hyps_max HP3P9P10eq HP3P9P10M2).
	assert(HP3mtmp : rk(P3 :: nil) >= 1) by (solve_hyps_min HP3eq HP3m1).
	assert(Hincl : incl (P3 :: nil) (list_inter (P1 :: P2 :: P3 :: nil) (P3 :: P9 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P9 :: P10 :: nil) (P1 :: P2 :: P3 :: P3 :: P9 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P3 :: P9 :: P10 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P3 :: P9 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: nil) (P3 :: P9 :: P10 :: nil) (P3 :: nil) 2 2 1 HP1P2P3Mtmp HP3P9P10Mtmp HP3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3M1. try clear HP3m1. try clear HP1P2P3P9P10M4. 

assert(HP1P2P3P9P10m3 : rk(P1 :: P2 :: P3 :: P9 :: P10 :: nil) >= 3).
{
	assert(HP1P2P9mtmp : rk(P1 :: P2 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P2P9eq HP1P2P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P9 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P9 :: nil) (P1 :: P2 :: P3 :: P9 :: P10 :: nil) 3 3 HP1P2P9mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P10m2. 

assert(HP1P2P3P9P12P13m2 : rk(P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P12P13m1. 

assert(HP1P2P3P9P12P13M3 : rk(P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil) <= 3).
{
	assert(HP9Mtmp : rk(P9 :: nil) <= 1) by (solve_hyps_max HP9eq HP9M1).
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P9 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil) (P9 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P9 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P9 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P9 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (nil) 1 2 0 HP9Mtmp HP1P2P3P12P13Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P9P12P13M4. 

assert(HP1P2P3P9P12P13m3 : rk(P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P9mtmp : rk(P1 :: P2 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P2P9eq HP1P2P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P9 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P9 :: nil) (P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil) 3 3 HP1P2P9mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9P12P13m2. 

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
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(HP1P2P3P9P12P13mtmp : rk(P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P3P9P12P13eq HP1P2P3P9P12P13m3).
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hincl : incl (P2 :: P3 :: nil) (list_inter (P2 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P9 :: P12 :: P13 :: nil) (P2 :: P3 :: P9 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P9 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P2 :: P3 :: P9 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P9P12P13mtmp;try rewrite HT2 in HP1P2P3P9P12P13mtmp.
	assert(HT := rule_2 (P2 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (P2 :: P3 :: nil) 3 2 2 HP1P2P3P9P12P13mtmp HP2P3mtmp HP1P2P3P12P13Mtmp Hincl);apply HT.
}
try clear HP2P3P9m2. try clear HP1P2P3P9P12P13M3. try clear HP1P2P3P9P12P13m3. 

assert(HP1P2P3P9m2 : rk(P1 :: P2 :: P3 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9m1. 

assert(HP1P2P3P9M3 : rk(P1 :: P2 :: P3 :: P9 :: nil) <= 3).
{
	assert(HP1P2P3Mtmp : rk(P1 :: P2 :: P3 :: nil) <= 2) by (solve_hyps_max HP1P2P3eq HP1P2P3M2).
	assert(HP9Mtmp : rk(P9 :: nil) <= 1) by (solve_hyps_max HP9eq HP9M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: P3 :: nil) (P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P9 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: nil) (P9 :: nil) (nil) 2 1 0 HP1P2P3Mtmp HP9Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3M2. try clear HP1P2P3m2. try clear HP1P2P3P9M4. 

assert(HP1P2P3P9m3 : rk(P1 :: P2 :: P3 :: P9 :: nil) >= 3).
{
	assert(HP1P2P9mtmp : rk(P1 :: P2 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P2P9eq HP1P2P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P9 :: nil) (P1 :: P2 :: P3 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P9 :: nil) (P1 :: P2 :: P3 :: P9 :: nil) 3 3 HP1P2P9mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P9m2. 

assert(HP2P3P9P10M3 : rk(P2 :: P3 :: P9 :: P10 :: nil) <= 3).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP3P9P10Mtmp : rk(P3 :: P9 :: P10 :: nil) <= 2) by (solve_hyps_max HP3P9P10eq HP3P9P10M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P3 :: P9 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P9 :: P10 :: nil) (P2 :: P3 :: P9 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P9 :: P10 :: nil) ((P2 :: nil) ++ (P3 :: P9 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: nil) (P3 :: P9 :: P10 :: nil) (nil) 1 2 0 HP2Mtmp HP3P9P10Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P3P9P10M4. 

assert(HP2P3P9P10m2 : rk(P2 :: P3 :: P9 :: P10 :: nil) >= 2).
{
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P9 :: P10 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3M2. try clear HP2P3m2. try clear HP2P3P9P10m1. 

assert(HP2P3P9P10m3 : rk(P2 :: P3 :: P9 :: P10 :: nil) >= 3).
{
	assert(HP1P2P3P9Mtmp : rk(P1 :: P2 :: P3 :: P9 :: nil) <= 3) by (solve_hyps_max HP1P2P3P9eq HP1P2P3P9M3).
	assert(HP1P2P3P9P10mtmp : rk(P1 :: P2 :: P3 :: P9 :: P10 :: nil) >= 3) by (solve_hyps_min HP1P2P3P9P10eq HP1P2P3P9P10m3).
	assert(HP2P3P9mtmp : rk(P2 :: P3 :: P9 :: nil) >= 3) by (solve_hyps_min HP2P3P9eq HP2P3P9m3).
	assert(Hincl : incl (P2 :: P3 :: P9 :: nil) (list_inter (P1 :: P2 :: P3 :: P9 :: nil) (P2 :: P3 :: P9 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P9 :: P10 :: nil) (P1 :: P2 :: P3 :: P9 :: P2 :: P3 :: P9 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P9 :: P2 :: P3 :: P9 :: P10 :: nil) ((P1 :: P2 :: P3 :: P9 :: nil) ++ (P2 :: P3 :: P9 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P9P10mtmp;try rewrite HT2 in HP1P2P3P9P10mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P9 :: nil) (P2 :: P3 :: P9 :: P10 :: nil) (P2 :: P3 :: P9 :: nil) 3 3 3 HP1P2P3P9P10mtmp HP2P3P9mtmp HP1P2P3P9Mtmp Hincl); apply HT.
}
try clear HP1P2P3P9M3. try clear HP1P2P3P9m3. try clear HP2P3P9P10m2. try clear HP2P3P9M3. try clear HP2P3P9m3. try clear HP1P2P3P9P10M3. try clear HP1P2P3P9P10m3. 

assert(HP2P10m2 : rk(P2 :: P10 :: nil) >= 2).
{
	assert(HP3P9P10Mtmp : rk(P3 :: P9 :: P10 :: nil) <= 2) by (solve_hyps_max HP3P9P10eq HP3P9P10M2).
	assert(HP2P3P9P10mtmp : rk(P2 :: P3 :: P9 :: P10 :: nil) >= 3) by (solve_hyps_min HP2P3P9P10eq HP2P3P9P10m3).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P2 :: P10 :: nil) (P3 :: P9 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P9 :: P10 :: nil) (P2 :: P10 :: P3 :: P9 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P10 :: P3 :: P9 :: P10 :: nil) ((P2 :: P10 :: nil) ++ (P3 :: P9 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P9P10mtmp;try rewrite HT2 in HP2P3P9P10mtmp.
	assert(HT := rule_2 (P2 :: P10 :: nil) (P3 :: P9 :: P10 :: nil) (P10 :: nil) 3 1 2 HP2P3P9P10mtmp HP10mtmp HP3P9P10Mtmp Hincl);apply HT.
}
try clear HP2P10m1. try clear HP3P9P10M2. try clear HP3P9P10m2. try clear HP2P3P9P10M3. try clear HP2P3P9P10m3. 

assert(HP2P4P10m2 : rk(P2 :: P4 :: P10 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P10 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P10m1. 

assert(HP2P4P10m3 : rk(P2 :: P4 :: P10 :: nil) >= 3).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP2P4P8P10mtmp : rk(P2 :: P4 :: P8 :: P10 :: nil) >= 3) by (solve_hyps_min HP2P4P8P10eq HP2P4P8P10m3).
	assert(HP2P10mtmp : rk(P2 :: P10 :: nil) >= 2) by (solve_hyps_min HP2P10eq HP2P10m2).
	assert(Hincl : incl (P2 :: P10 :: nil) (list_inter (P2 :: P4 :: P10 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P8 :: P10 :: nil) (P2 :: P4 :: P10 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P10 :: P2 :: P8 :: P10 :: nil) ((P2 :: P4 :: P10 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P8P10mtmp;try rewrite HT2 in HP2P4P8P10mtmp.
	assert(HT := rule_2 (P2 :: P4 :: P10 :: nil) (P2 :: P8 :: P10 :: nil) (P2 :: P10 :: nil) 3 2 2 HP2P4P8P10mtmp HP2P10mtmp HP2P8P10Mtmp Hincl);apply HT.
}
try clear HP2P4P10m2. try clear HP2P4P8P10M3. try clear HP2P4P8P10m3. 

assert(HP2P4P6P10P14m2 : rk(P2 :: P4 :: P6 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P10 :: P14 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P6P10P14m1. 

assert(HP2P4P6P10P14M3 : rk(P2 :: P4 :: P6 :: P10 :: P14 :: nil) <= 3).
{
	assert(HP2P4P6Mtmp : rk(P2 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP2P4P6eq HP2P4P6M2).
	assert(HP6P10P14Mtmp : rk(P6 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP6P10P14eq HP6P10P14M2).
	assert(HP6mtmp : rk(P6 :: nil) >= 1) by (solve_hyps_min HP6eq HP6m1).
	assert(Hincl : incl (P6 :: nil) (list_inter (P2 :: P4 :: P6 :: nil) (P6 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P6 :: P10 :: P14 :: nil) (P2 :: P4 :: P6 :: P6 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P6 :: P6 :: P10 :: P14 :: nil) ((P2 :: P4 :: P6 :: nil) ++ (P6 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P4 :: P6 :: nil) (P6 :: P10 :: P14 :: nil) (P6 :: nil) 2 2 1 HP2P4P6Mtmp HP6P10P14Mtmp HP6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P4P6P10P14M4. 

assert(HP2P4P6P10P14m3 : rk(P2 :: P4 :: P6 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP2P4P10mtmp : rk(P2 :: P4 :: P10 :: nil) >= 3) by (solve_hyps_min HP2P4P10eq HP2P4P10m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P10 :: nil) (P2 :: P4 :: P6 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: P10 :: nil) (P2 :: P4 :: P6 :: P10 :: P14 :: nil) 3 3 HP2P4P10mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P10M3. try clear HP2P4P10m3. try clear HP2P4P6P10P14m2. 

assert(HP2P4P6P8P10P14m2 : rk(P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P6P8P10P14m1. 

assert(HP2P4P6P8P10P14m3 : rk(P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP2P4P8mtmp : rk(P2 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P4P8eq HP2P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) 3 3 HP2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P6P8P10P14m2. 

assert(HP2P4P6P8P10P14M3 : rk(P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) <= 3).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP2P4P6P10P14Mtmp : rk(P2 :: P4 :: P6 :: P10 :: P14 :: nil) <= 3) by (solve_hyps_max HP2P4P6P10P14eq HP2P4P6P10P14M3).
	assert(HP2P10mtmp : rk(P2 :: P10 :: nil) >= 2) by (solve_hyps_min HP2P10eq HP2P10m2).
	assert(Hincl : incl (P2 :: P10 :: nil) (list_inter (P2 :: P8 :: P10 :: nil) (P2 :: P4 :: P6 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) (P2 :: P8 :: P10 :: P2 :: P4 :: P6 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P8 :: P10 :: P2 :: P4 :: P6 :: P10 :: P14 :: nil) ((P2 :: P8 :: P10 :: nil) ++ (P2 :: P4 :: P6 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P8 :: P10 :: nil) (P2 :: P4 :: P6 :: P10 :: P14 :: nil) (P2 :: P10 :: nil) 2 3 2 HP2P8P10Mtmp HP2P4P6P10P14Mtmp HP2P10mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P4P6P10P14M3. try clear HP2P4P6P10P14m3. try clear HP2P4P6P8P10P14M4. 

assert(HP2P4P8P14m2 : rk(P2 :: P4 :: P8 :: P14 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P8 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P8 :: P14 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P8P14m1. 

assert(HP2P4P8P14m3 : rk(P2 :: P4 :: P8 :: P14 :: nil) >= 3).
{
	assert(HP2P4P8mtmp : rk(P2 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P4P8eq HP2P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P8 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: P8 :: nil) (P2 :: P4 :: P8 :: P14 :: nil) 3 3 HP2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P8M3. try clear HP2P4P8m3. try clear HP2P4P8P14m2. 

assert(HP2P4P8P14M3 : rk(P2 :: P4 :: P8 :: P14 :: nil) <= 3).
{
	assert(HP2P4P6P8P10P14Mtmp : rk(P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) <= 3) by (solve_hyps_max HP2P4P6P8P10P14eq HP2P4P6P8P10P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: P8 :: P14 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P2 :: P4 :: P8 :: P14 :: nil) (P2 :: P4 :: P6 :: P8 :: P10 :: P14 :: nil) 3 3 HP2P4P6P8P10P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P8P14M4. try clear HP2P4P6P8P10P14M3. try clear HP2P4P6P8P10P14m3. 

assert(HP2P9m2 : rk(P2 :: P9 :: nil) >= 2).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP1P2P9mtmp : rk(P1 :: P2 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P2P9eq HP1P2P9m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P9 :: nil) (P1 :: P2 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P9 :: nil) ((P1 :: nil) ++ (P2 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P9mtmp;try rewrite HT2 in HP1P2P9mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P9 :: nil) (nil) 3 0 1 HP1P2P9mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}
try clear HP2P9m1. 

assert(HP2P9P11P14m2 : rk(P2 :: P9 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP2P9mtmp : rk(P2 :: P9 :: nil) >= 2) by (solve_hyps_min HP2P9eq HP2P9m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P9 :: nil) (P2 :: P9 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P9 :: nil) (P2 :: P9 :: P11 :: P14 :: nil) 2 2 HP2P9mtmp Hcomp Hincl);apply HT.
}
try clear HP2P9P11P14m1. 

assert(HP2P9P11P14M3 : rk(P2 :: P9 :: P11 :: P14 :: nil) <= 3).
{
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(HP14Mtmp : rk(P14 :: nil) <= 1) by (solve_hyps_max HP14eq HP14M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: P9 :: P11 :: nil) (P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P9 :: P11 :: P14 :: nil) (P2 :: P9 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P11 :: P14 :: nil) ((P2 :: P9 :: P11 :: nil) ++ (P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P9 :: P11 :: nil) (P14 :: nil) (nil) 2 1 0 HP2P9P11Mtmp HP14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P9P11P14M4. 

assert(HP2P9P11P14m3 : rk(P2 :: P9 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP2P4P8P14Mtmp : rk(P2 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP2P4P8P14eq HP2P4P8P14M3).
	assert(HP2P4P8P9P11P14mtmp : rk(P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) >= 4) by (solve_hyps_min HP2P4P8P9P11P14eq HP2P4P8P9P11P14m4).
	assert(HP2P14mtmp : rk(P2 :: P14 :: nil) >= 2) by (solve_hyps_min HP2P14eq HP2P14m2).
	assert(Hincl : incl (P2 :: P14 :: nil) (list_inter (P2 :: P4 :: P8 :: P14 :: nil) (P2 :: P9 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P8 :: P9 :: P11 :: P14 :: nil) (P2 :: P4 :: P8 :: P14 :: P2 :: P9 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P8 :: P14 :: P2 :: P9 :: P11 :: P14 :: nil) ((P2 :: P4 :: P8 :: P14 :: nil) ++ (P2 :: P9 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P8P9P11P14mtmp;try rewrite HT2 in HP2P4P8P9P11P14mtmp.
	assert(HT := rule_4 (P2 :: P4 :: P8 :: P14 :: nil) (P2 :: P9 :: P11 :: P14 :: nil) (P2 :: P14 :: nil) 4 2 3 HP2P4P8P9P11P14mtmp HP2P14mtmp HP2P4P8P14Mtmp Hincl); apply HT.
}
try clear HP2P4P8P14M3. try clear HP2P4P8P14m3. try clear HP2P9P11P14m2. try clear HP2P14M2. try clear HP2P14m2. try clear HP2P4P8P9P11P14M4. try clear HP2P4P8P9P11P14m4. 

assert(HP1P2P6P8P9P10P14m2 : rk(P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P8P9P10P14m1. 

assert(HP1P2P6P8P9P10P14m3 : rk(P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P2P6mtmp : rk(P1 :: P2 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P6eq HP1P2P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) 3 3 HP1P2P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P8P9P10P14m2. 

assert(HP1P2P6P8P9P10P14m4 : rk(P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) >= 4).
{
	assert(HP1P2P6P8mtmp : rk(P1 :: P2 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P6P8eq HP1P2P6P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: P8 :: nil) (P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: P8 :: nil) (P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) 4 4 HP1P2P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P8P9P10P14m3. 

assert(HP2P6P8P9P10P14m2 : rk(P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP2P6mtmp : rk(P2 :: P6 :: nil) >= 2) by (solve_hyps_min HP2P6eq HP2P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P6 :: nil) (P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P6 :: nil) (P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) 2 2 HP2P6mtmp Hcomp Hincl);apply HT.
}
try clear HP2P6M2. try clear HP2P6m2. try clear HP2P6P8P9P10P14m1. 

assert(HP2P6P8P9P10P14m3 : rk(P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP2P6P8mtmp : rk(P2 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P6P8eq HP2P6P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P6 :: P8 :: nil) (P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P6 :: P8 :: nil) (P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) 3 3 HP2P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P6P8M3. try clear HP2P6P8m3. try clear HP2P6P8P9P10P14m2. 

assert(HP2P6P8P9P10P14m4 : rk(P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) >= 4).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P2P6P8P9P10P14mtmp : rk(P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P6P8P9P10P14eq HP1P2P6P8P9P10P14m4).
	assert(HP8P9mtmp : rk(P8 :: P9 :: nil) >= 2) by (solve_hyps_min HP8P9eq HP8P9m2).
	assert(Hincl : incl (P8 :: P9 :: nil) (list_inter (P1 :: P8 :: P9 :: nil) (P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) (P1 :: P8 :: P9 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P9 :: P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) ((P1 :: P8 :: P9 :: nil) ++ (P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P6P8P9P10P14mtmp;try rewrite HT2 in HP1P2P6P8P9P10P14mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P9 :: nil) (P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) (P8 :: P9 :: nil) 4 2 2 HP1P2P6P8P9P10P14mtmp HP8P9mtmp HP1P8P9Mtmp Hincl); apply HT.
}
try clear HP2P6P8P9P10P14m3. try clear HP1P2P6P8P9P10P14M4. try clear HP1P2P6P8P9P10P14m4. 

assert(HP1P6P8P9M3 : rk(P1 :: P6 :: P8 :: P9 :: nil) <= 3).
{
	assert(HP6Mtmp : rk(P6 :: nil) <= 1) by (solve_hyps_max HP6eq HP6M1).
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P6 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P6 :: P8 :: P9 :: nil) (P6 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P1 :: P8 :: P9 :: nil) ((P6 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: nil) (P1 :: P8 :: P9 :: nil) (nil) 1 2 0 HP6Mtmp HP1P8P9Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P6P8P9M4. 

assert(HP1P6P8P9m2 : rk(P1 :: P6 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P6mtmp : rk(P1 :: P6 :: nil) >= 2) by (solve_hyps_min HP1P6eq HP1P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: nil) (P1 :: P6 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: nil) (P1 :: P6 :: P8 :: P9 :: nil) 2 2 HP1P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6P8P9m1. 

assert(HP1P6P8P9m3 : rk(P1 :: P6 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P6P8mtmp : rk(P1 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P6P8eq HP1P6P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: P8 :: nil) (P1 :: P6 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: P8 :: nil) (P1 :: P6 :: P8 :: P9 :: nil) 3 3 HP1P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6P8P9m2. 

assert(HP6P9m2 : rk(P6 :: P9 :: nil) >= 2).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P6P8P9mtmp : rk(P1 :: P6 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P6P8P9eq HP1P6P8P9m3).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P6 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P6 :: P8 :: P9 :: nil) (P6 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P9 :: P1 :: P8 :: P9 :: nil) ((P6 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P6P8P9mtmp;try rewrite HT2 in HP1P6P8P9mtmp.
	assert(HT := rule_2 (P6 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P9 :: nil) 3 1 2 HP1P6P8P9mtmp HP9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP6P9m1. try clear HP1P6P8P9M3. try clear HP1P6P8P9m3. 

assert(HP6P9P10P14M3 : rk(P6 :: P9 :: P10 :: P14 :: nil) <= 3).
{
	assert(HP9Mtmp : rk(P9 :: nil) <= 1) by (solve_hyps_max HP9eq HP9M1).
	assert(HP6P10P14Mtmp : rk(P6 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP6P10P14eq HP6P10P14M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P9 :: nil) (P6 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P9 :: P10 :: P14 :: nil) (P9 :: P6 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P9 :: P6 :: P10 :: P14 :: nil) ((P9 :: nil) ++ (P6 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P9 :: nil) (P6 :: P10 :: P14 :: nil) (nil) 1 2 0 HP9Mtmp HP6P10P14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP6P9P10P14M4. 

assert(HP6P9P10P14m2 : rk(P6 :: P9 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP6P9mtmp : rk(P6 :: P9 :: nil) >= 2) by (solve_hyps_min HP6P9eq HP6P9m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P6 :: P9 :: nil) (P6 :: P9 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P6 :: P9 :: nil) (P6 :: P9 :: P10 :: P14 :: nil) 2 2 HP6P9mtmp Hcomp Hincl);apply HT.
}
try clear HP6P9M2. try clear HP6P9m2. try clear HP6P9P10P14m1. 

assert(HP6P9P10P14m3 : rk(P6 :: P9 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP2P6P8P9P10P14mtmp : rk(P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) >= 4) by (solve_hyps_min HP2P6P8P9P10P14eq HP2P6P8P9P10P14m4).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P2 :: P8 :: P10 :: nil) (P6 :: P9 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P6 :: P8 :: P9 :: P10 :: P14 :: nil) (P2 :: P8 :: P10 :: P6 :: P9 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P8 :: P10 :: P6 :: P9 :: P10 :: P14 :: nil) ((P2 :: P8 :: P10 :: nil) ++ (P6 :: P9 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P6P8P9P10P14mtmp;try rewrite HT2 in HP2P6P8P9P10P14mtmp.
	assert(HT := rule_4 (P2 :: P8 :: P10 :: nil) (P6 :: P9 :: P10 :: P14 :: nil) (P10 :: nil) 4 1 2 HP2P6P8P9P10P14mtmp HP10mtmp HP2P8P10Mtmp Hincl); apply HT.
}
try clear HP6P9P10P14m2. try clear HP2P6P8P9P10P14M4. try clear HP2P6P8P9P10P14m4. 

assert(HP9P14m2 : rk(P9 :: P14 :: nil) >= 2).
{
	assert(HP6P10P14Mtmp : rk(P6 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP6P10P14eq HP6P10P14M2).
	assert(HP6P9P10P14mtmp : rk(P6 :: P9 :: P10 :: P14 :: nil) >= 3) by (solve_hyps_min HP6P9P10P14eq HP6P9P10P14m3).
	assert(HP14mtmp : rk(P14 :: nil) >= 1) by (solve_hyps_min HP14eq HP14m1).
	assert(Hincl : incl (P14 :: nil) (list_inter (P9 :: P14 :: nil) (P6 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P9 :: P10 :: P14 :: nil) (P9 :: P14 :: P6 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P9 :: P14 :: P6 :: P10 :: P14 :: nil) ((P9 :: P14 :: nil) ++ (P6 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP6P9P10P14mtmp;try rewrite HT2 in HP6P9P10P14mtmp.
	assert(HT := rule_2 (P9 :: P14 :: nil) (P6 :: P10 :: P14 :: nil) (P14 :: nil) 3 1 2 HP6P9P10P14mtmp HP14mtmp HP6P10P14Mtmp Hincl);apply HT.
}
try clear HP9P14m1. try clear HP6P9P10P14M3. try clear HP6P9P10P14m3. 

assert(HP2P9P14m2 : rk(P2 :: P9 :: P14 :: nil) >= 2).
{
	assert(HP2P9mtmp : rk(P2 :: P9 :: nil) >= 2) by (solve_hyps_min HP2P9eq HP2P9m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P9 :: nil) (P2 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P9 :: nil) (P2 :: P9 :: P14 :: nil) 2 2 HP2P9mtmp Hcomp Hincl);apply HT.
}
try clear HP2P9M2. try clear HP2P9m2. try clear HP2P9P14m1. 

assert(HP2P9P14m3 : rk(P2 :: P9 :: P14 :: nil) >= 3).
{
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(HP2P5P9P14mtmp : rk(P2 :: P5 :: P9 :: P14 :: nil) >= 3) by (solve_hyps_min HP2P5P9P14eq HP2P5P9P14m3).
	assert(HP9P14mtmp : rk(P9 :: P14 :: nil) >= 2) by (solve_hyps_min HP9P14eq HP9P14m2).
	assert(Hincl : incl (P9 :: P14 :: nil) (list_inter (P2 :: P9 :: P14 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P9 :: P14 :: nil) (P2 :: P9 :: P14 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P9 :: P14 :: P5 :: P9 :: P14 :: nil) ((P2 :: P9 :: P14 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P5P9P14mtmp;try rewrite HT2 in HP2P5P9P14mtmp.
	assert(HT := rule_2 (P2 :: P9 :: P14 :: nil) (P5 :: P9 :: P14 :: nil) (P9 :: P14 :: nil) 3 2 2 HP2P5P9P14mtmp HP9P14mtmp HP5P9P14Mtmp Hincl);apply HT.
}
try clear HP2P9P14m2. try clear HP9P14M2. try clear HP9P14m2. try clear HP2P5P9P14M3. try clear HP2P5P9P14m3. 

assert(HP2P7P9P11P14m2 : rk(P2 :: P7 :: P9 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP2P7mtmp : rk(P2 :: P7 :: nil) >= 2) by (solve_hyps_min HP2P7eq HP2P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: nil) (P2 :: P7 :: P9 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: nil) (P2 :: P7 :: P9 :: P11 :: P14 :: nil) 2 2 HP2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P9P11P14m1. 

assert(HP2P7P9P11P14m3 : rk(P2 :: P7 :: P9 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP2P7P9mtmp : rk(P2 :: P7 :: P9 :: nil) >= 3) by (solve_hyps_min HP2P7P9eq HP2P7P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: P9 :: nil) (P2 :: P7 :: P9 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: P9 :: nil) (P2 :: P7 :: P9 :: P11 :: P14 :: nil) 3 3 HP2P7P9mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P9P11P14m2. 

assert(HP2P7P9P11P14M3 : rk(P2 :: P7 :: P9 :: P11 :: P14 :: nil) <= 3).
{
	assert(HP2P7P9P14Mtmp : rk(P2 :: P7 :: P9 :: P14 :: nil) <= 3) by (solve_hyps_max HP2P7P9P14eq HP2P7P9P14M3).
	assert(HP2P9P11P14Mtmp : rk(P2 :: P9 :: P11 :: P14 :: nil) <= 3) by (solve_hyps_max HP2P9P11P14eq HP2P9P11P14M3).
	assert(HP2P9P14mtmp : rk(P2 :: P9 :: P14 :: nil) >= 3) by (solve_hyps_min HP2P9P14eq HP2P9P14m3).
	assert(Hincl : incl (P2 :: P9 :: P14 :: nil) (list_inter (P2 :: P7 :: P9 :: P14 :: nil) (P2 :: P9 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P7 :: P9 :: P11 :: P14 :: nil) (P2 :: P7 :: P9 :: P14 :: P2 :: P9 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P7 :: P9 :: P14 :: P2 :: P9 :: P11 :: P14 :: nil) ((P2 :: P7 :: P9 :: P14 :: nil) ++ (P2 :: P9 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P7 :: P9 :: P14 :: nil) (P2 :: P9 :: P11 :: P14 :: nil) (P2 :: P9 :: P14 :: nil) 3 3 3 HP2P7P9P14Mtmp HP2P9P11P14Mtmp HP2P9P14mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P7P9P14M3. try clear HP2P7P9P14m3. try clear HP2P9P11P14M3. try clear HP2P9P11P14m3. try clear HP2P9P14M3. try clear HP2P9P14m3. try clear HP2P7P9P11P14M4. 

assert(HP2P7P9P11M3 : rk(P2 :: P7 :: P9 :: P11 :: nil) <= 3).
{
	assert(HP7Mtmp : rk(P7 :: nil) <= 1) by (solve_hyps_max HP7eq HP7M1).
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P7 :: nil) (P2 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P7 :: P9 :: P11 :: nil) (P7 :: P2 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P2 :: P9 :: P11 :: nil) ((P7 :: nil) ++ (P2 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P7 :: nil) (P2 :: P9 :: P11 :: nil) (nil) 1 2 0 HP7Mtmp HP2P9P11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P7P9P11M4. 

assert(HP2P7P9P11m2 : rk(P2 :: P7 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP2P7mtmp : rk(P2 :: P7 :: nil) >= 2) by (solve_hyps_min HP2P7eq HP2P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: nil) (P2 :: P7 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: nil) (P2 :: P7 :: P9 :: P11 :: nil) 2 2 HP2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P9P11m1. 

assert(HP2P7P9P11m3 : rk(P2 :: P7 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP2P7P9mtmp : rk(P2 :: P7 :: P9 :: nil) >= 3) by (solve_hyps_min HP2P7P9eq HP2P7P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: P9 :: nil) (P2 :: P7 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: P9 :: nil) (P2 :: P7 :: P9 :: P11 :: nil) 3 3 HP2P7P9mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P9M3. try clear HP2P7P9m3. try clear HP2P7P9P11m2. 

assert(HP1P2P8P10M3 : rk(P1 :: P2 :: P8 :: P10 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P8 :: P10 :: nil) (P1 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P8 :: P10 :: nil) ((P1 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P2 :: P8 :: P10 :: nil) (nil) 1 2 0 HP1Mtmp HP2P8P10Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P8P10M4. 

assert(HP1P2P8P10m2 : rk(P1 :: P2 :: P8 :: P10 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P8 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P8P10m1. 

assert(HP1P2P8P10m3 : rk(P1 :: P2 :: P8 :: P10 :: nil) >= 3).
{
	assert(HP1P2P8mtmp : rk(P1 :: P2 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P8eq HP1P2P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P8 :: P10 :: nil) 3 3 HP1P2P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P8P10m2. 

assert(HP1P2P10m2 : rk(P1 :: P2 :: P10 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P10m1. 

assert(HP1P2P10m3 : rk(P1 :: P2 :: P10 :: nil) >= 3).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP1P2P8P10mtmp : rk(P1 :: P2 :: P8 :: P10 :: nil) >= 3) by (solve_hyps_min HP1P2P8P10eq HP1P2P8P10m3).
	assert(HP2P10mtmp : rk(P2 :: P10 :: nil) >= 2) by (solve_hyps_min HP2P10eq HP2P10m2).
	assert(Hincl : incl (P2 :: P10 :: nil) (list_inter (P1 :: P2 :: P10 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P8 :: P10 :: nil) (P1 :: P2 :: P10 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P10 :: P2 :: P8 :: P10 :: nil) ((P1 :: P2 :: P10 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P8P10mtmp;try rewrite HT2 in HP1P2P8P10mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P10 :: nil) (P2 :: P8 :: P10 :: nil) (P2 :: P10 :: nil) 3 2 2 HP1P2P8P10mtmp HP2P10mtmp HP2P8P10Mtmp Hincl);apply HT.
}
try clear HP1P2P10m2. 

assert(HP1P2P10P11M3 : rk(P1 :: P2 :: P10 :: P11 :: nil) <= 3).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP1P10P11Mtmp : rk(P1 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP1P10P11eq HP1P10P11M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P10 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P10 :: P11 :: nil) (P2 :: P1 :: P10 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P10 :: P11 :: nil) ((P2 :: nil) ++ (P1 :: P10 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: nil) (P1 :: P10 :: P11 :: nil) (nil) 1 2 0 HP2Mtmp HP1P10P11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P10P11M4. 

assert(HP1P2P10P11m2 : rk(P1 :: P2 :: P10 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P10 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P10 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P10P11m1. 

assert(HP1P2P10P11m3 : rk(P1 :: P2 :: P10 :: P11 :: nil) >= 3).
{
	assert(HP1P2P10mtmp : rk(P1 :: P2 :: P10 :: nil) >= 3) by (solve_hyps_min HP1P2P10eq HP1P2P10m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P10 :: nil) (P1 :: P2 :: P10 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P10 :: nil) (P1 :: P2 :: P10 :: P11 :: nil) 3 3 HP1P2P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P10M3. try clear HP1P2P10m3. try clear HP1P2P10P11m2. 

assert(HP2P11m2 : rk(P2 :: P11 :: nil) >= 2).
{
	assert(HP1P10P11Mtmp : rk(P1 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP1P10P11eq HP1P10P11M2).
	assert(HP1P2P10P11mtmp : rk(P1 :: P2 :: P10 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P2P10P11eq HP1P2P10P11m3).
	assert(HP11mtmp : rk(P11 :: nil) >= 1) by (solve_hyps_min HP11eq HP11m1).
	assert(Hincl : incl (P11 :: nil) (list_inter (P2 :: P11 :: nil) (P1 :: P10 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P10 :: P11 :: nil) (P2 :: P11 :: P1 :: P10 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P11 :: P1 :: P10 :: P11 :: nil) ((P2 :: P11 :: nil) ++ (P1 :: P10 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P10P11mtmp;try rewrite HT2 in HP1P2P10P11mtmp.
	assert(HT := rule_2 (P2 :: P11 :: nil) (P1 :: P10 :: P11 :: nil) (P11 :: nil) 3 1 2 HP1P2P10P11mtmp HP11mtmp HP1P10P11Mtmp Hincl);apply HT.
}
try clear HP2P11m1. try clear HP1P2P10P11M3. try clear HP1P2P10P11m3. 

assert(HP2P7P11m2 : rk(P2 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP2P7mtmp : rk(P2 :: P7 :: nil) >= 2) by (solve_hyps_min HP2P7eq HP2P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: nil) (P2 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: nil) (P2 :: P7 :: P11 :: nil) 2 2 HP2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P11m1. 

assert(HP2P7P11m3 : rk(P2 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(HP2P7P9P11mtmp : rk(P2 :: P7 :: P9 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P7P9P11eq HP2P7P9P11m3).
	assert(HP2P11mtmp : rk(P2 :: P11 :: nil) >= 2) by (solve_hyps_min HP2P11eq HP2P11m2).
	assert(Hincl : incl (P2 :: P11 :: nil) (list_inter (P2 :: P7 :: P11 :: nil) (P2 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P7 :: P9 :: P11 :: nil) (P2 :: P7 :: P11 :: P2 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P7 :: P11 :: P2 :: P9 :: P11 :: nil) ((P2 :: P7 :: P11 :: nil) ++ (P2 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P7P9P11mtmp;try rewrite HT2 in HP2P7P9P11mtmp.
	assert(HT := rule_2 (P2 :: P7 :: P11 :: nil) (P2 :: P9 :: P11 :: nil) (P2 :: P11 :: nil) 3 2 2 HP2P7P9P11mtmp HP2P11mtmp HP2P9P11Mtmp Hincl);apply HT.
}
try clear HP2P7P11m2. 

assert(HP2P7P11P14m2 : rk(P2 :: P7 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP2P7mtmp : rk(P2 :: P7 :: nil) >= 2) by (solve_hyps_min HP2P7eq HP2P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: nil) (P2 :: P7 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: nil) (P2 :: P7 :: P11 :: P14 :: nil) 2 2 HP2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7M2. try clear HP2P7m2. try clear HP2P7P11P14m1. 

assert(HP2P7P11P14m3 : rk(P2 :: P7 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP2P7P11mtmp : rk(P2 :: P7 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P7P11eq HP2P7P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: P11 :: nil) (P2 :: P7 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P7 :: P11 :: nil) (P2 :: P7 :: P11 :: P14 :: nil) 3 3 HP2P7P11mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P11M3. try clear HP2P7P11m3. try clear HP2P7P11P14m2. 

assert(HP2P7P11P14M3 : rk(P2 :: P7 :: P11 :: P14 :: nil) <= 3).
{
	assert(HP2P7P9P11P14Mtmp : rk(P2 :: P7 :: P9 :: P11 :: P14 :: nil) <= 3) by (solve_hyps_max HP2P7P9P11P14eq HP2P7P9P11P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P7 :: P11 :: P14 :: nil) (P2 :: P7 :: P9 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P2 :: P7 :: P11 :: P14 :: nil) (P2 :: P7 :: P9 :: P11 :: P14 :: nil) 3 3 HP2P7P9P11P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP2P7P11P14M4. try clear HP2P7P9P11P14M3. try clear HP2P7P9P11P14m3. 

assert(HP1P2P6P8P10m2 : rk(P1 :: P2 :: P6 :: P8 :: P10 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P8P10m1. 

assert(HP1P2P6P8P10m3 : rk(P1 :: P2 :: P6 :: P8 :: P10 :: nil) >= 3).
{
	assert(HP1P2P6mtmp : rk(P1 :: P2 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P6eq HP1P2P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: nil) 3 3 HP1P2P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P8P10m2. 

assert(HP1P2P6P8P10m4 : rk(P1 :: P2 :: P6 :: P8 :: P10 :: nil) >= 4).
{
	assert(HP1P2P6P8mtmp : rk(P1 :: P2 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P6P8eq HP1P2P6P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: P8 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: P8 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: nil) 4 4 HP1P2P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P8P10m3. 

assert(HP1P6P10m2 : rk(P1 :: P6 :: P10 :: nil) >= 2).
{
	assert(HP1P6mtmp : rk(P1 :: P6 :: nil) >= 2) by (solve_hyps_min HP1P6eq HP1P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: nil) (P1 :: P6 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: nil) (P1 :: P6 :: P10 :: nil) 2 2 HP1P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6P10m1. 

assert(HP1P6P10m3 : rk(P1 :: P6 :: P10 :: nil) >= 3).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP1P2P6P8P10mtmp : rk(P1 :: P2 :: P6 :: P8 :: P10 :: nil) >= 4) by (solve_hyps_min HP1P2P6P8P10eq HP1P2P6P8P10m4).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P1 :: P6 :: P10 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P6 :: P8 :: P10 :: nil) (P1 :: P6 :: P10 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P6 :: P10 :: P2 :: P8 :: P10 :: nil) ((P1 :: P6 :: P10 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P6P8P10mtmp;try rewrite HT2 in HP1P2P6P8P10mtmp.
	assert(HT := rule_2 (P1 :: P6 :: P10 :: nil) (P2 :: P8 :: P10 :: nil) (P10 :: nil) 4 1 2 HP1P2P6P8P10mtmp HP10mtmp HP2P8P10Mtmp Hincl);apply HT.
}
try clear HP1P6P10m2. try clear HP1P2P6P8P10M4. try clear HP1P2P6P8P10m4. 

assert(HP1P6P7P10P14m2 : rk(P1 :: P6 :: P7 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP1P6mtmp : rk(P1 :: P6 :: nil) >= 2) by (solve_hyps_min HP1P6eq HP1P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: nil) (P1 :: P6 :: P7 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: nil) (P1 :: P6 :: P7 :: P10 :: P14 :: nil) 2 2 HP1P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6P7P10P14m1. 

assert(HP1P6P7P10P14M3 : rk(P1 :: P6 :: P7 :: P10 :: P14 :: nil) <= 3).
{
	assert(HP1P6P7Mtmp : rk(P1 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P6P7eq HP1P6P7M2).
	assert(HP6P10P14Mtmp : rk(P6 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP6P10P14eq HP6P10P14M2).
	assert(HP6mtmp : rk(P6 :: nil) >= 1) by (solve_hyps_min HP6eq HP6m1).
	assert(Hincl : incl (P6 :: nil) (list_inter (P1 :: P6 :: P7 :: nil) (P6 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P6 :: P7 :: P10 :: P14 :: nil) (P1 :: P6 :: P7 :: P6 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P6 :: P7 :: P6 :: P10 :: P14 :: nil) ((P1 :: P6 :: P7 :: nil) ++ (P6 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P6 :: P7 :: nil) (P6 :: P10 :: P14 :: nil) (P6 :: nil) 2 2 1 HP1P6P7Mtmp HP6P10P14Mtmp HP6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P6P7P10P14M4. 

assert(HP1P6P7P10P14m3 : rk(P1 :: P6 :: P7 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P6P10mtmp : rk(P1 :: P6 :: P10 :: nil) >= 3) by (solve_hyps_min HP1P6P10eq HP1P6P10m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: P10 :: nil) (P1 :: P6 :: P7 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: P10 :: nil) (P1 :: P6 :: P7 :: P10 :: P14 :: nil) 3 3 HP1P6P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6P10M3. try clear HP1P6P10m3. try clear HP1P6P7P10P14m2. 

assert(HP1P2P7P8P10m2 : rk(P1 :: P2 :: P7 :: P8 :: P10 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P10m1. 

assert(HP1P2P7P8P10m3 : rk(P1 :: P2 :: P7 :: P8 :: P10 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: P10 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P10m2. 

assert(HP1P2P7P8P10m4 : rk(P1 :: P2 :: P7 :: P8 :: P10 :: nil) >= 4).
{
	assert(HP1P2P7P8mtmp : rk(P1 :: P2 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8eq HP1P2P7P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: P8 :: nil) (P1 :: P2 :: P7 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: P8 :: nil) (P1 :: P2 :: P7 :: P8 :: P10 :: nil) 4 4 HP1P2P7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P10m3. 

assert(HP1P7P10m2 : rk(P1 :: P7 :: P10 :: nil) >= 2).
{
	assert(HP1P7mtmp : rk(P1 :: P7 :: nil) >= 2) by (solve_hyps_min HP1P7eq HP1P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P7 :: nil) (P1 :: P7 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P7 :: nil) (P1 :: P7 :: P10 :: nil) 2 2 HP1P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P7P10m1. 

assert(HP1P7P10m3 : rk(P1 :: P7 :: P10 :: nil) >= 3).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP1P2P7P8P10mtmp : rk(P1 :: P2 :: P7 :: P8 :: P10 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8P10eq HP1P2P7P8P10m4).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P1 :: P7 :: P10 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P8 :: P10 :: nil) (P1 :: P7 :: P10 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P7 :: P10 :: P2 :: P8 :: P10 :: nil) ((P1 :: P7 :: P10 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P8P10mtmp;try rewrite HT2 in HP1P2P7P8P10mtmp.
	assert(HT := rule_2 (P1 :: P7 :: P10 :: nil) (P2 :: P8 :: P10 :: nil) (P10 :: nil) 4 1 2 HP1P2P7P8P10mtmp HP10mtmp HP2P8P10Mtmp Hincl);apply HT.
}
try clear HP1P7P10m2. 

assert(HP1P7P10P14m2 : rk(P1 :: P7 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP1P7mtmp : rk(P1 :: P7 :: nil) >= 2) by (solve_hyps_min HP1P7eq HP1P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P7 :: nil) (P1 :: P7 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P7 :: nil) (P1 :: P7 :: P10 :: P14 :: nil) 2 2 HP1P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P7P10P14m1. 

assert(HP1P7P10P14m3 : rk(P1 :: P7 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P7P10mtmp : rk(P1 :: P7 :: P10 :: nil) >= 3) by (solve_hyps_min HP1P7P10eq HP1P7P10m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P7 :: P10 :: nil) (P1 :: P7 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P7 :: P10 :: nil) (P1 :: P7 :: P10 :: P14 :: nil) 3 3 HP1P7P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P7P10P14m2. 

assert(HP1P7P10P14M3 : rk(P1 :: P7 :: P10 :: P14 :: nil) <= 3).
{
	assert(HP1P6P7P10P14Mtmp : rk(P1 :: P6 :: P7 :: P10 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P6P7P10P14eq HP1P6P7P10P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P7 :: P10 :: P14 :: nil) (P1 :: P6 :: P7 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P7 :: P10 :: P14 :: nil) (P1 :: P6 :: P7 :: P10 :: P14 :: nil) 3 3 HP1P6P7P10P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P7P10P14M4. try clear HP1P6P7P10P14M3. try clear HP1P6P7P10P14m3. 

assert(HP1P2P4P8P10P11P14m2 : rk(P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P10P11P14m1. 

assert(HP1P2P4P8P10P11P14m3 : rk(P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P10P11P14m2. 

assert(HP1P2P4P8P10P11P14m4 : rk(P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P10P11P14m3. 

assert(HP8P10m2 : rk(P8 :: P10 :: nil) >= 2).
{
	assert(HP9Mtmp : rk(P9 :: nil) <= 1) by (solve_hyps_max HP9eq HP9M1).
	assert(HP8P9P10mtmp : rk(P8 :: P9 :: P10 :: nil) >= 3) by (solve_hyps_min HP8P9P10eq HP8P9P10m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P9 :: nil) (P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P8 :: P9 :: P10 :: nil) (P9 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P9 :: P8 :: P10 :: nil) ((P9 :: nil) ++ (P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP8P9P10mtmp;try rewrite HT2 in HP8P9P10mtmp.
	assert(HT := rule_4 (P9 :: nil) (P8 :: P10 :: nil) (nil) 3 0 1 HP8P9P10mtmp Hmtmp HP9Mtmp Hincl); apply HT.
}
try clear HP8P10m1. try clear HP8P9P10M3. try clear HP8P9P10m3. 

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
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P10P11P14m2. 

assert(HP1P4P8P10P11P14m4 : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) >= 4).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP1P2P4P8P10P11P14mtmp : rk(P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8P10P11P14eq HP1P2P4P8P10P11P14m4).
	assert(HP8P10mtmp : rk(P8 :: P10 :: nil) >= 2) by (solve_hyps_min HP8P10eq HP8P10m2).
	assert(Hincl : incl (P8 :: P10 :: nil) (list_inter (P2 :: P8 :: P10 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) (P2 :: P8 :: P10 :: P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P8 :: P10 :: P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) ((P2 :: P8 :: P10 :: nil) ++ (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8P10P11P14mtmp;try rewrite HT2 in HP1P2P4P8P10P11P14mtmp.
	assert(HT := rule_4 (P2 :: P8 :: P10 :: nil) (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) (P8 :: P10 :: nil) 4 2 2 HP1P2P4P8P10P11P14mtmp HP8P10mtmp HP2P8P10Mtmp Hincl); apply HT.
}
try clear HP1P4P8P10P11P14m3. try clear HP1P2P4P8P10P11P14M4. try clear HP1P2P4P8P10P11P14m4. 

assert(HP1P10m2 : rk(P1 :: P10 :: nil) >= 2).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP1P2P8P10mtmp : rk(P1 :: P2 :: P8 :: P10 :: nil) >= 3) by (solve_hyps_min HP1P2P8P10eq HP1P2P8P10m3).
	assert(HP10mtmp : rk(P10 :: nil) >= 1) by (solve_hyps_min HP10eq HP10m1).
	assert(Hincl : incl (P10 :: nil) (list_inter (P1 :: P10 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P8 :: P10 :: nil) (P1 :: P10 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P10 :: P2 :: P8 :: P10 :: nil) ((P1 :: P10 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P8P10mtmp;try rewrite HT2 in HP1P2P8P10mtmp.
	assert(HT := rule_2 (P1 :: P10 :: nil) (P2 :: P8 :: P10 :: nil) (P10 :: nil) 3 1 2 HP1P2P8P10mtmp HP10mtmp HP2P8P10Mtmp Hincl);apply HT.
}
try clear HP1P10m1. try clear HP10M1. try clear HP10m1. 

assert(HP1P10P11P14m2 : rk(P1 :: P10 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP1P10mtmp : rk(P1 :: P10 :: nil) >= 2) by (solve_hyps_min HP1P10eq HP1P10m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P10 :: nil) (P1 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P10 :: nil) (P1 :: P10 :: P11 :: P14 :: nil) 2 2 HP1P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P10P11P14m1. 

assert(HP1P10P11P14M3 : rk(P1 :: P10 :: P11 :: P14 :: nil) <= 3).
{
	assert(HP1P10P11Mtmp : rk(P1 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP1P10P11eq HP1P10P11M2).
	assert(HP14Mtmp : rk(P14 :: nil) <= 1) by (solve_hyps_max HP14eq HP14M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P10 :: P11 :: nil) (P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P10 :: P11 :: P14 :: nil) (P1 :: P10 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P10 :: P11 :: P14 :: nil) ((P1 :: P10 :: P11 :: nil) ++ (P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P10 :: P11 :: nil) (P14 :: nil) (nil) 2 1 0 HP1P10P11Mtmp HP14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P10P11P14M4. 

assert(HP1P10P11P14m3 : rk(P1 :: P10 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP1P4P8P10P11P14mtmp : rk(P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P8P10P11P14eq HP1P4P8P10P11P14m4).
	assert(HP1P14mtmp : rk(P1 :: P14 :: nil) >= 2) by (solve_hyps_min HP1P14eq HP1P14m2).
	assert(Hincl : incl (P1 :: P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P10 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P10 :: P11 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P1 :: P10 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P1 :: P10 :: P11 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P1 :: P10 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P10P11P14mtmp;try rewrite HT2 in HP1P4P8P10P11P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P10 :: P11 :: P14 :: nil) (P1 :: P14 :: nil) 4 2 3 HP1P4P8P10P11P14mtmp HP1P14mtmp HP1P4P8P14Mtmp Hincl); apply HT.
}
try clear HP1P10P11P14m2. try clear HP1P4P8P10P11P14M4. try clear HP1P4P8P10P11P14m4. 

assert(HP1P2P4P8P10P14m2 : rk(P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P10P14m1. 

assert(HP1P2P4P8P10P14m3 : rk(P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P10P14m2. 

assert(HP1P2P4P8P10P14m4 : rk(P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P10P14m3. 

assert(HP1P4P8P10P14m2 : rk(P1 :: P4 :: P8 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P10 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P10P14m1. 

assert(HP1P4P8P10P14m3 : rk(P1 :: P4 :: P8 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P10 :: P14 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P10P14m2. 

assert(HP1P4P8P10P14m4 : rk(P1 :: P4 :: P8 :: P10 :: P14 :: nil) >= 4).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP1P2P4P8P10P14mtmp : rk(P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8P10P14eq HP1P2P4P8P10P14m4).
	assert(HP8P10mtmp : rk(P8 :: P10 :: nil) >= 2) by (solve_hyps_min HP8P10eq HP8P10m2).
	assert(Hincl : incl (P8 :: P10 :: nil) (list_inter (P2 :: P8 :: P10 :: nil) (P1 :: P4 :: P8 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: P10 :: P14 :: nil) (P2 :: P8 :: P10 :: P1 :: P4 :: P8 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P8 :: P10 :: P1 :: P4 :: P8 :: P10 :: P14 :: nil) ((P2 :: P8 :: P10 :: nil) ++ (P1 :: P4 :: P8 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8P10P14mtmp;try rewrite HT2 in HP1P2P4P8P10P14mtmp.
	assert(HT := rule_4 (P2 :: P8 :: P10 :: nil) (P1 :: P4 :: P8 :: P10 :: P14 :: nil) (P8 :: P10 :: nil) 4 2 2 HP1P2P4P8P10P14mtmp HP8P10mtmp HP2P8P10Mtmp Hincl); apply HT.
}
try clear HP1P4P8P10P14m3. try clear HP1P2P4P8P10P14M4. try clear HP1P2P4P8P10P14m4. 

assert(HP1P10P14m2 : rk(P1 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP1P10mtmp : rk(P1 :: P10 :: nil) >= 2) by (solve_hyps_min HP1P10eq HP1P10m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P10 :: nil) (P1 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P10 :: nil) (P1 :: P10 :: P14 :: nil) 2 2 HP1P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P10M2. try clear HP1P10m2. try clear HP1P10P14m1. 

assert(HP1P10P14m3 : rk(P1 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP1P4P8P10P14mtmp : rk(P1 :: P4 :: P8 :: P10 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P8P10P14eq HP1P4P8P10P14m4).
	assert(HP1P14mtmp : rk(P1 :: P14 :: nil) >= 2) by (solve_hyps_min HP1P14eq HP1P14m2).
	assert(Hincl : incl (P1 :: P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P10 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P1 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P1 :: P10 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P1 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P10P14mtmp;try rewrite HT2 in HP1P4P8P10P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P10 :: P14 :: nil) (P1 :: P14 :: nil) 4 2 3 HP1P4P8P10P14mtmp HP1P14mtmp HP1P4P8P14Mtmp Hincl); apply HT.
}
try clear HP1P10P14m2. try clear HP1P14M2. try clear HP1P14m2. try clear HP1P4P8P10P14M4. try clear HP1P4P8P10P14m4. 

assert(HP1P7P10P11P14m2 : rk(P1 :: P7 :: P10 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP1P7mtmp : rk(P1 :: P7 :: nil) >= 2) by (solve_hyps_min HP1P7eq HP1P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P7 :: nil) (P1 :: P7 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P7 :: nil) (P1 :: P7 :: P10 :: P11 :: P14 :: nil) 2 2 HP1P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P7M2. try clear HP1P7m2. try clear HP1P7P10P11P14m1. 

assert(HP1P7P10P11P14m3 : rk(P1 :: P7 :: P10 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP1P7P10mtmp : rk(P1 :: P7 :: P10 :: nil) >= 3) by (solve_hyps_min HP1P7P10eq HP1P7P10m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P7 :: P10 :: nil) (P1 :: P7 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P7 :: P10 :: nil) (P1 :: P7 :: P10 :: P11 :: P14 :: nil) 3 3 HP1P7P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P7P10M3. try clear HP1P7P10m3. try clear HP1P7P10P11P14m2. 

assert(HP1P7P10P11P14M3 : rk(P1 :: P7 :: P10 :: P11 :: P14 :: nil) <= 3).
{
	assert(HP1P7P10P14Mtmp : rk(P1 :: P7 :: P10 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P7P10P14eq HP1P7P10P14M3).
	assert(HP1P10P11P14Mtmp : rk(P1 :: P10 :: P11 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P10P11P14eq HP1P10P11P14M3).
	assert(HP1P10P14mtmp : rk(P1 :: P10 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P10P14eq HP1P10P14m3).
	assert(Hincl : incl (P1 :: P10 :: P14 :: nil) (list_inter (P1 :: P7 :: P10 :: P14 :: nil) (P1 :: P10 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P7 :: P10 :: P11 :: P14 :: nil) (P1 :: P7 :: P10 :: P14 :: P1 :: P10 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P7 :: P10 :: P14 :: P1 :: P10 :: P11 :: P14 :: nil) ((P1 :: P7 :: P10 :: P14 :: nil) ++ (P1 :: P10 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P7 :: P10 :: P14 :: nil) (P1 :: P10 :: P11 :: P14 :: nil) (P1 :: P10 :: P14 :: nil) 3 3 3 HP1P7P10P14Mtmp HP1P10P11P14Mtmp HP1P10P14mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P7P10P14M3. try clear HP1P7P10P14m3. try clear HP1P10P11P14M3. try clear HP1P10P11P14m3. try clear HP1P10P14M3. try clear HP1P10P14m3. try clear HP1P7P10P11P14M4. 

assert(HP1P2P7P10m2 : rk(P1 :: P2 :: P7 :: P10 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P10m1. 

assert(HP1P2P7P10m3 : rk(P1 :: P2 :: P7 :: P10 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P10 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P10m2. 

assert(HP1P2P7P10m4 : rk(P1 :: P2 :: P7 :: P10 :: nil) >= 4).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP1P2P7P8P10mtmp : rk(P1 :: P2 :: P7 :: P8 :: P10 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8P10eq HP1P2P7P8P10m4).
	assert(HP2P10mtmp : rk(P2 :: P10 :: nil) >= 2) by (solve_hyps_min HP2P10eq HP2P10m2).
	assert(Hincl : incl (P2 :: P10 :: nil) (list_inter (P1 :: P2 :: P7 :: P10 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P8 :: P10 :: nil) (P1 :: P2 :: P7 :: P10 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P7 :: P10 :: P2 :: P8 :: P10 :: nil) ((P1 :: P2 :: P7 :: P10 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P8P10mtmp;try rewrite HT2 in HP1P2P7P8P10mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P7 :: P10 :: nil) (P2 :: P8 :: P10 :: nil) (P2 :: P10 :: nil) 4 2 2 HP1P2P7P8P10mtmp HP2P10mtmp HP2P8P10Mtmp Hincl);apply HT.
}
try clear HP1P2P7P10m3. try clear HP2P10M2. try clear HP2P10m2. try clear HP1P2P7P8P10M4. try clear HP1P2P7P8P10m4. 

assert(HP1P2P7P10P11P14m2 : rk(P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P10P11P14m1. 

assert(HP1P2P7P10P11P14m3 : rk(P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P10P11P14m2. 

assert(HP1P2P7P10P11P14m4 : rk(P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil) >= 4).
{
	assert(HP1P2P7P10mtmp : rk(P1 :: P2 :: P7 :: P10 :: nil) >= 4) by (solve_hyps_min HP1P2P7P10eq HP1P2P7P10m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: P10 :: nil) (P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: P10 :: nil) (P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil) 4 4 HP1P2P7P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P10M4. try clear HP1P2P7P10m4. try clear HP1P2P7P10P11P14m3. 

assert(HP7P11m2 : rk(P7 :: P11 :: nil) >= 2).
{
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(HP2P7P9P11mtmp : rk(P2 :: P7 :: P9 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P7P9P11eq HP2P7P9P11m3).
	assert(HP11mtmp : rk(P11 :: nil) >= 1) by (solve_hyps_min HP11eq HP11m1).
	assert(Hincl : incl (P11 :: nil) (list_inter (P7 :: P11 :: nil) (P2 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P7 :: P9 :: P11 :: nil) (P7 :: P11 :: P2 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P11 :: P2 :: P9 :: P11 :: nil) ((P7 :: P11 :: nil) ++ (P2 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P7P9P11mtmp;try rewrite HT2 in HP2P7P9P11mtmp.
	assert(HT := rule_2 (P7 :: P11 :: nil) (P2 :: P9 :: P11 :: nil) (P11 :: nil) 3 1 2 HP2P7P9P11mtmp HP11mtmp HP2P9P11Mtmp Hincl);apply HT.
}
try clear HP7P11m1. try clear HP2P7P9P11M3. try clear HP2P7P9P11m3. 

assert(HP7P11P14m2 : rk(P7 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP7P11mtmp : rk(P7 :: P11 :: nil) >= 2) by (solve_hyps_min HP7P11eq HP7P11m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P7 :: P11 :: nil) (P7 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P11 :: nil) (P7 :: P11 :: P14 :: nil) 2 2 HP7P11mtmp Hcomp Hincl);apply HT.
}
try clear HP7P11P14m1. 

assert(HP7P11P14M2 : rk(P7 :: P11 :: P14 :: nil) <= 2).
{
	assert(HP2P7P11P14Mtmp : rk(P2 :: P7 :: P11 :: P14 :: nil) <= 3) by (solve_hyps_max HP2P7P11P14eq HP2P7P11P14M3).
	assert(HP1P7P10P11P14Mtmp : rk(P1 :: P7 :: P10 :: P11 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P7P10P11P14eq HP1P7P10P11P14M3).
	assert(HP1P2P7P10P11P14mtmp : rk(P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P7P10P11P14eq HP1P2P7P10P11P14m4).
	assert(Hincl : incl (P7 :: P11 :: P14 :: nil) (list_inter (P2 :: P7 :: P11 :: P14 :: nil) (P1 :: P7 :: P10 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P10 :: P11 :: P14 :: nil) (P2 :: P7 :: P11 :: P14 :: P1 :: P7 :: P10 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P7 :: P11 :: P14 :: P1 :: P7 :: P10 :: P11 :: P14 :: nil) ((P2 :: P7 :: P11 :: P14 :: nil) ++ (P1 :: P7 :: P10 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P10P11P14mtmp;try rewrite HT2 in HP1P2P7P10P11P14mtmp.
	assert(HT := rule_3 (P2 :: P7 :: P11 :: P14 :: nil) (P1 :: P7 :: P10 :: P11 :: P14 :: nil) (P7 :: P11 :: P14 :: nil) 3 3 4 HP2P7P11P14Mtmp HP1P7P10P11P14Mtmp HP1P2P7P10P11P14mtmp Hincl);apply HT.
}
try clear HP2P7P11P14M3. try clear HP2P7P11P14m3. try clear HP1P7P10P11P14M3. try clear HP1P7P10P11P14m3. try clear HP7P11P14M3. try clear HP1P2P7P10P11P14M4. try clear HP1P2P7P10P11P14m4. 

assert(HP1P2P7P9m2 : rk(P1 :: P2 :: P7 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P9m1. 

assert(HP1P2P7P9m3 : rk(P1 :: P2 :: P7 :: P9 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P9 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P9m2. 

assert(HP1P2P7P9m4 : rk(P1 :: P2 :: P7 :: P9 :: nil) >= 4).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P2P7P8P9mtmp : rk(P1 :: P2 :: P7 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8P9eq HP1P2P7P8P9m4).
	assert(HP1P9mtmp : rk(P1 :: P9 :: nil) >= 2) by (solve_hyps_min HP1P9eq HP1P9m2).
	assert(Hincl : incl (P1 :: P9 :: nil) (list_inter (P1 :: P2 :: P7 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P8 :: P9 :: nil) (P1 :: P2 :: P7 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P7 :: P9 :: P1 :: P8 :: P9 :: nil) ((P1 :: P2 :: P7 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P8P9mtmp;try rewrite HT2 in HP1P2P7P8P9mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P7 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P1 :: P9 :: nil) 4 2 2 HP1P2P7P8P9mtmp HP1P9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP1P2P7P9m3. try clear HP1P2P7P8P9M4. try clear HP1P2P7P8P9m4. 

assert(HP1P2P7P9P11m2 : rk(P1 :: P2 :: P7 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P9 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P9P11m1. 

assert(HP1P2P7P9P11m3 : rk(P1 :: P2 :: P7 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P9 :: P11 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P9P11m2. 

assert(HP1P2P7P9P11m4 : rk(P1 :: P2 :: P7 :: P9 :: P11 :: nil) >= 4).
{
	assert(HP1P2P7P9mtmp : rk(P1 :: P2 :: P7 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P7P9eq HP1P2P7P9m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: P9 :: nil) (P1 :: P2 :: P7 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: P9 :: nil) (P1 :: P2 :: P7 :: P9 :: P11 :: nil) 4 4 HP1P2P7P9mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P9M4. try clear HP1P2P7P9m4. try clear HP1P2P7P9P11m3. 

assert(HP1P2P7P11m2 : rk(P1 :: P2 :: P7 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P11m1. 

assert(HP1P2P7P11m3 : rk(P1 :: P2 :: P7 :: P11 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P11 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P11m2. 

assert(HP1P2P7P11m4 : rk(P1 :: P2 :: P7 :: P11 :: nil) >= 4).
{
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(HP1P2P7P9P11mtmp : rk(P1 :: P2 :: P7 :: P9 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P7P9P11eq HP1P2P7P9P11m4).
	assert(HP2P11mtmp : rk(P2 :: P11 :: nil) >= 2) by (solve_hyps_min HP2P11eq HP2P11m2).
	assert(Hincl : incl (P2 :: P11 :: nil) (list_inter (P1 :: P2 :: P7 :: P11 :: nil) (P2 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P9 :: P11 :: nil) (P1 :: P2 :: P7 :: P11 :: P2 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P7 :: P11 :: P2 :: P9 :: P11 :: nil) ((P1 :: P2 :: P7 :: P11 :: nil) ++ (P2 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P9P11mtmp;try rewrite HT2 in HP1P2P7P9P11mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P7 :: P11 :: nil) (P2 :: P9 :: P11 :: nil) (P2 :: P11 :: nil) 4 2 2 HP1P2P7P9P11mtmp HP2P11mtmp HP2P9P11Mtmp Hincl);apply HT.
}
try clear HP1P2P7P11m3. try clear HP2P11M2. try clear HP2P11m2. try clear HP1P2P7P9P11M4. try clear HP1P2P7P9P11m4. 

assert(HP1P2P7P11P12P14m2 : rk(P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P11P12P14m1. 

assert(HP1P2P7P11P12P14m3 : rk(P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P11P12P14m2. 

assert(HP1P2P7P11P12P14m4 : rk(P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil) >= 4).
{
	assert(HP1P2P7P11mtmp : rk(P1 :: P2 :: P7 :: P11 :: nil) >= 4) by (solve_hyps_min HP1P2P7P11eq HP1P2P7P11m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: P11 :: nil) (P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: P11 :: nil) (P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil) 4 4 HP1P2P7P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P11M4. try clear HP1P2P7P11m4. try clear HP1P2P7P11P12P14m3. 

assert(HP7P11P12P14m2 : rk(P7 :: P11 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP7P11mtmp : rk(P7 :: P11 :: nil) >= 2) by (solve_hyps_min HP7P11eq HP7P11m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P7 :: P11 :: nil) (P7 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P11 :: nil) (P7 :: P11 :: P12 :: P14 :: nil) 2 2 HP7P11mtmp Hcomp Hincl);apply HT.
}
try clear HP7P11M2. try clear HP7P11m2. try clear HP7P11P12P14m1. 

assert(HP7P11P12P14m3 : rk(P7 :: P11 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P2P12Mtmp : rk(P1 :: P2 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P2P12eq HP1P2P12M2).
	assert(HP1P2P7P11P12P14mtmp : rk(P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P7P11P12P14eq HP1P2P7P11P12P14m4).
	assert(HP12mtmp : rk(P12 :: nil) >= 1) by (solve_hyps_min HP12eq HP12m1).
	assert(Hincl : incl (P12 :: nil) (list_inter (P1 :: P2 :: P12 :: nil) (P7 :: P11 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P11 :: P12 :: P14 :: nil) (P1 :: P2 :: P12 :: P7 :: P11 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P12 :: P7 :: P11 :: P12 :: P14 :: nil) ((P1 :: P2 :: P12 :: nil) ++ (P7 :: P11 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P11P12P14mtmp;try rewrite HT2 in HP1P2P7P11P12P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P12 :: nil) (P7 :: P11 :: P12 :: P14 :: nil) (P12 :: nil) 4 1 2 HP1P2P7P11P12P14mtmp HP12mtmp HP1P2P12Mtmp Hincl); apply HT.
}
try clear HP7P11P12P14m2. try clear HP1P2P7P11P12P14M4. try clear HP1P2P7P11P12P14m4. 

assert(HP7P11P12P14M3 : rk(P7 :: P11 :: P12 :: P14 :: nil) <= 3).
{
	assert(HP12Mtmp : rk(P12 :: nil) <= 1) by (solve_hyps_max HP12eq HP12M1).
	assert(HP7P11P14Mtmp : rk(P7 :: P11 :: P14 :: nil) <= 2) by (solve_hyps_max HP7P11P14eq HP7P11P14M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P12 :: nil) (P7 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P7 :: P11 :: P12 :: P14 :: nil) (P12 :: P7 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P12 :: P7 :: P11 :: P14 :: nil) ((P12 :: nil) ++ (P7 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P12 :: nil) (P7 :: P11 :: P14 :: nil) (nil) 1 2 0 HP12Mtmp HP7P11P14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP7P11P14M2. try clear HP7P11P14m2. try clear HP7P11P12P14M4. 

assert(HP1P2P4P8P9m2 : rk(P1 :: P2 :: P4 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P9m1. 

assert(HP1P2P4P8P9m3 : rk(P1 :: P2 :: P4 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P9m2. 

assert(HP1P2P4P8P9m4 : rk(P1 :: P2 :: P4 :: P8 :: P9 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P9 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P9m3. 

assert(HP1P2P4P9m2 : rk(P1 :: P2 :: P4 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P9m1. 

assert(HP1P2P4P9m3 : rk(P1 :: P2 :: P4 :: P9 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P9 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P9m2. 

assert(HP1P2P4P9m4 : rk(P1 :: P2 :: P4 :: P9 :: nil) >= 4).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P2P4P8P9mtmp : rk(P1 :: P2 :: P4 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8P9eq HP1P2P4P8P9m4).
	assert(HP1P9mtmp : rk(P1 :: P9 :: nil) >= 2) by (solve_hyps_min HP1P9eq HP1P9m2).
	assert(Hincl : incl (P1 :: P9 :: nil) (list_inter (P1 :: P2 :: P4 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: P9 :: nil) (P1 :: P2 :: P4 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P4 :: P9 :: P1 :: P8 :: P9 :: nil) ((P1 :: P2 :: P4 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8P9mtmp;try rewrite HT2 in HP1P2P4P8P9mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P4 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P1 :: P9 :: nil) 4 2 2 HP1P2P4P8P9mtmp HP1P9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP1P2P4P9m3. try clear HP1P2P4P8P9M4. try clear HP1P2P4P8P9m4. 

assert(HP1P2P4P5P7P9P12P14m2 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P9P12P14m1. 

assert(HP1P2P4P5P7P9P12P14m3 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P9P12P14m2. 

assert(HP1P2P4P5P7P9P12P14m4 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 4).
{
	assert(HP1P2P4P9mtmp : rk(P1 :: P2 :: P4 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P4P9eq HP1P2P4P9m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P9 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P9 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) 4 4 HP1P2P4P9mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P4P5P7P9P12m2 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P9P12m1. 

assert(HP1P2P4P5P7P9P12m3 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P7P9P12m2. 

assert(HP1P2P4P5P7P9P12m4 : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil) >= 4).
{
	assert(HP1P2P4P9mtmp : rk(P1 :: P2 :: P4 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P4P9eq HP1P2P4P9m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P9 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P9 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil) 4 4 HP1P2P4P9mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P9M4. try clear HP1P2P4P9m4. try clear HP1P2P4P5P7P9P12m3. 

assert(HP4P5P9m2 : rk(P4 :: P5 :: P9 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P9 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P9m1. 

assert(HP4P5P9m3 : rk(P4 :: P5 :: P9 :: nil) >= 3).
{
	assert(HP1P2P4P5P7P12Mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) <= 3) by (solve_hyps_max HP1P2P4P5P7P12eq HP1P2P4P5P7P12M3).
	assert(HP1P2P4P5P7P9P12mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil) >= 4) by (solve_hyps_min HP1P2P4P5P7P9P12eq HP1P2P4P5P7P9P12m4).
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P4 :: P5 :: P9 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: nil) (P4 :: P5 :: P9 :: P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P9 :: P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) ((P4 :: P5 :: P9 :: nil) ++ (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P7P9P12mtmp;try rewrite HT2 in HP1P2P4P5P7P9P12mtmp.
	assert(HT := rule_2 (P4 :: P5 :: P9 :: nil) (P1 :: P2 :: P4 :: P5 :: P7 :: P12 :: nil) (P4 :: P5 :: nil) 4 2 3 HP1P2P4P5P7P9P12mtmp HP4P5mtmp HP1P2P4P5P7P12Mtmp Hincl);apply HT.
}
try clear HP4P5P9m2. try clear HP1P2P4P5P7P12M3. try clear HP1P2P4P5P7P12m3. try clear HP1P2P4P5P7P9P12M4. try clear HP1P2P4P5P7P9P12m4. 

assert(HP1P4P5P8P9m2 : rk(P1 :: P4 :: P5 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P8P9m1. 

assert(HP1P4P5P8P9M3 : rk(P1 :: P4 :: P5 :: P8 :: P9 :: nil) <= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1mtmp : rk(P1 :: nil) >= 1) by (solve_hyps_min HP1eq HP1m1).
	assert(Hincl : incl (P1 :: nil) (list_inter (P1 :: P4 :: P5 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P8 :: P9 :: nil) (P1 :: P4 :: P5 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P1 :: P8 :: P9 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P5 :: nil) (P1 :: P8 :: P9 :: nil) (P1 :: nil) 2 2 1 HP1P4P5Mtmp HP1P8P9Mtmp HP1mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P8P9M4. 

assert(HP1P4P5P8P9m3 : rk(P1 :: P4 :: P5 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: P9 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P8P9m2. 

assert(HP1P4P5P9m2 : rk(P1 :: P4 :: P5 :: P9 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P5 :: P9 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P5P9m1. 

assert(HP1P4P5P9M3 : rk(P1 :: P4 :: P5 :: P9 :: nil) <= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP9Mtmp : rk(P9 :: nil) <= 1) by (solve_hyps_max HP9eq HP9M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P4 :: P5 :: nil) (P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P9 :: nil) (P1 :: P4 :: P5 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P9 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P4 :: P5 :: nil) (P9 :: nil) (nil) 2 1 0 HP1P4P5Mtmp HP9Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P5P9M4. 

assert(HP1P4P5P9m3 : rk(P1 :: P4 :: P5 :: P9 :: nil) >= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P4P5P8P9mtmp : rk(P1 :: P4 :: P5 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P4P5P8P9eq HP1P4P5P8P9m3).
	assert(HP1P9mtmp : rk(P1 :: P9 :: nil) >= 2) by (solve_hyps_min HP1P9eq HP1P9m2).
	assert(Hincl : incl (P1 :: P9 :: nil) (list_inter (P1 :: P4 :: P5 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P5 :: P8 :: P9 :: nil) (P1 :: P4 :: P5 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P9 :: P1 :: P8 :: P9 :: nil) ((P1 :: P4 :: P5 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P5P8P9mtmp;try rewrite HT2 in HP1P4P5P8P9mtmp.
	assert(HT := rule_2 (P1 :: P4 :: P5 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P1 :: P9 :: nil) 3 2 2 HP1P4P5P8P9mtmp HP1P9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP1P4P5P9m2. try clear HP1P9M2. try clear HP1P9m2. try clear HP1P4P5P8P9M3. try clear HP1P4P5P8P9m3. 

assert(HP2P4P5P7P9P12P14m2 : rk(P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4P5P7P9P12P14m1. 

assert(HP2P4P5P7P9P12P14m3 : rk(P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP1P2P4P5P7P9P12P14mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P2P4P5P7P9P12P14eq HP1P2P4P5P7P9P12P14m3).
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P1 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P1 :: P4 :: P5 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P7P9P12P14mtmp;try rewrite HT2 in HP1P2P4P5P7P9P12P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P4 :: P5 :: nil) 3 2 2 HP1P2P4P5P7P9P12P14mtmp HP4P5mtmp HP1P4P5Mtmp Hincl); apply HT.
}
try clear HP2P4P5P7P9P12P14m2. try clear HP1P2P4P5P7P9P12P14M4. try clear HP1P2P4P5P7P9P12P14m3. 

assert(HP2P4P5P7P9P12P14m4 : rk(P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 4).
{
	assert(HP1P4P5P9Mtmp : rk(P1 :: P4 :: P5 :: P9 :: nil) <= 3) by (solve_hyps_max HP1P4P5P9eq HP1P4P5P9M3).
	assert(HP1P2P4P5P7P9P12P14mtmp : rk(P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P4P5P7P9P12P14eq HP1P2P4P5P7P9P12P14m4).
	assert(HP4P5P9mtmp : rk(P4 :: P5 :: P9 :: nil) >= 3) by (solve_hyps_min HP4P5P9eq HP4P5P9m3).
	assert(Hincl : incl (P4 :: P5 :: P9 :: nil) (list_inter (P1 :: P4 :: P5 :: P9 :: nil) (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P1 :: P4 :: P5 :: P9 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P9 :: P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) ((P1 :: P4 :: P5 :: P9 :: nil) ++ (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P7P9P12P14mtmp;try rewrite HT2 in HP1P2P4P5P7P9P12P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P5 :: P9 :: nil) (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P4 :: P5 :: P9 :: nil) 4 3 3 HP1P2P4P5P7P9P12P14mtmp HP4P5P9mtmp HP1P4P5P9Mtmp Hincl); apply HT.
}
try clear HP1P4P5P9M3. try clear HP1P4P5P9m3. try clear HP4P5P9M3. try clear HP4P5P9m3. try clear HP1P2P4P5P7P9P12P14M4. try clear HP1P2P4P5P7P9P12P14m4. 

assert(HP1P3P5m2 : rk(P1 :: P3 :: P5 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5m1. 

assert(HP1P3P5m3 : rk(P1 :: P3 :: P5 :: nil) >= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP1P3P4P5mtmp : rk(P1 :: P3 :: P4 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P3P4P5eq HP1P3P4P5m3).
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hincl : incl (P1 :: P5 :: nil) (list_inter (P1 :: P3 :: P5 :: nil) (P1 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P4 :: P5 :: nil) (P1 :: P3 :: P5 :: P1 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P5 :: P1 :: P4 :: P5 :: nil) ((P1 :: P3 :: P5 :: nil) ++ (P1 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P4P5mtmp;try rewrite HT2 in HP1P3P4P5mtmp.
	assert(HT := rule_2 (P1 :: P3 :: P5 :: nil) (P1 :: P4 :: P5 :: nil) (P1 :: P5 :: nil) 3 2 2 HP1P3P4P5mtmp HP1P5mtmp HP1P4P5Mtmp Hincl);apply HT.
}
try clear HP1P3P5m2. try clear HP1P3P4P5M3. try clear HP1P3P4P5m3. 

assert(HP1P3P5P8m2 : rk(P1 :: P3 :: P5 :: P8 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P8 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P8m1. 

assert(HP1P3P5P8m3 : rk(P1 :: P3 :: P5 :: P8 :: nil) >= 3).
{
	assert(HP1P3P5mtmp : rk(P1 :: P3 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P3P5eq HP1P3P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P5 :: nil) (P1 :: P3 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P5 :: nil) (P1 :: P3 :: P5 :: P8 :: nil) 3 3 HP1P3P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P8m2. 

assert(HP1P3P5P8m4 : rk(P1 :: P3 :: P5 :: P8 :: nil) >= 4).
{
	assert(HP1P4P5P8Mtmp : rk(P1 :: P4 :: P5 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P4P5P8eq HP1P4P5P8M3).
	assert(HP1P3P4P5P8mtmp : rk(P1 :: P3 :: P4 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P3P4P5P8eq HP1P3P4P5P8m4).
	assert(HP1P5P8mtmp : rk(P1 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P5P8eq HP1P5P8m3).
	assert(Hincl : incl (P1 :: P5 :: P8 :: nil) (list_inter (P1 :: P3 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P4 :: P5 :: P8 :: nil) (P1 :: P3 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P5 :: P8 :: P1 :: P4 :: P5 :: P8 :: nil) ((P1 :: P3 :: P5 :: P8 :: nil) ++ (P1 :: P4 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P4P5P8mtmp;try rewrite HT2 in HP1P3P4P5P8mtmp.
	assert(HT := rule_2 (P1 :: P3 :: P5 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: nil) (P1 :: P5 :: P8 :: nil) 4 3 3 HP1P3P4P5P8mtmp HP1P5P8mtmp HP1P4P5P8Mtmp Hincl);apply HT.
}
try clear HP1P3P5P8m3. try clear HP1P3P4P5P8M4. try clear HP1P3P4P5P8m4. 

assert(HP1P3P5P6P8m2 : rk(P1 :: P3 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: P8 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P6P8m1. 

assert(HP1P3P5P6P8m3 : rk(P1 :: P3 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P3P5mtmp : rk(P1 :: P3 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P3P5eq HP1P3P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P5 :: nil) (P1 :: P3 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P5 :: nil) (P1 :: P3 :: P5 :: P6 :: P8 :: nil) 3 3 HP1P3P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P6P8m2. 

assert(HP1P3P5P6P8m4 : rk(P1 :: P3 :: P5 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP1P3P5P8mtmp : rk(P1 :: P3 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P3P5P8eq HP1P3P5P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P5 :: P8 :: nil) (P1 :: P3 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P5 :: P8 :: nil) (P1 :: P3 :: P5 :: P6 :: P8 :: nil) 4 4 HP1P3P5P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5P8M4. try clear HP1P3P5P8m4. try clear HP1P3P5P6P8m3. 

assert(HP1P2P4P5P6P8m2 : rk(P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P6P8m1. 

assert(HP1P2P4P5P6P8m3 : rk(P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P5P6P8m2. 

assert(HP1P2P4P5P6P8m4 : rk(P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}


assert(HP2P4P5P6P8m2 : rk(P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP2P4mtmp : rk(P2 :: P4 :: nil) >= 2) by (solve_hyps_min HP2P4eq HP2P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P4 :: nil) (P2 :: P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P4 :: nil) (P2 :: P4 :: P5 :: P6 :: P8 :: nil) 2 2 HP2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP2P4M2. try clear HP2P4m2. try clear HP2P4P5P6P8m1. 

assert(HP2P4P5P6P8m3 : rk(P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P4P5Mtmp : rk(P1 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P4P5eq HP1P4P5M2).
	assert(HP1P2P4P5P6P8mtmp : rk(P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P4P5P6P8eq HP1P2P4P5P6P8m3).
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P1 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) (P1 :: P4 :: P5 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) ((P1 :: P4 :: P5 :: nil) ++ (P2 :: P4 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P6P8mtmp;try rewrite HT2 in HP1P2P4P5P6P8mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: nil) 3 2 2 HP1P2P4P5P6P8mtmp HP4P5mtmp HP1P4P5Mtmp Hincl); apply HT.
}
try clear HP1P4P5M2. try clear HP1P4P5m2. try clear HP2P4P5P6P8m2. try clear HP1P2P4P5P6P8M4. try clear HP1P2P4P5P6P8m3. 

assert(HP2P4P5P6P8m4 : rk(P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP1P4P5P8Mtmp : rk(P1 :: P4 :: P5 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P4P5P8eq HP1P4P5P8M3).
	assert(HP1P2P4P5P6P8mtmp : rk(P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P5P6P8eq HP1P2P4P5P6P8m4).
	assert(HP4P5P8mtmp : rk(P4 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P8eq HP4P5P8m3).
	assert(Hincl : incl (P4 :: P5 :: P8 :: nil) (list_inter (P1 :: P4 :: P5 :: P8 :: nil) (P2 :: P4 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) (P1 :: P4 :: P5 :: P8 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P5 :: P8 :: P2 :: P4 :: P5 :: P6 :: P8 :: nil) ((P1 :: P4 :: P5 :: P8 :: nil) ++ (P2 :: P4 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P5P6P8mtmp;try rewrite HT2 in HP1P2P4P5P6P8mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P5 :: P8 :: nil) (P2 :: P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: P8 :: nil) 4 3 3 HP1P2P4P5P6P8mtmp HP4P5P8mtmp HP1P4P5P8Mtmp Hincl); apply HT.
}
try clear HP1P4P5P8M3. try clear HP1P4P5P8m3. try clear HP4P5P8M3. try clear HP4P5P8m3. try clear HP1P2P4P5P6P8M4. try clear HP1P2P4P5P6P8m4. 

assert(HP5P6P8m2 : rk(P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP2P4P6Mtmp : rk(P2 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP2P4P6eq HP2P4P6M2).
	assert(HP2P4P5P6P8mtmp : rk(P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P4P5P6P8eq HP2P4P5P6P8m3).
	assert(HP6mtmp : rk(P6 :: nil) >= 1) by (solve_hyps_min HP6eq HP6m1).
	assert(Hincl : incl (P6 :: nil) (list_inter (P2 :: P4 :: P6 :: nil) (P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P5 :: P6 :: P8 :: nil) (P2 :: P4 :: P6 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P6 :: P5 :: P6 :: P8 :: nil) ((P2 :: P4 :: P6 :: nil) ++ (P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P5P6P8mtmp;try rewrite HT2 in HP2P4P5P6P8mtmp.
	assert(HT := rule_4 (P2 :: P4 :: P6 :: nil) (P5 :: P6 :: P8 :: nil) (P6 :: nil) 3 1 2 HP2P4P5P6P8mtmp HP6mtmp HP2P4P6Mtmp Hincl); apply HT.
}
try clear HP2P4P6M2. try clear HP2P4P6m2. try clear HP5P6P8m1. try clear HP6M1. try clear HP6m1. try clear HP2P4P5P6P8M4. try clear HP2P4P5P6P8m3. 

assert(HP5P6P8m3 : rk(P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP2P4P6P8Mtmp : rk(P2 :: P4 :: P6 :: P8 :: nil) <= 3) by (solve_hyps_max HP2P4P6P8eq HP2P4P6P8M3).
	assert(HP2P4P5P6P8mtmp : rk(P2 :: P4 :: P5 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP2P4P5P6P8eq HP2P4P5P6P8m4).
	assert(HP6P8mtmp : rk(P6 :: P8 :: nil) >= 2) by (solve_hyps_min HP6P8eq HP6P8m2).
	assert(Hincl : incl (P6 :: P8 :: nil) (list_inter (P2 :: P4 :: P6 :: P8 :: nil) (P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P5 :: P6 :: P8 :: nil) (P2 :: P4 :: P6 :: P8 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P6 :: P8 :: P5 :: P6 :: P8 :: nil) ((P2 :: P4 :: P6 :: P8 :: nil) ++ (P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P5P6P8mtmp;try rewrite HT2 in HP2P4P5P6P8mtmp.
	assert(HT := rule_4 (P2 :: P4 :: P6 :: P8 :: nil) (P5 :: P6 :: P8 :: nil) (P6 :: P8 :: nil) 4 2 3 HP2P4P5P6P8mtmp HP6P8mtmp HP2P4P6P8Mtmp Hincl); apply HT.
}
try clear HP2P4P6P8M3. try clear HP2P4P6P8m3. try clear HP5P6P8m2. try clear HP6P8M2. try clear HP6P8m2. try clear HP2P4P5P6P8M4. try clear HP2P4P5P6P8m4. 

assert(HP1P3P5P6M3 : rk(P1 :: P3 :: P5 :: P6 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP3P5P6Mtmp : rk(P3 :: P5 :: P6 :: nil) <= 2) by (solve_hyps_max HP3P5P6eq HP3P5P6M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P3 :: P5 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P5 :: P6 :: nil) (P1 :: P3 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P5 :: P6 :: nil) ((P1 :: nil) ++ (P3 :: P5 :: P6 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P3 :: P5 :: P6 :: nil) (nil) 1 2 0 HP1Mtmp HP3P5P6Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P3P5P6M4. 

assert(HP1P3P5P6m2 : rk(P1 :: P3 :: P5 :: P6 :: nil) >= 2).
{
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P3 :: P5 :: P6 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3M2. try clear HP1P3m2. try clear HP1P3P5P6m1. 

assert(HP1P3P5P6m3 : rk(P1 :: P3 :: P5 :: P6 :: nil) >= 3).
{
	assert(HP1P3P5mtmp : rk(P1 :: P3 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P3P5eq HP1P3P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: P5 :: nil) (P1 :: P3 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: P5 :: nil) (P1 :: P3 :: P5 :: P6 :: nil) 3 3 HP1P3P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P3P5M3. try clear HP1P3P5m3. try clear HP1P3P5P6m2. 

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
try clear HP4M1. try clear HP4m1. try clear HP5P6m1. try clear HP4P5P6M3. try clear HP4P5P6m3. 

assert(HP1P5P6m2 : rk(P1 :: P5 :: P6 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P6 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6m1. 

assert(HP1P5P6m3 : rk(P1 :: P5 :: P6 :: nil) >= 3).
{
	assert(HP3P5P6Mtmp : rk(P3 :: P5 :: P6 :: nil) <= 2) by (solve_hyps_max HP3P5P6eq HP3P5P6M2).
	assert(HP1P3P5P6mtmp : rk(P1 :: P3 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P3P5P6eq HP1P3P5P6m3).
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hincl : incl (P5 :: P6 :: nil) (list_inter (P1 :: P5 :: P6 :: nil) (P3 :: P5 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P3 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P5 :: P6 :: P3 :: P5 :: P6 :: nil) ((P1 :: P5 :: P6 :: nil) ++ (P3 :: P5 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P5P6mtmp;try rewrite HT2 in HP1P3P5P6mtmp.
	assert(HT := rule_2 (P1 :: P5 :: P6 :: nil) (P3 :: P5 :: P6 :: nil) (P5 :: P6 :: nil) 3 2 2 HP1P3P5P6mtmp HP5P6mtmp HP3P5P6Mtmp Hincl);apply HT.
}
try clear HP1P5P6m2. try clear HP3P5P6M2. try clear HP3P5P6m2. try clear HP5P6M2. try clear HP5P6m2. try clear HP1P3P5P6M3. try clear HP1P3P5P6m3. 

assert(HP1P5P6P8m2 : rk(P1 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P6 :: P8 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6P8m1. 

assert(HP1P5P6P8m3 : rk(P1 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	assert(HP1P5P6mtmp : rk(P1 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P5P6eq HP1P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P8 :: nil) 3 3 HP1P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6P8m2. 

assert(HP1P5P6P8m4 : rk(P1 :: P5 :: P6 :: P8 :: nil) >= 4).
{
	assert(HP3P5P6P8Mtmp : rk(P3 :: P5 :: P6 :: P8 :: nil) <= 3) by (solve_hyps_max HP3P5P6P8eq HP3P5P6P8M3).
	assert(HP1P3P5P6P8mtmp : rk(P1 :: P3 :: P5 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P3P5P6P8eq HP1P3P5P6P8m4).
	assert(HP5P6P8mtmp : rk(P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP5P6P8eq HP5P6P8m3).
	assert(Hincl : incl (P5 :: P6 :: P8 :: nil) (list_inter (P1 :: P5 :: P6 :: P8 :: nil) (P3 :: P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P3 :: P5 :: P6 :: P8 :: nil) (P1 :: P5 :: P6 :: P8 :: P3 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P5 :: P6 :: P8 :: P3 :: P5 :: P6 :: P8 :: nil) ((P1 :: P5 :: P6 :: P8 :: nil) ++ (P3 :: P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P3P5P6P8mtmp;try rewrite HT2 in HP1P3P5P6P8mtmp.
	assert(HT := rule_2 (P1 :: P5 :: P6 :: P8 :: nil) (P3 :: P5 :: P6 :: P8 :: nil) (P5 :: P6 :: P8 :: nil) 4 3 3 HP1P3P5P6P8mtmp HP5P6P8mtmp HP3P5P6P8Mtmp Hincl);apply HT.
}
try clear HP1P5P6P8m3. try clear HP3P5P6P8M3. try clear HP3P5P6P8m3. try clear HP5P6P8M3. try clear HP5P6P8m3. try clear HP1P3P5P6P8M4. try clear HP1P3P5P6P8m4. 

assert(HP1P5P6P7P8m2 : rk(P1 :: P5 :: P6 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P6 :: P7 :: P8 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6P7P8m1. 

assert(HP1P5P6P7P8m3 : rk(P1 :: P5 :: P6 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P5P6mtmp : rk(P1 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P5P6eq HP1P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P7 :: P8 :: nil) 3 3 HP1P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6P7P8m2. 

assert(HP1P5P6P7P8m4 : rk(P1 :: P5 :: P6 :: P7 :: P8 :: nil) >= 4).
{
	assert(HP1P5P6P8mtmp : rk(P1 :: P5 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P5P6P8eq HP1P5P6P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: P6 :: P8 :: nil) (P1 :: P5 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: P6 :: P8 :: nil) (P1 :: P5 :: P6 :: P7 :: P8 :: nil) 4 4 HP1P5P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6P8M4. try clear HP1P5P6P8m4. try clear HP1P5P6P7P8m3. 

assert(HP1P5P6P7M3 : rk(P1 :: P5 :: P6 :: P7 :: nil) <= 3).
{
	assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M1).
	assert(HP1P6P7Mtmp : rk(P1 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P6P7eq HP1P6P7M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: nil) (P1 :: P6 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P6 :: P7 :: nil) (P5 :: P1 :: P6 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P1 :: P6 :: P7 :: nil) ((P5 :: nil) ++ (P1 :: P6 :: P7 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: nil) (P1 :: P6 :: P7 :: nil) (nil) 1 2 0 HP5Mtmp HP1P6P7Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP5M1. try clear HP5m1. try clear HP1P5P6P7M4. 

assert(HP1P5P6P7m2 : rk(P1 :: P5 :: P6 :: P7 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P6 :: P7 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6P7m1. 

assert(HP1P5P6P7m3 : rk(P1 :: P5 :: P6 :: P7 :: nil) >= 3).
{
	assert(HP1P5P6mtmp : rk(P1 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P5P6eq HP1P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: P6 :: nil) (P1 :: P5 :: P6 :: P7 :: nil) 3 3 HP1P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P6M3. try clear HP1P5P6m3. try clear HP1P5P6P7m2. 

assert(HP5P7m2 : rk(P5 :: P7 :: nil) >= 2).
{
	assert(HP1P6P7Mtmp : rk(P1 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P6P7eq HP1P6P7M2).
	assert(HP1P5P6P7mtmp : rk(P1 :: P5 :: P6 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P5P6P7eq HP1P5P6P7m3).
	assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m1).
	assert(Hincl : incl (P7 :: nil) (list_inter (P5 :: P7 :: nil) (P1 :: P6 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P6 :: P7 :: nil) (P5 :: P7 :: P1 :: P6 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P7 :: P1 :: P6 :: P7 :: nil) ((P5 :: P7 :: nil) ++ (P1 :: P6 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P5P6P7mtmp;try rewrite HT2 in HP1P5P6P7mtmp.
	assert(HT := rule_2 (P5 :: P7 :: nil) (P1 :: P6 :: P7 :: nil) (P7 :: nil) 3 1 2 HP1P5P6P7mtmp HP7mtmp HP1P6P7Mtmp Hincl);apply HT.
}
try clear HP5P7m1. try clear HP1P6P7M2. try clear HP1P6P7m2. try clear HP1P5P6P7M3. try clear HP1P5P6P7m3. 

assert(HP5P7P8m2 : rk(P5 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P7 :: nil) (P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P7 :: nil) (P5 :: P7 :: P8 :: nil) 2 2 HP5P7mtmp Hcomp Hincl);apply HT.
}
try clear HP5P7P8m1. 

assert(HP5P7P8m3 : rk(P5 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P6P7P8Mtmp : rk(P1 :: P6 :: P7 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P6P7P8eq HP1P6P7P8M3).
	assert(HP1P5P6P7P8mtmp : rk(P1 :: P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P5P6P7P8eq HP1P5P6P7P8m4).
	assert(HP7P8mtmp : rk(P7 :: P8 :: nil) >= 2) by (solve_hyps_min HP7P8eq HP7P8m2).
	assert(Hincl : incl (P7 :: P8 :: nil) (list_inter (P5 :: P7 :: P8 :: nil) (P1 :: P6 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P6 :: P7 :: P8 :: nil) (P5 :: P7 :: P8 :: P1 :: P6 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P7 :: P8 :: P1 :: P6 :: P7 :: P8 :: nil) ((P5 :: P7 :: P8 :: nil) ++ (P1 :: P6 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P5P6P7P8mtmp;try rewrite HT2 in HP1P5P6P7P8mtmp.
	assert(HT := rule_2 (P5 :: P7 :: P8 :: nil) (P1 :: P6 :: P7 :: P8 :: nil) (P7 :: P8 :: nil) 4 2 3 HP1P5P6P7P8mtmp HP7P8mtmp HP1P6P7P8Mtmp Hincl);apply HT.
}
try clear HP5P7P8m2. try clear HP1P6P7P8M3. try clear HP1P6P7P8m3. try clear HP1P5P6P7P8M4. try clear HP1P5P6P7P8m4. 

assert(HP1P5P7m2 : rk(P1 :: P5 :: P7 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P7 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P7m1. 

assert(HP1P5P7m3 : rk(P1 :: P5 :: P7 :: nil) >= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP1P2P5P7mtmp : rk(P1 :: P2 :: P5 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P5P7eq HP1P2P5P7m3).
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hincl : incl (P5 :: P7 :: nil) (list_inter (P1 :: P5 :: P7 :: nil) (P2 :: P5 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P7 :: nil) (P1 :: P5 :: P7 :: P2 :: P5 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P5 :: P7 :: P2 :: P5 :: P7 :: nil) ((P1 :: P5 :: P7 :: nil) ++ (P2 :: P5 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P7mtmp;try rewrite HT2 in HP1P2P5P7mtmp.
	assert(HT := rule_2 (P1 :: P5 :: P7 :: nil) (P2 :: P5 :: P7 :: nil) (P5 :: P7 :: nil) 3 2 2 HP1P2P5P7mtmp HP5P7mtmp HP2P5P7Mtmp Hincl);apply HT.
}
try clear HP1P5P7m2. try clear HP1P2P5P7M3. try clear HP1P2P5P7m3. 

assert(HP1P5P7P8m2 : rk(P1 :: P5 :: P7 :: P8 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P7 :: P8 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P7P8m1. 

assert(HP1P5P7P8m3 : rk(P1 :: P5 :: P7 :: P8 :: nil) >= 3).
{
	assert(HP1P5P7mtmp : rk(P1 :: P5 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P5P7eq HP1P5P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: P7 :: nil) (P1 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: P7 :: nil) (P1 :: P5 :: P7 :: P8 :: nil) 3 3 HP1P5P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P7P8m2. 

assert(HP1P5P7P8m4 : rk(P1 :: P5 :: P7 :: P8 :: nil) >= 4).
{
	assert(HP2P5P7P8Mtmp : rk(P2 :: P5 :: P7 :: P8 :: nil) <= 3) by (solve_hyps_max HP2P5P7P8eq HP2P5P7P8M3).
	assert(HP1P2P5P7P8mtmp : rk(P1 :: P2 :: P5 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P5P7P8eq HP1P2P5P7P8m4).
	assert(HP5P7P8mtmp : rk(P5 :: P7 :: P8 :: nil) >= 3) by (solve_hyps_min HP5P7P8eq HP5P7P8m3).
	assert(Hincl : incl (P5 :: P7 :: P8 :: nil) (list_inter (P1 :: P5 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P7 :: P8 :: nil) (P1 :: P5 :: P7 :: P8 :: P2 :: P5 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P5 :: P7 :: P8 :: P2 :: P5 :: P7 :: P8 :: nil) ((P1 :: P5 :: P7 :: P8 :: nil) ++ (P2 :: P5 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P7P8mtmp;try rewrite HT2 in HP1P2P5P7P8mtmp.
	assert(HT := rule_2 (P1 :: P5 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P8 :: nil) (P5 :: P7 :: P8 :: nil) 4 3 3 HP1P2P5P7P8mtmp HP5P7P8mtmp HP2P5P7P8Mtmp Hincl);apply HT.
}
try clear HP1P5P7P8m3. try clear HP2P5P7P8M3. try clear HP2P5P7P8m3. try clear HP5P7P8M3. try clear HP5P7P8m3. try clear HP1P2P5P7P8M4. try clear HP1P2P5P7P8m4. 

assert(HP1P5P7P8P9m2 : rk(P1 :: P5 :: P7 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P7 :: P8 :: P9 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P7P8P9m1. 

assert(HP1P5P7P8P9m3 : rk(P1 :: P5 :: P7 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P5P7mtmp : rk(P1 :: P5 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P5P7eq HP1P5P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: P7 :: nil) (P1 :: P5 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: P7 :: nil) (P1 :: P5 :: P7 :: P8 :: P9 :: nil) 3 3 HP1P5P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P7M3. try clear HP1P5P7m3. try clear HP1P5P7P8P9m2. 

assert(HP1P5P7P8P9m4 : rk(P1 :: P5 :: P7 :: P8 :: P9 :: nil) >= 4).
{
	assert(HP1P5P7P8mtmp : rk(P1 :: P5 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P5P7P8eq HP1P5P7P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: P7 :: P8 :: nil) (P1 :: P5 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: P7 :: P8 :: nil) (P1 :: P5 :: P7 :: P8 :: P9 :: nil) 4 4 HP1P5P7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P7P8M4. try clear HP1P5P7P8m4. try clear HP1P5P7P8P9m3. 

assert(HP5P7P9m2 : rk(P5 :: P7 :: P9 :: nil) >= 2).
{
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P7 :: nil) (P5 :: P7 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P7 :: nil) (P5 :: P7 :: P9 :: nil) 2 2 HP5P7mtmp Hcomp Hincl);apply HT.
}
try clear HP5P7P9m1. 

assert(HP5P7P9m3 : rk(P5 :: P7 :: P9 :: nil) >= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P5P7P8P9mtmp : rk(P1 :: P5 :: P7 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P5P7P8P9eq HP1P5P7P8P9m4).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P5 :: P7 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P7 :: P8 :: P9 :: nil) (P5 :: P7 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P7 :: P9 :: P1 :: P8 :: P9 :: nil) ((P5 :: P7 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P5P7P8P9mtmp;try rewrite HT2 in HP1P5P7P8P9mtmp.
	assert(HT := rule_2 (P5 :: P7 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P9 :: nil) 4 1 2 HP1P5P7P8P9mtmp HP9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP5P7P9m2. try clear HP1P5P7P8P9M4. try clear HP1P5P7P8P9m4. 

assert(HP1P2P5P7P8P9m2 : rk(P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P7P8P9m1. 

assert(HP1P2P5P7P8P9m3 : rk(P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil) >= 3).
{
	assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5M3. try clear HP1P2P5m3. try clear HP1P2P5P7P8P9m2. 

assert(HP1P2P5P7P8P9m4 : rk(P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil) >= 4).
{
	assert(HP1P2P5P8mtmp : rk(P1 :: P2 :: P5 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P5P8eq HP1P2P5P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: P8 :: nil) (P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil) 4 4 HP1P2P5P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P5P8M4. try clear HP1P2P5P8m4. try clear HP1P2P5P7P8P9m3. 

assert(HP2P5P7P9m2 : rk(P2 :: P5 :: P7 :: P9 :: nil) >= 2).
{
	assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P5 :: P7 :: P9 :: nil) 2 2 HP2P5mtmp Hcomp Hincl);apply HT.
}
try clear HP2P5M2. try clear HP2P5m2. try clear HP2P5P7P9m1. 

assert(HP2P5P7P9M3 : rk(P2 :: P5 :: P7 :: P9 :: nil) <= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP9Mtmp : rk(P9 :: nil) <= 1) by (solve_hyps_max HP9eq HP9M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: P5 :: P7 :: nil) (P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P5 :: P7 :: P9 :: nil) (P2 :: P5 :: P7 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P9 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P5 :: P7 :: nil) (P9 :: nil) (nil) 2 1 0 HP2P5P7Mtmp HP9Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P5P7P9M4. 

assert(HP2P5P7P9m3 : rk(P2 :: P5 :: P7 :: P9 :: nil) >= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P2P5P7P8P9mtmp : rk(P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P5P7P8P9eq HP1P2P5P7P8P9m4).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P2 :: P5 :: P7 :: P9 :: nil) (P1 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: P7 :: P8 :: P9 :: nil) (P2 :: P5 :: P7 :: P9 :: P1 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P9 :: P1 :: P8 :: P9 :: nil) ((P2 :: P5 :: P7 :: P9 :: nil) ++ (P1 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5P7P8P9mtmp;try rewrite HT2 in HP1P2P5P7P8P9mtmp.
	assert(HT := rule_2 (P2 :: P5 :: P7 :: P9 :: nil) (P1 :: P8 :: P9 :: nil) (P9 :: nil) 4 1 2 HP1P2P5P7P8P9mtmp HP9mtmp HP1P8P9Mtmp Hincl);apply HT.
}
try clear HP2P5P7P9m2. try clear HP1P2P5P7P8P9M4. try clear HP1P2P5P7P8P9m4. 

assert(HP4P5P7P9P12P14m2 : rk(P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) 2 2 HP4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5M2. try clear HP4P5m2. try clear HP4P5P7P9P12P14m1. 

assert(HP4P5P7P9P12P14m3 : rk(P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M2).
	assert(HP2P4P5P7P9P12P14mtmp : rk(P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 3) by (solve_hyps_min HP2P4P5P7P9P12P14eq HP2P4P5P7P9P12P14m3).
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hincl : incl (P5 :: P7 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P2 :: P5 :: P7 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P5P7P9P12P14mtmp;try rewrite HT2 in HP2P4P5P7P9P12P14mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P7 :: nil) (P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P5 :: P7 :: nil) 3 2 2 HP2P4P5P7P9P12P14mtmp HP5P7mtmp HP2P5P7Mtmp Hincl); apply HT.
}
try clear HP2P5P7M2. try clear HP2P5P7m2. try clear HP4P5P7P9P12P14m2. try clear HP2P4P5P7P9P12P14M4. try clear HP2P4P5P7P9P12P14m3. 

assert(HP4P5P7P9P12P14m4 : rk(P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 4).
{
	assert(HP2P5P7P9Mtmp : rk(P2 :: P5 :: P7 :: P9 :: nil) <= 3) by (solve_hyps_max HP2P5P7P9eq HP2P5P7P9M3).
	assert(HP2P4P5P7P9P12P14mtmp : rk(P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 4) by (solve_hyps_min HP2P4P5P7P9P12P14eq HP2P4P5P7P9P12P14m4).
	assert(HP5P7P9mtmp : rk(P5 :: P7 :: P9 :: nil) >= 3) by (solve_hyps_min HP5P7P9eq HP5P7P9m3).
	assert(Hincl : incl (P5 :: P7 :: P9 :: nil) (list_inter (P2 :: P5 :: P7 :: P9 :: nil) (P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P2 :: P5 :: P7 :: P9 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P9 :: P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) ((P2 :: P5 :: P7 :: P9 :: nil) ++ (P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P4P5P7P9P12P14mtmp;try rewrite HT2 in HP2P4P5P7P9P12P14mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P7 :: P9 :: nil) (P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P5 :: P7 :: P9 :: nil) 4 3 3 HP2P4P5P7P9P12P14mtmp HP5P7P9mtmp HP2P5P7P9Mtmp Hincl); apply HT.
}
try clear HP2P5P7P9M3. try clear HP2P5P7P9m3. try clear HP4P5P7P9P12P14m3. try clear HP2P4P5P7P9P12P14M4. try clear HP2P4P5P7P9P12P14m4. 

assert(HP1P2P3P7P12P13m2 : rk(P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P7P12P13m1. 

assert(HP1P2P3P7P12P13M3 : rk(P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil) <= 3).
{
	assert(HP7Mtmp : rk(P7 :: nil) <= 1) by (solve_hyps_max HP7eq HP7M1).
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P7 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil) (P7 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P7 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P7 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (nil) 1 2 0 HP7Mtmp HP1P2P3P12P13Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP7M1. try clear HP7m1. try clear HP1P2P3P7P12P13M4. 

assert(HP1P2P3P7P12P13m3 : rk(P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P7P12P13m2. 

assert(HP7P12m2 : rk(P7 :: P12 :: nil) >= 2).
{
	assert(HP1P2P3P12P13Mtmp : rk(P1 :: P2 :: P3 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P12P13eq HP1P2P3P12P13M2).
	assert(HP1P2P3P7P12P13mtmp : rk(P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil) >= 3) by (solve_hyps_min HP1P2P3P7P12P13eq HP1P2P3P7P12P13m3).
	assert(HP12mtmp : rk(P12 :: nil) >= 1) by (solve_hyps_min HP12eq HP12m1).
	assert(Hincl : incl (P12 :: nil) (list_inter (P7 :: P12 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P7 :: P12 :: P13 :: nil) (P7 :: P12 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P12 :: P1 :: P2 :: P3 :: P12 :: P13 :: nil) ((P7 :: P12 :: nil) ++ (P1 :: P2 :: P3 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P7P12P13mtmp;try rewrite HT2 in HP1P2P3P7P12P13mtmp.
	assert(HT := rule_2 (P7 :: P12 :: nil) (P1 :: P2 :: P3 :: P12 :: P13 :: nil) (P12 :: nil) 3 1 2 HP1P2P3P7P12P13mtmp HP12mtmp HP1P2P3P12P13Mtmp Hincl);apply HT.
}
try clear HP7P12m1. try clear HP1P2P3P12P13M2. try clear HP1P2P3P12P13m2. try clear HP1P2P3P7P12P13M3. try clear HP1P2P3P7P12P13m3. 

assert(HP5P7P9P12P14m2 : rk(P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP5P7mtmp : rk(P5 :: P7 :: nil) >= 2) by (solve_hyps_min HP5P7eq HP5P7m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P7 :: nil) (P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P7 :: nil) (P5 :: P7 :: P9 :: P12 :: P14 :: nil) 2 2 HP5P7mtmp Hcomp Hincl);apply HT.
}
try clear HP5P7M2. try clear HP5P7m2. try clear HP5P7P9P12P14m1. 

assert(HP5P7P9P12P14m3 : rk(P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP5P7P9mtmp : rk(P5 :: P7 :: P9 :: nil) >= 3) by (solve_hyps_min HP5P7P9eq HP5P7P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P5 :: P7 :: P9 :: nil) (P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P7 :: P9 :: nil) (P5 :: P7 :: P9 :: P12 :: P14 :: nil) 3 3 HP5P7P9mtmp Hcomp Hincl);apply HT.
}
try clear HP5P7P9M3. try clear HP5P7P9m3. try clear HP5P7P9P12P14m2. 

assert(HP5P7P9P12P14m4 : rk(P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 4).
{
	assert(HP4P7P12Mtmp : rk(P4 :: P7 :: P12 :: nil) <= 2) by (solve_hyps_max HP4P7P12eq HP4P7P12M2).
	assert(HP4P5P7P9P12P14mtmp : rk(P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 4) by (solve_hyps_min HP4P5P7P9P12P14eq HP4P5P7P9P12P14m4).
	assert(HP7P12mtmp : rk(P7 :: P12 :: nil) >= 2) by (solve_hyps_min HP7P12eq HP7P12m2).
	assert(Hincl : incl (P7 :: P12 :: nil) (list_inter (P4 :: P7 :: P12 :: nil) (P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P4 :: P7 :: P12 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P7 :: P12 :: P5 :: P7 :: P9 :: P12 :: P14 :: nil) ((P4 :: P7 :: P12 :: nil) ++ (P5 :: P7 :: P9 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P7P9P12P14mtmp;try rewrite HT2 in HP4P5P7P9P12P14mtmp.
	assert(HT := rule_4 (P4 :: P7 :: P12 :: nil) (P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P7 :: P12 :: nil) 4 2 2 HP4P5P7P9P12P14mtmp HP7P12mtmp HP4P7P12Mtmp Hincl); apply HT.
}
try clear HP4P7P12M2. try clear HP4P7P12m2. try clear HP5P7P9P12P14m3. try clear HP7P12M2. try clear HP7P12m2. try clear HP4P5P7P9P12P14M4. try clear HP4P5P7P9P12P14m4. 

assert(HP1P2P7P12P14m2 : rk(P1 :: P2 :: P7 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P12 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P12P14m1. 

assert(HP1P2P7P12P14m3 : rk(P1 :: P2 :: P7 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P12 :: P14 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P12P14m2. 

assert(HP7P12P14m2 : rk(P7 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP1P2P12Mtmp : rk(P1 :: P2 :: P12 :: nil) <= 2) by (solve_hyps_max HP1P2P12eq HP1P2P12M2).
	assert(HP1P2P7P12P14mtmp : rk(P1 :: P2 :: P7 :: P12 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P2P7P12P14eq HP1P2P7P12P14m3).
	assert(HP12mtmp : rk(P12 :: nil) >= 1) by (solve_hyps_min HP12eq HP12m1).
	assert(Hincl : incl (P12 :: nil) (list_inter (P1 :: P2 :: P12 :: nil) (P7 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P12 :: P14 :: nil) (P1 :: P2 :: P12 :: P7 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P12 :: P7 :: P12 :: P14 :: nil) ((P1 :: P2 :: P12 :: nil) ++ (P7 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P12P14mtmp;try rewrite HT2 in HP1P2P7P12P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P12 :: nil) (P7 :: P12 :: P14 :: nil) (P12 :: nil) 3 1 2 HP1P2P7P12P14mtmp HP12mtmp HP1P2P12Mtmp Hincl); apply HT.
}
try clear HP1P2P12M2. try clear HP1P2P12m2. try clear HP7P12P14m1. try clear HP12M1. try clear HP12m1. try clear HP1P2P7P12P14M4. try clear HP1P2P7P12P14m3. 

assert(HP7P12P14m3 : rk(P7 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(HP5P7P9P12P14mtmp : rk(P5 :: P7 :: P9 :: P12 :: P14 :: nil) >= 4) by (solve_hyps_min HP5P7P9P12P14eq HP5P7P9P12P14m4).
	assert(HP14mtmp : rk(P14 :: nil) >= 1) by (solve_hyps_min HP14eq HP14m1).
	assert(Hincl : incl (P14 :: nil) (list_inter (P5 :: P9 :: P14 :: nil) (P7 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P7 :: P9 :: P12 :: P14 :: nil) (P5 :: P9 :: P14 :: P7 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P9 :: P14 :: P7 :: P12 :: P14 :: nil) ((P5 :: P9 :: P14 :: nil) ++ (P7 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P7P9P12P14mtmp;try rewrite HT2 in HP5P7P9P12P14mtmp.
	assert(HT := rule_4 (P5 :: P9 :: P14 :: nil) (P7 :: P12 :: P14 :: nil) (P14 :: nil) 4 1 2 HP5P7P9P12P14mtmp HP14mtmp HP5P9P14Mtmp Hincl); apply HT.
}
try clear HP7P12P14m2. try clear HP5P7P9P12P14M4. try clear HP5P7P9P12P14m4. 

assert(HP1P2P7P8P11P12P14m2 : rk(P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8P11P12P14m1. 

assert(HP1P2P7P8P11P12P14m3 : rk(P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P2P7mtmp : rk(P1 :: P2 :: P7 :: nil) >= 3) by (solve_hyps_min HP1P2P7eq HP1P2P7m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: nil) (P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil) 3 3 HP1P2P7mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7M3. try clear HP1P2P7m3. try clear HP1P2P7P8P11P12P14m2. 

assert(HP1P2P7P8P11P12P14m4 : rk(P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil) >= 4).
{
	assert(HP1P2P7P8mtmp : rk(P1 :: P2 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8eq HP1P2P7P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P7 :: P8 :: nil) (P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P7 :: P8 :: nil) (P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil) 4 4 HP1P2P7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P7P8M4. try clear HP1P2P7P8m4. try clear HP1P2P7P8P11P12P14m3. 

assert(HP1P2P8P9P11m2 : rk(P1 :: P2 :: P8 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P8 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P8 :: P9 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P8P9P11m1. 

assert(HP1P2P8P9P11m3 : rk(P1 :: P2 :: P8 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP1P2P8mtmp : rk(P1 :: P2 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P8eq HP1P2P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P8 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P8 :: P9 :: P11 :: nil) 3 3 HP1P2P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P8P9P11m2. 

assert(HP1P2P8P9P11M3 : rk(P1 :: P2 :: P8 :: P9 :: P11 :: nil) <= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P1 :: P8 :: P9 :: nil) (P2 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P8 :: P9 :: P11 :: nil) (P1 :: P8 :: P9 :: P2 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P9 :: P2 :: P9 :: P11 :: nil) ((P1 :: P8 :: P9 :: nil) ++ (P2 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P8 :: P9 :: nil) (P2 :: P9 :: P11 :: nil) (P9 :: nil) 2 2 1 HP1P8P9Mtmp HP2P9P11Mtmp HP9mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P8P9P11M4. 

assert(HP2P8m2 : rk(P2 :: P8 :: nil) >= 2).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP1P2P8mtmp : rk(P1 :: P2 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P8eq HP1P2P8m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P8 :: nil) ((P1 :: nil) ++ (P2 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P8mtmp;try rewrite HT2 in HP1P2P8mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P8 :: nil) (nil) 3 0 1 HP1P2P8mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}
try clear HP2P8m1. 

assert(HP2P8P9P11M3 : rk(P2 :: P8 :: P9 :: P11 :: nil) <= 3).
{
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P8 :: nil) (P2 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P8 :: P9 :: P11 :: nil) (P8 :: P2 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P2 :: P9 :: P11 :: nil) ((P8 :: nil) ++ (P2 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P8 :: nil) (P2 :: P9 :: P11 :: nil) (nil) 1 2 0 HP8Mtmp HP2P9P11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2P8P9P11M4. 

assert(HP2P8P9P11m2 : rk(P2 :: P8 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP2P8mtmp : rk(P2 :: P8 :: nil) >= 2) by (solve_hyps_min HP2P8eq HP2P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P8 :: nil) (P2 :: P8 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P8 :: nil) (P2 :: P8 :: P9 :: P11 :: nil) 2 2 HP2P8mtmp Hcomp Hincl);apply HT.
}
try clear HP2P8M2. try clear HP2P8m2. try clear HP2P8P9P11m1. 

assert(HP2P8P9P11m3 : rk(P2 :: P8 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P2P8P9P11mtmp : rk(P1 :: P2 :: P8 :: P9 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P2P8P9P11eq HP1P2P8P9P11m3).
	assert(HP8P9mtmp : rk(P8 :: P9 :: nil) >= 2) by (solve_hyps_min HP8P9eq HP8P9m2).
	assert(Hincl : incl (P8 :: P9 :: nil) (list_inter (P1 :: P8 :: P9 :: nil) (P2 :: P8 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P8 :: P9 :: P11 :: nil) (P1 :: P8 :: P9 :: P2 :: P8 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P9 :: P2 :: P8 :: P9 :: P11 :: nil) ((P1 :: P8 :: P9 :: nil) ++ (P2 :: P8 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P8P9P11mtmp;try rewrite HT2 in HP1P2P8P9P11mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P9 :: nil) (P2 :: P8 :: P9 :: P11 :: nil) (P8 :: P9 :: nil) 3 2 2 HP1P2P8P9P11mtmp HP8P9mtmp HP1P8P9Mtmp Hincl); apply HT.
}
try clear HP2P8P9P11m2. 

assert(HP8P11m2 : rk(P8 :: P11 :: nil) >= 2).
{
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(HP2P8P9P11mtmp : rk(P2 :: P8 :: P9 :: P11 :: nil) >= 3) by (solve_hyps_min HP2P8P9P11eq HP2P8P9P11m3).
	assert(HP11mtmp : rk(P11 :: nil) >= 1) by (solve_hyps_min HP11eq HP11m1).
	assert(Hincl : incl (P11 :: nil) (list_inter (P8 :: P11 :: nil) (P2 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P8 :: P9 :: P11 :: nil) (P8 :: P11 :: P2 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P11 :: P2 :: P9 :: P11 :: nil) ((P8 :: P11 :: nil) ++ (P2 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P8P9P11mtmp;try rewrite HT2 in HP2P8P9P11mtmp.
	assert(HT := rule_2 (P8 :: P11 :: nil) (P2 :: P9 :: P11 :: nil) (P11 :: nil) 3 1 2 HP2P8P9P11mtmp HP11mtmp HP2P9P11Mtmp Hincl);apply HT.
}
try clear HP8P11m1. try clear HP2P8P9P11M3. try clear HP2P8P9P11m3. 

assert(HP1P2P8P11m2 : rk(P1 :: P2 :: P8 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P8 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P8 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P8P11m1. 

assert(HP1P2P8P11m3 : rk(P1 :: P2 :: P8 :: P11 :: nil) >= 3).
{
	assert(HP1P2P8mtmp : rk(P1 :: P2 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P8eq HP1P2P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P8 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P8 :: nil) (P1 :: P2 :: P8 :: P11 :: nil) 3 3 HP1P2P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P8P11m2. 

assert(HP1P2P8P11M3 : rk(P1 :: P2 :: P8 :: P11 :: nil) <= 3).
{
	assert(HP1P2P8P9P11Mtmp : rk(P1 :: P2 :: P8 :: P9 :: P11 :: nil) <= 3) by (solve_hyps_max HP1P2P8P9P11eq HP1P2P8P9P11M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P2 :: P8 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P2 :: P8 :: P9 :: P11 :: nil) 3 3 HP1P2P8P9P11Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P8P11M4. try clear HP1P2P8P9P11M3. try clear HP1P2P8P9P11m3. 

assert(HP7P8P11P12P14m2 : rk(P7 :: P8 :: P11 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP7P8mtmp : rk(P7 :: P8 :: nil) >= 2) by (solve_hyps_min HP7P8eq HP7P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P7 :: P8 :: nil) (P7 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P8 :: nil) (P7 :: P8 :: P11 :: P12 :: P14 :: nil) 2 2 HP7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP7P8M2. try clear HP7P8m2. try clear HP7P8P11P12P14m1. 

assert(HP7P8P11P12P14m3 : rk(P7 :: P8 :: P11 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P2P8P11Mtmp : rk(P1 :: P2 :: P8 :: P11 :: nil) <= 3) by (solve_hyps_max HP1P2P8P11eq HP1P2P8P11M3).
	assert(HP1P2P7P8P11P12P14mtmp : rk(P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P7P8P11P12P14eq HP1P2P7P8P11P12P14m4).
	assert(HP8P11mtmp : rk(P8 :: P11 :: nil) >= 2) by (solve_hyps_min HP8P11eq HP8P11m2).
	assert(Hincl : incl (P8 :: P11 :: nil) (list_inter (P1 :: P2 :: P8 :: P11 :: nil) (P7 :: P8 :: P11 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil) (P1 :: P2 :: P8 :: P11 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P8 :: P11 :: P7 :: P8 :: P11 :: P12 :: P14 :: nil) ((P1 :: P2 :: P8 :: P11 :: nil) ++ (P7 :: P8 :: P11 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P7P8P11P12P14mtmp;try rewrite HT2 in HP1P2P7P8P11P12P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P8 :: P11 :: nil) (P7 :: P8 :: P11 :: P12 :: P14 :: nil) (P8 :: P11 :: nil) 4 2 3 HP1P2P7P8P11P12P14mtmp HP8P11mtmp HP1P2P8P11Mtmp Hincl); apply HT.
}
try clear HP7P8P11P12P14m2. try clear HP1P2P7P8P11P12P14M4. try clear HP1P2P7P8P11P12P14m4. 

assert(HP7P8P11P12P14M3 : rk(P7 :: P8 :: P11 :: P12 :: P14 :: nil) <= 3).
{
	assert(HP7P8P12P14Mtmp : rk(P7 :: P8 :: P12 :: P14 :: nil) <= 3) by (solve_hyps_max HP7P8P12P14eq HP7P8P12P14M3).
	assert(HP7P11P12P14Mtmp : rk(P7 :: P11 :: P12 :: P14 :: nil) <= 3) by (solve_hyps_max HP7P11P12P14eq HP7P11P12P14M3).
	assert(HP7P12P14mtmp : rk(P7 :: P12 :: P14 :: nil) >= 3) by (solve_hyps_min HP7P12P14eq HP7P12P14m3).
	assert(Hincl : incl (P7 :: P12 :: P14 :: nil) (list_inter (P7 :: P8 :: P12 :: P14 :: nil) (P7 :: P11 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P7 :: P8 :: P11 :: P12 :: P14 :: nil) (P7 :: P8 :: P12 :: P14 :: P7 :: P11 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P8 :: P12 :: P14 :: P7 :: P11 :: P12 :: P14 :: nil) ((P7 :: P8 :: P12 :: P14 :: nil) ++ (P7 :: P11 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P7 :: P8 :: P12 :: P14 :: nil) (P7 :: P11 :: P12 :: P14 :: nil) (P7 :: P12 :: P14 :: nil) 3 3 3 HP7P8P12P14Mtmp HP7P11P12P14Mtmp HP7P12P14mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP7P8P12P14M3. try clear HP7P8P12P14m3. try clear HP7P11P12P14M3. try clear HP7P11P12P14m3. try clear HP7P12P14M3. try clear HP7P12P14m3. try clear HP7P8P11P12P14M4. 

assert(HP1P2P4P8P11P12P14m2 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P12P14m1. 

assert(HP1P2P4P8P11P12P14m3 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P12P14m2. 

assert(HP1P2P4P8P11P12P14m4 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P12P14m3. 

assert(HP1P8m2 : rk(P1 :: P8 :: nil) >= 2).
{
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	assert(HP1P2P8mtmp : rk(P1 :: P2 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P2P8eq HP1P2P8m3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P8 :: nil) (P2 :: P1 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P8 :: nil) ((P2 :: nil) ++ (P1 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P8mtmp;try rewrite HT2 in HP1P2P8mtmp.
	assert(HT := rule_4 (P2 :: nil) (P1 :: P8 :: nil) (nil) 3 0 1 HP1P2P8mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}
try clear HP2M1. try clear HP2m1. try clear HP1P8m1. try clear HP1P2P8M3. try clear HP1P2P8m3. 

assert(HP1P8P10m2 : rk(P1 :: P8 :: P10 :: nil) >= 2).
{
	assert(HP1P8mtmp : rk(P1 :: P8 :: nil) >= 2) by (solve_hyps_min HP1P8eq HP1P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P8 :: nil) (P1 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P8 :: nil) (P1 :: P8 :: P10 :: nil) 2 2 HP1P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P8P10m1. 

assert(HP1P8P10m3 : rk(P1 :: P8 :: P10 :: nil) >= 3).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP1P2P8P10mtmp : rk(P1 :: P2 :: P8 :: P10 :: nil) >= 3) by (solve_hyps_min HP1P2P8P10eq HP1P2P8P10m3).
	assert(HP8P10mtmp : rk(P8 :: P10 :: nil) >= 2) by (solve_hyps_min HP8P10eq HP8P10m2).
	assert(Hincl : incl (P8 :: P10 :: nil) (list_inter (P1 :: P8 :: P10 :: nil) (P2 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P8 :: P10 :: nil) (P1 :: P8 :: P10 :: P2 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P10 :: P2 :: P8 :: P10 :: nil) ((P1 :: P8 :: P10 :: nil) ++ (P2 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P8P10mtmp;try rewrite HT2 in HP1P2P8P10mtmp.
	assert(HT := rule_2 (P1 :: P8 :: P10 :: nil) (P2 :: P8 :: P10 :: nil) (P8 :: P10 :: nil) 3 2 2 HP1P2P8P10mtmp HP8P10mtmp HP2P8P10Mtmp Hincl);apply HT.
}
try clear HP1P8P10m2. try clear HP1P2P8P10M3. try clear HP1P2P8P10m3. 

assert(HP1P8P10P11M3 : rk(P1 :: P8 :: P10 :: P11 :: nil) <= 3).
{
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(HP1P10P11Mtmp : rk(P1 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP1P10P11eq HP1P10P11M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P8 :: nil) (P1 :: P10 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P10 :: P11 :: nil) (P8 :: P1 :: P10 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P1 :: P10 :: P11 :: nil) ((P8 :: nil) ++ (P1 :: P10 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P8 :: nil) (P1 :: P10 :: P11 :: nil) (nil) 1 2 0 HP8Mtmp HP1P10P11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P8P10P11M4. 

assert(HP1P8P10P11m2 : rk(P1 :: P8 :: P10 :: P11 :: nil) >= 2).
{
	assert(HP1P8mtmp : rk(P1 :: P8 :: nil) >= 2) by (solve_hyps_min HP1P8eq HP1P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P8 :: nil) (P1 :: P8 :: P10 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P8 :: nil) (P1 :: P8 :: P10 :: P11 :: nil) 2 2 HP1P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P8P10P11m1. 

assert(HP1P8P10P11m3 : rk(P1 :: P8 :: P10 :: P11 :: nil) >= 3).
{
	assert(HP1P8P10mtmp : rk(P1 :: P8 :: P10 :: nil) >= 3) by (solve_hyps_min HP1P8P10eq HP1P8P10m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P8 :: P10 :: nil) (P1 :: P8 :: P10 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P8 :: P10 :: nil) (P1 :: P8 :: P10 :: P11 :: nil) 3 3 HP1P8P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P8P10M3. try clear HP1P8P10m3. try clear HP1P8P10P11m2. 

assert(HP1P2P9P11M3 : rk(P1 :: P2 :: P9 :: P11 :: nil) <= 3).
{
	assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M1).
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P9 :: P11 :: nil) (P1 :: P2 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P9 :: P11 :: nil) ((P1 :: nil) ++ (P2 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: nil) (P2 :: P9 :: P11 :: nil) (nil) 1 2 0 HP1Mtmp HP2P9P11Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1M1. try clear HP1m1. try clear HP1P2P9P11M4. 

assert(HP1P2P9P11m2 : rk(P1 :: P2 :: P9 :: P11 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P9 :: P11 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P9P11m1. 

assert(HP1P2P9P11m3 : rk(P1 :: P2 :: P9 :: P11 :: nil) >= 3).
{
	assert(HP1P2P9mtmp : rk(P1 :: P2 :: P9 :: nil) >= 3) by (solve_hyps_min HP1P2P9eq HP1P2P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P9 :: nil) (P1 :: P2 :: P9 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P9 :: nil) (P1 :: P2 :: P9 :: P11 :: nil) 3 3 HP1P2P9mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P9M3. try clear HP1P2P9m3. try clear HP1P2P9P11m2. 

assert(HP1P11m2 : rk(P1 :: P11 :: nil) >= 2).
{
	assert(HP2P9P11Mtmp : rk(P2 :: P9 :: P11 :: nil) <= 2) by (solve_hyps_max HP2P9P11eq HP2P9P11M2).
	assert(HP1P2P9P11mtmp : rk(P1 :: P2 :: P9 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P2P9P11eq HP1P2P9P11m3).
	assert(HP11mtmp : rk(P11 :: nil) >= 1) by (solve_hyps_min HP11eq HP11m1).
	assert(Hincl : incl (P11 :: nil) (list_inter (P1 :: P11 :: nil) (P2 :: P9 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P9 :: P11 :: nil) (P1 :: P11 :: P2 :: P9 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P11 :: P2 :: P9 :: P11 :: nil) ((P1 :: P11 :: nil) ++ (P2 :: P9 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P9P11mtmp;try rewrite HT2 in HP1P2P9P11mtmp.
	assert(HT := rule_2 (P1 :: P11 :: nil) (P2 :: P9 :: P11 :: nil) (P11 :: nil) 3 1 2 HP1P2P9P11mtmp HP11mtmp HP2P9P11Mtmp Hincl);apply HT.
}
try clear HP1P11m1. try clear HP2P9P11M2. try clear HP2P9P11m2. try clear HP11M1. try clear HP11m1. try clear HP1P2P9P11M3. try clear HP1P2P9P11m3. 

assert(HP1P8P11m2 : rk(P1 :: P8 :: P11 :: nil) >= 2).
{
	assert(HP1P8mtmp : rk(P1 :: P8 :: nil) >= 2) by (solve_hyps_min HP1P8eq HP1P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P8 :: nil) (P1 :: P8 :: P11 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P8 :: nil) (P1 :: P8 :: P11 :: nil) 2 2 HP1P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P8P11m1. 

assert(HP1P8P11m3 : rk(P1 :: P8 :: P11 :: nil) >= 3).
{
	assert(HP1P10P11Mtmp : rk(P1 :: P10 :: P11 :: nil) <= 2) by (solve_hyps_max HP1P10P11eq HP1P10P11M2).
	assert(HP1P8P10P11mtmp : rk(P1 :: P8 :: P10 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P8P10P11eq HP1P8P10P11m3).
	assert(HP1P11mtmp : rk(P1 :: P11 :: nil) >= 2) by (solve_hyps_min HP1P11eq HP1P11m2).
	assert(Hincl : incl (P1 :: P11 :: nil) (list_inter (P1 :: P8 :: P11 :: nil) (P1 :: P10 :: P11 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P10 :: P11 :: nil) (P1 :: P8 :: P11 :: P1 :: P10 :: P11 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P11 :: P1 :: P10 :: P11 :: nil) ((P1 :: P8 :: P11 :: nil) ++ (P1 :: P10 :: P11 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P8P10P11mtmp;try rewrite HT2 in HP1P8P10P11mtmp.
	assert(HT := rule_2 (P1 :: P8 :: P11 :: nil) (P1 :: P10 :: P11 :: nil) (P1 :: P11 :: nil) 3 2 2 HP1P8P10P11mtmp HP1P11mtmp HP1P10P11Mtmp Hincl);apply HT.
}
try clear HP1P8P11m2. try clear HP1P10P11M2. try clear HP1P10P11m2. try clear HP1P11M2. try clear HP1P11m2. try clear HP1P8P10P11M3. try clear HP1P8P10P11m3. 

assert(HP1P4P8P11P12P14m2 : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P12P14m1. 

assert(HP1P4P8P11P12P14m3 : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P12P14m2. 

assert(HP1P4P8P11P12P14m4 : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) >= 4).
{
	assert(HP1P2P8P11Mtmp : rk(P1 :: P2 :: P8 :: P11 :: nil) <= 3) by (solve_hyps_max HP1P2P8P11eq HP1P2P8P11M3).
	assert(HP1P2P4P8P11P12P14mtmp : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8P11P12P14eq HP1P2P4P8P11P12P14m4).
	assert(HP1P8P11mtmp : rk(P1 :: P8 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P8P11eq HP1P8P11m3).
	assert(Hincl : incl (P1 :: P8 :: P11 :: nil) (list_inter (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) (P1 :: P2 :: P8 :: P11 :: P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P8 :: P11 :: P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) ((P1 :: P2 :: P8 :: P11 :: nil) ++ (P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8P11P12P14mtmp;try rewrite HT2 in HP1P2P4P8P11P12P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) (P1 :: P8 :: P11 :: nil) 4 3 3 HP1P2P4P8P11P12P14mtmp HP1P8P11mtmp HP1P2P8P11Mtmp Hincl); apply HT.
}
try clear HP1P4P8P11P12P14m3. try clear HP1P2P4P8P11P12P14M4. try clear HP1P2P4P8P11P12P14m4. 

assert(HP1P5P8P9P14m2 : rk(P1 :: P5 :: P8 :: P9 :: P14 :: nil) >= 2).
{
	assert(HP1P5mtmp : rk(P1 :: P5 :: nil) >= 2) by (solve_hyps_min HP1P5eq HP1P5m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: nil) (P1 :: P5 :: P8 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: nil) (P1 :: P5 :: P8 :: P9 :: P14 :: nil) 2 2 HP1P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5M2. try clear HP1P5m2. try clear HP1P5P8P9P14m1. 

assert(HP1P5P8P9P14m3 : rk(P1 :: P5 :: P8 :: P9 :: P14 :: nil) >= 3).
{
	assert(HP1P5P8mtmp : rk(P1 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P5P8eq HP1P5P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P5 :: P8 :: nil) (P1 :: P5 :: P8 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P5 :: P8 :: nil) (P1 :: P5 :: P8 :: P9 :: P14 :: nil) 3 3 HP1P5P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P5P8M3. try clear HP1P5P8m3. try clear HP1P5P8P9P14m2. 

assert(HP1P5P8P9P14M3 : rk(P1 :: P5 :: P8 :: P9 :: P14 :: nil) <= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m1).
	assert(Hincl : incl (P9 :: nil) (list_inter (P1 :: P8 :: P9 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P8 :: P9 :: P14 :: nil) (P1 :: P8 :: P9 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P9 :: P5 :: P9 :: P14 :: nil) ((P1 :: P8 :: P9 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P8 :: P9 :: nil) (P5 :: P9 :: P14 :: nil) (P9 :: nil) 2 2 1 HP1P8P9Mtmp HP5P9P14Mtmp HP9mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP9M1. try clear HP9m1. try clear HP1P5P8P9P14M4. 

assert(HP5P8P9P14M3 : rk(P5 :: P8 :: P9 :: P14 :: nil) <= 3).
{
	assert(HP8Mtmp : rk(P8 :: nil) <= 1) by (solve_hyps_max HP8eq HP8M1).
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P8 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P8 :: P9 :: P14 :: nil) (P8 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P5 :: P9 :: P14 :: nil) ((P8 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P8 :: nil) (P5 :: P9 :: P14 :: nil) (nil) 1 2 0 HP8Mtmp HP5P9P14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP8M1. try clear HP8m1. try clear HP5P8P9P14M4. 

assert(HP5P8P9P14m2 : rk(P5 :: P8 :: P9 :: P14 :: nil) >= 2).
{
	assert(HP5P8mtmp : rk(P5 :: P8 :: nil) >= 2) by (solve_hyps_min HP5P8eq HP5P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P5 :: P8 :: nil) (P5 :: P8 :: P9 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P8 :: nil) (P5 :: P8 :: P9 :: P14 :: nil) 2 2 HP5P8mtmp Hcomp Hincl);apply HT.
}
try clear HP5P8M2. try clear HP5P8m2. try clear HP5P8P9P14m1. 

assert(HP5P8P9P14m3 : rk(P5 :: P8 :: P9 :: P14 :: nil) >= 3).
{
	assert(HP1P8P9Mtmp : rk(P1 :: P8 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P8P9eq HP1P8P9M2).
	assert(HP1P5P8P9P14mtmp : rk(P1 :: P5 :: P8 :: P9 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P5P8P9P14eq HP1P5P8P9P14m3).
	assert(HP8P9mtmp : rk(P8 :: P9 :: nil) >= 2) by (solve_hyps_min HP8P9eq HP8P9m2).
	assert(Hincl : incl (P8 :: P9 :: nil) (list_inter (P1 :: P8 :: P9 :: nil) (P5 :: P8 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P5 :: P8 :: P9 :: P14 :: nil) (P1 :: P8 :: P9 :: P5 :: P8 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P9 :: P5 :: P8 :: P9 :: P14 :: nil) ((P1 :: P8 :: P9 :: nil) ++ (P5 :: P8 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P5P8P9P14mtmp;try rewrite HT2 in HP1P5P8P9P14mtmp.
	assert(HT := rule_4 (P1 :: P8 :: P9 :: nil) (P5 :: P8 :: P9 :: P14 :: nil) (P8 :: P9 :: nil) 3 2 2 HP1P5P8P9P14mtmp HP8P9mtmp HP1P8P9Mtmp Hincl); apply HT.
}
try clear HP1P8P9M2. try clear HP1P8P9m2. try clear HP5P8P9P14m2. try clear HP8P9M2. try clear HP8P9m2. try clear HP1P5P8P9P14M3. try clear HP1P5P8P9P14m3. 

assert(HP8P14m2 : rk(P8 :: P14 :: nil) >= 2).
{
	assert(HP5P9P14Mtmp : rk(P5 :: P9 :: P14 :: nil) <= 2) by (solve_hyps_max HP5P9P14eq HP5P9P14M2).
	assert(HP5P8P9P14mtmp : rk(P5 :: P8 :: P9 :: P14 :: nil) >= 3) by (solve_hyps_min HP5P8P9P14eq HP5P8P9P14m3).
	assert(HP14mtmp : rk(P14 :: nil) >= 1) by (solve_hyps_min HP14eq HP14m1).
	assert(Hincl : incl (P14 :: nil) (list_inter (P8 :: P14 :: nil) (P5 :: P9 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P8 :: P9 :: P14 :: nil) (P8 :: P14 :: P5 :: P9 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P14 :: P5 :: P9 :: P14 :: nil) ((P8 :: P14 :: nil) ++ (P5 :: P9 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP5P8P9P14mtmp;try rewrite HT2 in HP5P8P9P14mtmp.
	assert(HT := rule_2 (P8 :: P14 :: nil) (P5 :: P9 :: P14 :: nil) (P14 :: nil) 3 1 2 HP5P8P9P14mtmp HP14mtmp HP5P9P14Mtmp Hincl);apply HT.
}
try clear HP8P14m1. try clear HP5P9P14M2. try clear HP5P9P14m2. try clear HP5P8P9P14M3. try clear HP5P8P9P14m3. 

assert(HP8P11P12P14m2 : rk(P8 :: P11 :: P12 :: P14 :: nil) >= 2).
{
	assert(HP8P11mtmp : rk(P8 :: P11 :: nil) >= 2) by (solve_hyps_min HP8P11eq HP8P11m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P8 :: P11 :: nil) (P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P8 :: P11 :: nil) (P8 :: P11 :: P12 :: P14 :: nil) 2 2 HP8P11mtmp Hcomp Hincl);apply HT.
}
try clear HP8P11P12P14m1. 

assert(HP8P11P12P14m3 : rk(P8 :: P11 :: P12 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP1P4P8P11P12P14mtmp : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P8P11P12P14eq HP1P4P8P11P12P14m4).
	assert(HP8P14mtmp : rk(P8 :: P14 :: nil) >= 2) by (solve_hyps_min HP8P14eq HP8P14m2).
	assert(Hincl : incl (P8 :: P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P8 :: P11 :: P12 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P11 :: P12 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P8 :: P11 :: P12 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P8 :: P11 :: P12 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P8 :: P11 :: P12 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P11P12P14mtmp;try rewrite HT2 in HP1P4P8P11P12P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P8 :: P14 :: nil) (P8 :: P11 :: P12 :: P14 :: nil) (P8 :: P14 :: nil) 4 2 3 HP1P4P8P11P12P14mtmp HP8P14mtmp HP1P4P8P14Mtmp Hincl); apply HT.
}
try clear HP8P11P12P14m2. try clear HP1P4P8P11P12P14M4. try clear HP1P4P8P11P12P14m4. 

assert(HP8P11P12P14M3 : rk(P8 :: P11 :: P12 :: P14 :: nil) <= 3).
{
	assert(HP7P8P11P12P14Mtmp : rk(P7 :: P8 :: P11 :: P12 :: P14 :: nil) <= 3) by (solve_hyps_max HP7P8P11P12P14eq HP7P8P11P12P14M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P8 :: P11 :: P12 :: P14 :: nil) (P7 :: P8 :: P11 :: P12 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P8 :: P11 :: P12 :: P14 :: nil) (P7 :: P8 :: P11 :: P12 :: P14 :: nil) 3 3 HP7P8P11P12P14Mtmp Hcomp Hincl);apply HT.
}
try clear HP8P11P12P14M4. try clear HP7P8P11P12P14M3. try clear HP7P8P11P12P14m3. 

assert(HP1P2P4P8P11P13P14m2 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P13P14m1. 

assert(HP1P2P4P8P11P13P14m3 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P13P14m2. 

assert(HP1P2P4P8P11P13P14m4 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P13P14m3. 

assert(HP1P4P8P11P13P14m2 : rk(P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P13P14m1. 

assert(HP1P4P8P11P13P14m3 : rk(P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P13P14m2. 

assert(HP1P4P8P11P13P14m4 : rk(P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P2P8P11Mtmp : rk(P1 :: P2 :: P8 :: P11 :: nil) <= 3) by (solve_hyps_max HP1P2P8P11eq HP1P2P8P11M3).
	assert(HP1P2P4P8P11P13P14mtmp : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8P11P13P14eq HP1P2P4P8P11P13P14m4).
	assert(HP1P8P11mtmp : rk(P1 :: P8 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P8P11eq HP1P8P11m3).
	assert(Hincl : incl (P1 :: P8 :: P11 :: nil) (list_inter (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) (P1 :: P2 :: P8 :: P11 :: P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P8 :: P11 :: P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) ((P1 :: P2 :: P8 :: P11 :: nil) ++ (P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8P11P13P14mtmp;try rewrite HT2 in HP1P2P4P8P11P13P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) (P1 :: P8 :: P11 :: nil) 4 3 3 HP1P2P4P8P11P13P14mtmp HP1P8P11mtmp HP1P2P8P11Mtmp Hincl); apply HT.
}
try clear HP1P4P8P11P13P14m3. try clear HP1P2P4P8P11P13P14M4. try clear HP1P2P4P8P11P13P14m4. 

assert(HP8P11P13P14m2 : rk(P8 :: P11 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP8P11mtmp : rk(P8 :: P11 :: nil) >= 2) by (solve_hyps_min HP8P11eq HP8P11m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P8 :: P11 :: nil) (P8 :: P11 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P8 :: P11 :: nil) (P8 :: P11 :: P13 :: P14 :: nil) 2 2 HP8P11mtmp Hcomp Hincl);apply HT.
}
try clear HP8P11P13P14m1. 

assert(HP8P11P13P14M3 : rk(P8 :: P11 :: P13 :: P14 :: nil) <= 3).
{
	assert(HP8P11P13Mtmp : rk(P8 :: P11 :: P13 :: nil) <= 2) by (solve_hyps_max HP8P11P13eq HP8P11P13M2).
	assert(HP14Mtmp : rk(P14 :: nil) <= 1) by (solve_hyps_max HP14eq HP14M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P8 :: P11 :: P13 :: nil) (P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P8 :: P11 :: P13 :: P14 :: nil) (P8 :: P11 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P11 :: P13 :: P14 :: nil) ((P8 :: P11 :: P13 :: nil) ++ (P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P8 :: P11 :: P13 :: nil) (P14 :: nil) (nil) 2 1 0 HP8P11P13Mtmp HP14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP8P11P13M2. try clear HP8P11P13m2. try clear HP8P11P13P14M4. 

assert(HP8P11P13P14m3 : rk(P8 :: P11 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP1P4P8P11P13P14mtmp : rk(P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P8P11P13P14eq HP1P4P8P11P13P14m4).
	assert(HP8P14mtmp : rk(P8 :: P14 :: nil) >= 2) by (solve_hyps_min HP8P14eq HP8P14m2).
	assert(Hincl : incl (P8 :: P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P8 :: P11 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P11 :: P13 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P8 :: P11 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P8 :: P11 :: P13 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P8 :: P11 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P11P13P14mtmp;try rewrite HT2 in HP1P4P8P11P13P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P8 :: P14 :: nil) (P8 :: P11 :: P13 :: P14 :: nil) (P8 :: P14 :: nil) 4 2 3 HP1P4P8P11P13P14mtmp HP8P14mtmp HP1P4P8P14Mtmp Hincl); apply HT.
}
try clear HP8P11P13P14m2. try clear HP1P4P8P11P13P14M4. try clear HP1P4P8P11P13P14m4. 

assert(HP1P2P4P8P11P14m2 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P14m1. 

assert(HP1P2P4P8P11P14m3 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P14m2. 

assert(HP1P2P4P8P11P14m4 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P14m3. 

assert(HP1P4P8P11P14m2 : rk(P1 :: P4 :: P8 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P14m1. 

assert(HP1P4P8P11P14m3 : rk(P1 :: P4 :: P8 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P11 :: P14 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8P11P14m2. 

assert(HP1P4P8P11P14m4 : rk(P1 :: P4 :: P8 :: P11 :: P14 :: nil) >= 4).
{
	assert(HP1P2P8P11Mtmp : rk(P1 :: P2 :: P8 :: P11 :: nil) <= 3) by (solve_hyps_max HP1P2P8P11eq HP1P2P8P11M3).
	assert(HP1P2P4P8P11P14mtmp : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8P11P14eq HP1P2P4P8P11P14m4).
	assert(HP1P8P11mtmp : rk(P1 :: P8 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P8P11eq HP1P8P11m3).
	assert(Hincl : incl (P1 :: P8 :: P11 :: nil) (list_inter (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: P11 :: P14 :: nil) (P1 :: P2 :: P8 :: P11 :: P1 :: P4 :: P8 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P8 :: P11 :: P1 :: P4 :: P8 :: P11 :: P14 :: nil) ((P1 :: P2 :: P8 :: P11 :: nil) ++ (P1 :: P4 :: P8 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8P11P14mtmp;try rewrite HT2 in HP1P2P4P8P11P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P14 :: nil) (P1 :: P8 :: P11 :: nil) 4 3 3 HP1P2P4P8P11P14mtmp HP1P8P11mtmp HP1P2P8P11Mtmp Hincl); apply HT.
}
try clear HP1P4P8P11P14m3. try clear HP1P2P4P8P11P14M4. try clear HP1P2P4P8P11P14m4. 

assert(HP8P11P14m2 : rk(P8 :: P11 :: P14 :: nil) >= 2).
{
	assert(HP8P11mtmp : rk(P8 :: P11 :: nil) >= 2) by (solve_hyps_min HP8P11eq HP8P11m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P8 :: P11 :: nil) (P8 :: P11 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P8 :: P11 :: nil) (P8 :: P11 :: P14 :: nil) 2 2 HP8P11mtmp Hcomp Hincl);apply HT.
}
try clear HP8P11P14m1. 

assert(HP8P11P14m3 : rk(P8 :: P11 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP1P4P8P11P14mtmp : rk(P1 :: P4 :: P8 :: P11 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P8P11P14eq HP1P4P8P11P14m4).
	assert(HP8P14mtmp : rk(P8 :: P14 :: nil) >= 2) by (solve_hyps_min HP8P14eq HP8P14m2).
	assert(Hincl : incl (P8 :: P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P8 :: P11 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P11 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P8 :: P11 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P8 :: P11 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P8 :: P11 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P11P14mtmp;try rewrite HT2 in HP1P4P8P11P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P8 :: P14 :: nil) (P8 :: P11 :: P14 :: nil) (P8 :: P14 :: nil) 4 2 3 HP1P4P8P11P14mtmp HP8P14mtmp HP1P4P8P14Mtmp Hincl); apply HT.
}
try clear HP8P11P14m2. try clear HP1P4P8P11P14M4. try clear HP1P4P8P11P14m4. 

assert(HP1P2P4P8P11P12P13P14m2 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8P11P12P13P14m1. 

assert(HP1P2P4P8P11P12P13P14m3 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4M3. try clear HP1P2P4m3. try clear HP1P2P4P8P11P12P13P14m2. 

assert(HP1P2P4P8P11P12P13P14m4 : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P2P4P8mtmp : rk(P1 :: P2 :: P4 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8eq HP1P2P4P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: P8 :: nil) (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) 4 4 HP1P2P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4P8M4. try clear HP1P2P4P8m4. try clear HP1P2P4P8P11P12P13P14m3. 

assert(HP1P4P8P11P12P13P14m2 : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P4mtmp : rk(P1 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P4eq HP1P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4M2. try clear HP1P4m2. try clear HP1P4P8P11P12P13P14m1. 

assert(HP1P4P8P11P12P13P14m3 : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8mtmp : rk(P1 :: P4 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P4P8eq HP1P4P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P4 :: P8 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P4P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P4P8M3. try clear HP1P4P8m3. try clear HP1P4P8P11P12P13P14m2. 

assert(HP1P4P8P11P12P13P14m4 : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P2P8P11Mtmp : rk(P1 :: P2 :: P8 :: P11 :: nil) <= 3) by (solve_hyps_max HP1P2P8P11eq HP1P2P8P11M3).
	assert(HP1P2P4P8P11P12P13P14mtmp : rk(P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P4P8P11P12P13P14eq HP1P2P4P8P11P12P13P14m4).
	assert(HP1P8P11mtmp : rk(P1 :: P8 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P8P11eq HP1P8P11m3).
	assert(Hincl : incl (P1 :: P8 :: P11 :: nil) (list_inter (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) (P1 :: P2 :: P8 :: P11 :: P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P8 :: P11 :: P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) ((P1 :: P2 :: P8 :: P11 :: nil) ++ (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P4P8P11P12P13P14mtmp;try rewrite HT2 in HP1P2P4P8P11P12P13P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P8 :: P11 :: nil) (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) (P1 :: P8 :: P11 :: nil) 4 3 3 HP1P2P4P8P11P12P13P14mtmp HP1P8P11mtmp HP1P2P8P11Mtmp Hincl); apply HT.
}
try clear HP1P2P8P11M3. try clear HP1P2P8P11m3. try clear HP1P4P8P11P12P13P14m3. try clear HP1P2P4P8P11P12P13P14M4. try clear HP1P2P4P8P11P12P13P14m4. 

assert(HP8P11P12P13P14m2 : rk(P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP8P11mtmp : rk(P8 :: P11 :: nil) >= 2) by (solve_hyps_min HP8P11eq HP8P11m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P8 :: P11 :: nil) (P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P8 :: P11 :: nil) (P8 :: P11 :: P12 :: P13 :: P14 :: nil) 2 2 HP8P11mtmp Hcomp Hincl);apply HT.
}
try clear HP8P11M2. try clear HP8P11m2. try clear HP8P11P12P13P14m1. 

assert(HP8P11P12P13P14m3 : rk(P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP1P4P8P11P12P13P14mtmp : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P8P11P12P13P14eq HP1P4P8P11P12P13P14m4).
	assert(HP8P14mtmp : rk(P8 :: P14 :: nil) >= 2) by (solve_hyps_min HP8P14eq HP8P14m2).
	assert(Hincl : incl (P8 :: P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P8 :: P11 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P8 :: P11 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P11P12P13P14mtmp;try rewrite HT2 in HP1P4P8P11P12P13P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P8 :: P14 :: nil) (P8 :: P11 :: P12 :: P13 :: P14 :: nil) (P8 :: P14 :: nil) 4 2 3 HP1P4P8P11P12P13P14mtmp HP8P14mtmp HP1P4P8P14Mtmp Hincl); apply HT.
}
try clear HP8P11P12P13P14m2. try clear HP8P14M2. try clear HP8P14m2. 

assert(HP8P11P12P13P14M3 : rk(P8 :: P11 :: P12 :: P13 :: P14 :: nil) <= 3).
{
	assert(HP8P11P12P14Mtmp : rk(P8 :: P11 :: P12 :: P14 :: nil) <= 3) by (solve_hyps_max HP8P11P12P14eq HP8P11P12P14M3).
	assert(HP8P11P13P14Mtmp : rk(P8 :: P11 :: P13 :: P14 :: nil) <= 3) by (solve_hyps_max HP8P11P13P14eq HP8P11P13P14M3).
	assert(HP8P11P14mtmp : rk(P8 :: P11 :: P14 :: nil) >= 3) by (solve_hyps_min HP8P11P14eq HP8P11P14m3).
	assert(Hincl : incl (P8 :: P11 :: P14 :: nil) (list_inter (P8 :: P11 :: P12 :: P14 :: nil) (P8 :: P11 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P8 :: P11 :: P12 :: P13 :: P14 :: nil) (P8 :: P11 :: P12 :: P14 :: P8 :: P11 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P8 :: P11 :: P12 :: P14 :: P8 :: P11 :: P13 :: P14 :: nil) ((P8 :: P11 :: P12 :: P14 :: nil) ++ (P8 :: P11 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P8 :: P11 :: P12 :: P14 :: nil) (P8 :: P11 :: P13 :: P14 :: nil) (P8 :: P11 :: P14 :: nil) 3 3 3 HP8P11P12P14Mtmp HP8P11P13P14Mtmp HP8P11P14mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP8P11P12P14M3. try clear HP8P11P12P14m3. try clear HP8P11P13P14M3. try clear HP8P11P13P14m3. try clear HP8P11P14M3. try clear HP8P11P14m3. try clear HP8P11P12P13P14M4. 

assert(HP1P2P6P8P10P14m2 : rk(P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil) 2 2 HP1P2mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2M2. try clear HP1P2m2. try clear HP1P2P6P8P10P14m1. 

assert(HP1P2P6P8P10P14m3 : rk(P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P2P6mtmp : rk(P1 :: P2 :: P6 :: nil) >= 3) by (solve_hyps_min HP1P2P6eq HP1P2P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil) 3 3 HP1P2P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6M3. try clear HP1P2P6m3. try clear HP1P2P6P8P10P14m2. 

assert(HP1P2P6P8P10P14m4 : rk(P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil) >= 4).
{
	assert(HP1P2P6P8mtmp : rk(P1 :: P2 :: P6 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P6P8eq HP1P2P6P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P6 :: P8 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P6 :: P8 :: nil) (P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil) 4 4 HP1P2P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P6P8M4. try clear HP1P2P6P8m4. try clear HP1P2P6P8P10P14m3. 

assert(HP1P6P8P10P14m2 : rk(P1 :: P6 :: P8 :: P10 :: P14 :: nil) >= 2).
{
	assert(HP1P6mtmp : rk(P1 :: P6 :: nil) >= 2) by (solve_hyps_min HP1P6eq HP1P6m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: nil) (P1 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: nil) (P1 :: P6 :: P8 :: P10 :: P14 :: nil) 2 2 HP1P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6M2. try clear HP1P6m2. try clear HP1P6P8P10P14m1. 

assert(HP1P6P8P10P14m3 : rk(P1 :: P6 :: P8 :: P10 :: P14 :: nil) >= 3).
{
	assert(HP1P6P8mtmp : rk(P1 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP1P6P8eq HP1P6P8m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P6 :: P8 :: nil) (P1 :: P6 :: P8 :: P10 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P6 :: P8 :: nil) (P1 :: P6 :: P8 :: P10 :: P14 :: nil) 3 3 HP1P6P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P6P8M3. try clear HP1P6P8m3. try clear HP1P6P8P10P14m2. 

assert(HP1P6P8P10P14m4 : rk(P1 :: P6 :: P8 :: P10 :: P14 :: nil) >= 4).
{
	assert(HP2P8P10Mtmp : rk(P2 :: P8 :: P10 :: nil) <= 2) by (solve_hyps_max HP2P8P10eq HP2P8P10M2).
	assert(HP1P2P6P8P10P14mtmp : rk(P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P6P8P10P14eq HP1P2P6P8P10P14m4).
	assert(HP8P10mtmp : rk(P8 :: P10 :: nil) >= 2) by (solve_hyps_min HP8P10eq HP8P10m2).
	assert(Hincl : incl (P8 :: P10 :: nil) (list_inter (P2 :: P8 :: P10 :: nil) (P1 :: P6 :: P8 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P6 :: P8 :: P10 :: P14 :: nil) (P2 :: P8 :: P10 :: P1 :: P6 :: P8 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P8 :: P10 :: P1 :: P6 :: P8 :: P10 :: P14 :: nil) ((P2 :: P8 :: P10 :: nil) ++ (P1 :: P6 :: P8 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P6P8P10P14mtmp;try rewrite HT2 in HP1P2P6P8P10P14mtmp.
	assert(HT := rule_4 (P2 :: P8 :: P10 :: nil) (P1 :: P6 :: P8 :: P10 :: P14 :: nil) (P8 :: P10 :: nil) 4 2 2 HP1P2P6P8P10P14mtmp HP8P10mtmp HP2P8P10Mtmp Hincl); apply HT.
}
try clear HP2P8P10M2. try clear HP2P8P10m2. try clear HP1P6P8P10P14m3. try clear HP8P10M2. try clear HP8P10m2. try clear HP1P2P6P8P10P14M4. try clear HP1P2P6P8P10P14m4. 

assert(HP1P8P14m2 : rk(P1 :: P8 :: P14 :: nil) >= 2).
{
	assert(HP1P8mtmp : rk(P1 :: P8 :: nil) >= 2) by (solve_hyps_min HP1P8eq HP1P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P8 :: nil) (P1 :: P8 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P8 :: nil) (P1 :: P8 :: P14 :: nil) 2 2 HP1P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P8P14m1. 

assert(HP1P8P14m3 : rk(P1 :: P8 :: P14 :: nil) >= 3).
{
	assert(HP6P10P14Mtmp : rk(P6 :: P10 :: P14 :: nil) <= 2) by (solve_hyps_max HP6P10P14eq HP6P10P14M2).
	assert(HP1P6P8P10P14mtmp : rk(P1 :: P6 :: P8 :: P10 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P6P8P10P14eq HP1P6P8P10P14m4).
	assert(HP14mtmp : rk(P14 :: nil) >= 1) by (solve_hyps_min HP14eq HP14m1).
	assert(Hincl : incl (P14 :: nil) (list_inter (P1 :: P8 :: P14 :: nil) (P6 :: P10 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P6 :: P8 :: P10 :: P14 :: nil) (P1 :: P8 :: P14 :: P6 :: P10 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P8 :: P14 :: P6 :: P10 :: P14 :: nil) ((P1 :: P8 :: P14 :: nil) ++ (P6 :: P10 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P6P8P10P14mtmp;try rewrite HT2 in HP1P6P8P10P14mtmp.
	assert(HT := rule_2 (P1 :: P8 :: P14 :: nil) (P6 :: P10 :: P14 :: nil) (P14 :: nil) 4 1 2 HP1P6P8P10P14mtmp HP14mtmp HP6P10P14Mtmp Hincl);apply HT.
}
try clear HP1P8P14m2. try clear HP6P10P14M2. try clear HP6P10P14m2. try clear HP1P6P8P10P14M4. try clear HP1P6P8P10P14m4. 

assert(HP1P8P11P12P13P14m2 : rk(P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P8mtmp : rk(P1 :: P8 :: nil) >= 2) by (solve_hyps_min HP1P8eq HP1P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P8 :: nil) (P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P8 :: nil) (P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) 2 2 HP1P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P8M2. try clear HP1P8m2. try clear HP1P8P11P12P13P14m1. 

assert(HP1P8P11P12P13P14m3 : rk(P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 3).
{
	assert(HP1P8P11mtmp : rk(P1 :: P8 :: P11 :: nil) >= 3) by (solve_hyps_min HP1P8P11eq HP1P8P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P8 :: P11 :: nil) (P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P8 :: P11 :: nil) (P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) 3 3 HP1P8P11mtmp Hcomp Hincl);apply HT.
}
try clear HP1P8P11M3. try clear HP1P8P11m3. try clear HP1P8P11P12P13P14m2. 

assert(HP1P8P11P12P13P14m4 : rk(P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP1P4P8P11P12P13P14mtmp : rk(P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P8P11P12P13P14eq HP1P4P8P11P12P13P14m4).
	assert(HP1P8P14mtmp : rk(P1 :: P8 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P8P14eq HP1P8P14m3).
	assert(Hincl : incl (P1 :: P8 :: P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P11P12P13P14mtmp;try rewrite HT2 in HP1P4P8P11P12P13P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P8 :: P14 :: nil) (P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) (P1 :: P8 :: P14 :: nil) 4 3 3 HP1P4P8P11P12P13P14mtmp HP1P8P14mtmp HP1P4P8P14Mtmp Hincl); apply HT.
}
try clear HP1P8P11P12P13P14m3. try clear HP1P8P14M3. try clear HP1P8P14m3. try clear HP1P4P8P11P12P13P14M4. try clear HP1P4P8P11P12P13P14m4. 

assert(HP12P13P14m2 : rk(P12 :: P13 :: P14 :: nil) >= 2).
{
	assert(HP1P4P8P14Mtmp : rk(P1 :: P4 :: P8 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P4P8P14eq HP1P4P8P14M3).
	assert(HP1P4P8P12P13P14mtmp : rk(P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P4P8P12P13P14eq HP1P4P8P12P13P14m4).
	assert(HP14mtmp : rk(P14 :: nil) >= 1) by (solve_hyps_min HP14eq HP14m1).
	assert(Hincl : incl (P14 :: nil) (list_inter (P1 :: P4 :: P8 :: P14 :: nil) (P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P4 :: P8 :: P12 :: P13 :: P14 :: nil) (P1 :: P4 :: P8 :: P14 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P4 :: P8 :: P14 :: P12 :: P13 :: P14 :: nil) ((P1 :: P4 :: P8 :: P14 :: nil) ++ (P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P4P8P12P13P14mtmp;try rewrite HT2 in HP1P4P8P12P13P14mtmp.
	assert(HT := rule_4 (P1 :: P4 :: P8 :: P14 :: nil) (P12 :: P13 :: P14 :: nil) (P14 :: nil) 4 1 3 HP1P4P8P12P13P14mtmp HP14mtmp HP1P4P8P14Mtmp Hincl); apply HT.
}
try clear HP1P4P8P14M3. try clear HP1P4P8P14m3. try clear HP12P13P14m1. try clear HP14M1. try clear HP14m1. try clear HP1P4P8P12P13P14M4. try clear HP1P4P8P12P13P14m4. 

assert(HP12P13P14M2 : rk(P12 :: P13 :: P14 :: nil) <= 2).
{
	assert(HP1P12P13P14Mtmp : rk(P1 :: P12 :: P13 :: P14 :: nil) <= 3) by (solve_hyps_max HP1P12P13P14eq HP1P12P13P14M3).
	assert(HP8P11P12P13P14Mtmp : rk(P8 :: P11 :: P12 :: P13 :: P14 :: nil) <= 3) by (solve_hyps_max HP8P11P12P13P14eq HP8P11P12P13P14M3).
	assert(HP1P8P11P12P13P14mtmp : rk(P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P8P11P12P13P14eq HP1P8P11P12P13P14m4).
	assert(Hincl : incl (P12 :: P13 :: P14 :: nil) (list_inter (P1 :: P12 :: P13 :: P14 :: nil) (P8 :: P11 :: P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) (P1 :: P12 :: P13 :: P14 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P12 :: P13 :: P14 :: P8 :: P11 :: P12 :: P13 :: P14 :: nil) ((P1 :: P12 :: P13 :: P14 :: nil) ++ (P8 :: P11 :: P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P8P11P12P13P14mtmp;try rewrite HT2 in HP1P8P11P12P13P14mtmp.
	assert(HT := rule_3 (P1 :: P12 :: P13 :: P14 :: nil) (P8 :: P11 :: P12 :: P13 :: P14 :: nil) (P12 :: P13 :: P14 :: nil) 3 3 4 HP1P12P13P14Mtmp HP8P11P12P13P14Mtmp HP1P8P11P12P13P14mtmp Hincl);apply HT.
}
try clear HP8P11P12P13P14M3. try clear HP8P11P12P13P14m3. try clear HP12P13P14M3. try clear HP1P8P11P12P13P14M4. try clear HP1P8P11P12P13P14m4. 

assert(HP12P13M1 : rk(P12 :: P13 :: nil) <= 1).
{
	assert(HP1P12P13Mtmp : rk(P1 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P12P13eq HP1P12P13M2).
	assert(HP12P13P14Mtmp : rk(P12 :: P13 :: P14 :: nil) <= 2) by (solve_hyps_max HP12P13P14eq HP12P13P14M2).
	assert(HP1P12P13P14mtmp : rk(P1 :: P12 :: P13 :: P14 :: nil) >= 3) by (solve_hyps_min HP1P12P13P14eq HP1P12P13P14m3).
	assert(Hincl : incl (P12 :: P13 :: nil) (list_inter (P1 :: P12 :: P13 :: nil) (P12 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P12 :: P13 :: P14 :: nil) (P1 :: P12 :: P13 :: P12 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P12 :: P13 :: P12 :: P13 :: P14 :: nil) ((P1 :: P12 :: P13 :: nil) ++ (P12 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P12P13P14mtmp;try rewrite HT2 in HP1P12P13P14mtmp.
	assert(HT := rule_3 (P1 :: P12 :: P13 :: nil) (P12 :: P13 :: P14 :: nil) (P12 :: P13 :: nil) 2 2 3 HP1P12P13Mtmp HP12P13P14Mtmp HP1P12P13P14mtmp Hincl);apply HT.
}
try clear HP1P12P13M2. try clear HP1P12P13m2. try clear HP12P13P14M2. try clear HP12P13P14m2. try clear HP12P13M2. try clear HP1P12P13P14M3. try clear HP1P12P13P14m3. 

assert(rk(P12 :: P13 ::  nil) <= 2) by (solve[apply matroid1_b_useful;simpl;repeat constructor|apply rk_upper_dim]).
assert(rk(P12 :: P13 ::  nil) >= 1) by (solve[apply matroid1_b_useful2;simpl;repeat constructor|apply matroid1_a]).
omega.
Qed.