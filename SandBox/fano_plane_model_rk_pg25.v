Require Import ssrfun ssrbool.
Require Export ProjectiveGeometry.Dev.fano_matroid_tactics.

(** Pg(2,5). **)

(** To show that our axiom system is consistent we build a finite model. **)
(*****************************************************************************)

Section s_fanoPlaneModelRkPG25.
(* fano_plane_model_rk_pg25_spec.v: #points = 31, #lines = 31 *)

Parameter 
 P0  P1  P2  P3  P4  P5  P6  P7  P8  P9  P10  P11  P12  P13  P14  P15  P16  P17  P18  P19  P20  P21  P22  P23  P24  P25  P26  P27  P28  P29  P30 : Point.

Parameter rk_points : 
rk (P0 :: nil) = 1  /\ rk (P1 :: nil) = 1  /\ rk (P2 :: nil) = 1  /\ rk (P3 :: nil) = 1  /\ rk (P4 :: nil) = 1  /\ rk (P5 :: nil) = 1  /\ rk (P6 :: nil) = 1  /\ rk (P7 :: nil) = 1  /\ rk (P8 :: nil) = 1  /\ rk (P9 :: nil) = 1  /\ rk (P10 :: nil) = 1  /\ rk (P11 :: nil) = 1  /\ rk (P12 :: nil) = 1  /\ rk (P13 :: nil) = 1  /\ rk (P14 :: nil) = 1  /\ rk (P15 :: nil) = 1  /\ rk (P16 :: nil) = 1  /\ rk (P17 :: nil) = 1  /\ rk (P18 :: nil) = 1  /\ rk (P19 :: nil) = 1  /\ rk (P20 :: nil) = 1  /\ rk (P21 :: nil) = 1  /\ rk (P22 :: nil) = 1  /\ rk (P23 :: nil) = 1  /\ rk (P24 :: nil) = 1  /\ rk (P25 :: nil) = 1  /\ rk (P26 :: nil) = 1  /\ rk (P27 :: nil) = 1  /\ rk (P28 :: nil) = 1  /\ rk (P29 :: nil) = 1  /\ rk (P30 :: nil) = 1 .

Parameter rk_distinct_points : 
rk (P0 :: P1 :: nil) = 2  /\ rk (P0 :: P2 :: nil) = 2  /\ rk (P0 :: P3 :: nil) = 2  /\ rk (P0 :: P4 :: nil) = 2  /\ rk (P0 :: P5 :: nil) = 2  /\ rk (P0 :: P6 :: nil) = 2  /\ rk (P0 :: P7 :: nil) = 2  /\ rk (P0 :: P8 :: nil) = 2  /\ rk (P0 :: P9 :: nil) = 2  /\ rk (P0 :: P10 :: nil) = 2  /\ rk (P0 :: P11 :: nil) = 2  /\ rk (P0 :: P12 :: nil) = 2  /\ rk (P0 :: P13 :: nil) = 2  /\ rk (P0 :: P14 :: nil) = 2  /\ rk (P0 :: P15 :: nil) = 2  /\ rk (P0 :: P16 :: nil) = 2  /\ rk (P0 :: P17 :: nil) = 2  /\ rk (P0 :: P18 :: nil) = 2  /\ rk (P0 :: P19 :: nil) = 2  /\ rk (P0 :: P20 :: nil) = 2  /\ rk (P0 :: P21 :: nil) = 2  /\ rk (P0 :: P22 :: nil) = 2  /\ rk (P0 :: P23 :: nil) = 2  /\ rk (P0 :: P24 :: nil) = 2  /\ rk (P0 :: P25 :: nil) = 2  /\ rk (P0 :: P26 :: nil) = 2  /\ rk (P0 :: P27 :: nil) = 2  /\ rk (P0 :: P28 :: nil) = 2  /\ rk (P0 :: P29 :: nil) = 2  /\ rk (P0 :: P30 :: nil) = 2  /\ rk (P1 :: P2 :: nil) = 2  /\ rk (P1 :: P3 :: nil) = 2  /\ rk (P1 :: P4 :: nil) = 2  /\ rk (P1 :: P5 :: nil) = 2  /\ rk (P1 :: P6 :: nil) = 2  /\ rk (P1 :: P7 :: nil) = 2  /\ rk (P1 :: P8 :: nil) = 2  /\ rk (P1 :: P9 :: nil) = 2  /\ rk (P1 :: P10 :: nil) = 2  /\ rk (P1 :: P11 :: nil) = 2  /\ rk (P1 :: P12 :: nil) = 2  /\ rk (P1 :: P13 :: nil) = 2  /\ rk (P1 :: P14 :: nil) = 2  /\ rk (P1 :: P15 :: nil) = 2  /\ rk (P1 :: P16 :: nil) = 2  /\ rk (P1 :: P17 :: nil) = 2  /\ rk (P1 :: P18 :: nil) = 2  /\ rk (P1 :: P19 :: nil) = 2  /\ rk (P1 :: P20 :: nil) = 2  /\ rk (P1 :: P21 :: nil) = 2  /\ rk (P1 :: P22 :: nil) = 2  /\ rk (P1 :: P23 :: nil) = 2  /\ rk (P1 :: P24 :: nil) = 2  /\ rk (P1 :: P25 :: nil) = 2  /\ rk (P1 :: P26 :: nil) = 2  /\ rk (P1 :: P27 :: nil) = 2  /\ rk (P1 :: P28 :: nil) = 2  /\ rk (P1 :: P29 :: nil) = 2  /\ rk (P1 :: P30 :: nil) = 2  /\ rk (P2 :: P3 :: nil) = 2  /\ rk (P2 :: P4 :: nil) = 2  /\ rk (P2 :: P5 :: nil) = 2  /\ rk (P2 :: P6 :: nil) = 2  /\ rk (P2 :: P7 :: nil) = 2  /\ rk (P2 :: P8 :: nil) = 2  /\ rk (P2 :: P9 :: nil) = 2  /\ rk (P2 :: P10 :: nil) = 2  /\ rk (P2 :: P11 :: nil) = 2  /\ rk (P2 :: P12 :: nil) = 2  /\ rk (P2 :: P13 :: nil) = 2  /\ rk (P2 :: P14 :: nil) = 2  /\ rk (P2 :: P15 :: nil) = 2  /\ rk (P2 :: P16 :: nil) = 2  /\ rk (P2 :: P17 :: nil) = 2  /\ rk (P2 :: P18 :: nil) = 2  /\ rk (P2 :: P19 :: nil) = 2  /\ rk (P2 :: P20 :: nil) = 2  /\ rk (P2 :: P21 :: nil) = 2  /\ rk (P2 :: P22 :: nil) = 2  /\ rk (P2 :: P23 :: nil) = 2  /\ rk (P2 :: P24 :: nil) = 2  /\ rk (P2 :: P25 :: nil) = 2  /\ rk (P2 :: P26 :: nil) = 2  /\ rk (P2 :: P27 :: nil) = 2  /\ rk (P2 :: P28 :: nil) = 2  /\ rk (P2 :: P29 :: nil) = 2  /\ rk (P2 :: P30 :: nil) = 2  /\ rk (P3 :: P4 :: nil) = 2  /\ rk (P3 :: P5 :: nil) = 2  /\ rk (P3 :: P6 :: nil) = 2  /\ rk (P3 :: P7 :: nil) = 2  /\ rk (P3 :: P8 :: nil) = 2  /\ rk (P3 :: P9 :: nil) = 2  /\ rk (P3 :: P10 :: nil) = 2  /\ rk (P3 :: P11 :: nil) = 2  /\ rk (P3 :: P12 :: nil) = 2  /\ rk (P3 :: P13 :: nil) = 2  /\ rk (P3 :: P14 :: nil) = 2  /\ rk (P3 :: P15 :: nil) = 2  /\ rk (P3 :: P16 :: nil) = 2  /\ rk (P3 :: P17 :: nil) = 2  /\ rk (P3 :: P18 :: nil) = 2  /\ rk (P3 :: P19 :: nil) = 2  /\ rk (P3 :: P20 :: nil) = 2  /\ rk (P3 :: P21 :: nil) = 2  /\ rk (P3 :: P22 :: nil) = 2  /\ rk (P3 :: P23 :: nil) = 2  /\ rk (P3 :: P24 :: nil) = 2  /\ rk (P3 :: P25 :: nil) = 2  /\ rk (P3 :: P26 :: nil) = 2  /\ rk (P3 :: P27 :: nil) = 2  /\ rk (P3 :: P28 :: nil) = 2  /\ rk (P3 :: P29 :: nil) = 2  /\ rk (P3 :: P30 :: nil) = 2  /\ rk (P4 :: P5 :: nil) = 2  /\ rk (P4 :: P6 :: nil) = 2  /\ rk (P4 :: P7 :: nil) = 2  /\ rk (P4 :: P8 :: nil) = 2  /\ rk (P4 :: P9 :: nil) = 2  /\ rk (P4 :: P10 :: nil) = 2  /\ rk (P4 :: P11 :: nil) = 2  /\ rk (P4 :: P12 :: nil) = 2  /\ rk (P4 :: P13 :: nil) = 2  /\ rk (P4 :: P14 :: nil) = 2  /\ rk (P4 :: P15 :: nil) = 2  /\ rk (P4 :: P16 :: nil) = 2  /\ rk (P4 :: P17 :: nil) = 2  /\ rk (P4 :: P18 :: nil) = 2  /\ rk (P4 :: P19 :: nil) = 2  /\ rk (P4 :: P20 :: nil) = 2  /\ rk (P4 :: P21 :: nil) = 2  /\ rk (P4 :: P22 :: nil) = 2  /\ rk (P4 :: P23 :: nil) = 2  /\ rk (P4 :: P24 :: nil) = 2  /\ rk (P4 :: P25 :: nil) = 2  /\ rk (P4 :: P26 :: nil) = 2  /\ rk (P4 :: P27 :: nil) = 2  /\ rk (P4 :: P28 :: nil) = 2  /\ rk (P4 :: P29 :: nil) = 2  /\ rk (P4 :: P30 :: nil) = 2  /\ rk (P5 :: P6 :: nil) = 2  /\ rk (P5 :: P7 :: nil) = 2  /\ rk (P5 :: P8 :: nil) = 2  /\ rk (P5 :: P9 :: nil) = 2  /\ rk (P5 :: P10 :: nil) = 2  /\ rk (P5 :: P11 :: nil) = 2  /\ rk (P5 :: P12 :: nil) = 2  /\ rk (P5 :: P13 :: nil) = 2  /\ rk (P5 :: P14 :: nil) = 2  /\ rk (P5 :: P15 :: nil) = 2  /\ rk (P5 :: P16 :: nil) = 2  /\ rk (P5 :: P17 :: nil) = 2  /\ rk (P5 :: P18 :: nil) = 2  /\ rk (P5 :: P19 :: nil) = 2  /\ rk (P5 :: P20 :: nil) = 2  /\ rk (P5 :: P21 :: nil) = 2  /\ rk (P5 :: P22 :: nil) = 2  /\ rk (P5 :: P23 :: nil) = 2  /\ rk (P5 :: P24 :: nil) = 2  /\ rk (P5 :: P25 :: nil) = 2  /\ rk (P5 :: P26 :: nil) = 2  /\ rk (P5 :: P27 :: nil) = 2  /\ rk (P5 :: P28 :: nil) = 2  /\ rk (P5 :: P29 :: nil) = 2  /\ rk (P5 :: P30 :: nil) = 2  /\ rk (P6 :: P7 :: nil) = 2  /\ rk (P6 :: P8 :: nil) = 2  /\ rk (P6 :: P9 :: nil) = 2  /\ rk (P6 :: P10 :: nil) = 2  /\ rk (P6 :: P11 :: nil) = 2  /\ rk (P6 :: P12 :: nil) = 2  /\ rk (P6 :: P13 :: nil) = 2  /\ rk (P6 :: P14 :: nil) = 2  /\ rk (P6 :: P15 :: nil) = 2  /\ rk (P6 :: P16 :: nil) = 2  /\ rk (P6 :: P17 :: nil) = 2  /\ rk (P6 :: P18 :: nil) = 2  /\ rk (P6 :: P19 :: nil) = 2  /\ rk (P6 :: P20 :: nil) = 2  /\ rk (P6 :: P21 :: nil) = 2  /\ rk (P6 :: P22 :: nil) = 2  /\ rk (P6 :: P23 :: nil) = 2  /\ rk (P6 :: P24 :: nil) = 2  /\ rk (P6 :: P25 :: nil) = 2  /\ rk (P6 :: P26 :: nil) = 2  /\ rk (P6 :: P27 :: nil) = 2  /\ rk (P6 :: P28 :: nil) = 2  /\ rk (P6 :: P29 :: nil) = 2  /\ rk (P6 :: P30 :: nil) = 2  /\ rk (P7 :: P8 :: nil) = 2  /\ rk (P7 :: P9 :: nil) = 2  /\ rk (P7 :: P10 :: nil) = 2  /\ rk (P7 :: P11 :: nil) = 2  /\ rk (P7 :: P12 :: nil) = 2  /\ rk (P7 :: P13 :: nil) = 2  /\ rk (P7 :: P14 :: nil) = 2  /\ rk (P7 :: P15 :: nil) = 2  /\ rk (P7 :: P16 :: nil) = 2  /\ rk (P7 :: P17 :: nil) = 2  /\ rk (P7 :: P18 :: nil) = 2  /\ rk (P7 :: P19 :: nil) = 2  /\ rk (P7 :: P20 :: nil) = 2  /\ rk (P7 :: P21 :: nil) = 2  /\ rk (P7 :: P22 :: nil) = 2  /\ rk (P7 :: P23 :: nil) = 2  /\ rk (P7 :: P24 :: nil) = 2  /\ rk (P7 :: P25 :: nil) = 2  /\ rk (P7 :: P26 :: nil) = 2  /\ rk (P7 :: P27 :: nil) = 2  /\ rk (P7 :: P28 :: nil) = 2  /\ rk (P7 :: P29 :: nil) = 2  /\ rk (P7 :: P30 :: nil) = 2  /\ rk (P8 :: P9 :: nil) = 2  /\ rk (P8 :: P10 :: nil) = 2  /\ rk (P8 :: P11 :: nil) = 2  /\ rk (P8 :: P12 :: nil) = 2  /\ rk (P8 :: P13 :: nil) = 2  /\ rk (P8 :: P14 :: nil) = 2  /\ rk (P8 :: P15 :: nil) = 2  /\ rk (P8 :: P16 :: nil) = 2  /\ rk (P8 :: P17 :: nil) = 2  /\ rk (P8 :: P18 :: nil) = 2  /\ rk (P8 :: P19 :: nil) = 2  /\ rk (P8 :: P20 :: nil) = 2  /\ rk (P8 :: P21 :: nil) = 2  /\ rk (P8 :: P22 :: nil) = 2  /\ rk (P8 :: P23 :: nil) = 2  /\ rk (P8 :: P24 :: nil) = 2  /\ rk (P8 :: P25 :: nil) = 2  /\ rk (P8 :: P26 :: nil) = 2  /\ rk (P8 :: P27 :: nil) = 2  /\ rk (P8 :: P28 :: nil) = 2  /\ rk (P8 :: P29 :: nil) = 2  /\ rk (P8 :: P30 :: nil) = 2  /\ rk (P9 :: P10 :: nil) = 2  /\ rk (P9 :: P11 :: nil) = 2  /\ rk (P9 :: P12 :: nil) = 2  /\ rk (P9 :: P13 :: nil) = 2  /\ rk (P9 :: P14 :: nil) = 2  /\ rk (P9 :: P15 :: nil) = 2  /\ rk (P9 :: P16 :: nil) = 2  /\ rk (P9 :: P17 :: nil) = 2  /\ rk (P9 :: P18 :: nil) = 2  /\ rk (P9 :: P19 :: nil) = 2  /\ rk (P9 :: P20 :: nil) = 2  /\ rk (P9 :: P21 :: nil) = 2  /\ rk (P9 :: P22 :: nil) = 2  /\ rk (P9 :: P23 :: nil) = 2  /\ rk (P9 :: P24 :: nil) = 2  /\ rk (P9 :: P25 :: nil) = 2  /\ rk (P9 :: P26 :: nil) = 2  /\ rk (P9 :: P27 :: nil) = 2  /\ rk (P9 :: P28 :: nil) = 2  /\ rk (P9 :: P29 :: nil) = 2  /\ rk (P9 :: P30 :: nil) = 2  /\ rk (P10 :: P11 :: nil) = 2  /\ rk (P10 :: P12 :: nil) = 2  /\ rk (P10 :: P13 :: nil) = 2  /\ rk (P10 :: P14 :: nil) = 2  /\ rk (P10 :: P15 :: nil) = 2  /\ rk (P10 :: P16 :: nil) = 2  /\ rk (P10 :: P17 :: nil) = 2  /\ rk (P10 :: P18 :: nil) = 2  /\ rk (P10 :: P19 :: nil) = 2  /\ rk (P10 :: P20 :: nil) = 2  /\ rk (P10 :: P21 :: nil) = 2  /\ rk (P10 :: P22 :: nil) = 2  /\ rk (P10 :: P23 :: nil) = 2  /\ rk (P10 :: P24 :: nil) = 2  /\ rk (P10 :: P25 :: nil) = 2  /\ rk (P10 :: P26 :: nil) = 2  /\ rk (P10 :: P27 :: nil) = 2  /\ rk (P10 :: P28 :: nil) = 2  /\ rk (P10 :: P29 :: nil) = 2  /\ rk (P10 :: P30 :: nil) = 2  /\ rk (P11 :: P12 :: nil) = 2  /\ rk (P11 :: P13 :: nil) = 2  /\ rk (P11 :: P14 :: nil) = 2  /\ rk (P11 :: P15 :: nil) = 2  /\ rk (P11 :: P16 :: nil) = 2  /\ rk (P11 :: P17 :: nil) = 2  /\ rk (P11 :: P18 :: nil) = 2  /\ rk (P11 :: P19 :: nil) = 2  /\ rk (P11 :: P20 :: nil) = 2  /\ rk (P11 :: P21 :: nil) = 2  /\ rk (P11 :: P22 :: nil) = 2  /\ rk (P11 :: P23 :: nil) = 2  /\ rk (P11 :: P24 :: nil) = 2  /\ rk (P11 :: P25 :: nil) = 2  /\ rk (P11 :: P26 :: nil) = 2  /\ rk (P11 :: P27 :: nil) = 2  /\ rk (P11 :: P28 :: nil) = 2  /\ rk (P11 :: P29 :: nil) = 2  /\ rk (P11 :: P30 :: nil) = 2  /\ rk (P12 :: P13 :: nil) = 2  /\ rk (P12 :: P14 :: nil) = 2  /\ rk (P12 :: P15 :: nil) = 2  /\ rk (P12 :: P16 :: nil) = 2  /\ rk (P12 :: P17 :: nil) = 2  /\ rk (P12 :: P18 :: nil) = 2  /\ rk (P12 :: P19 :: nil) = 2  /\ rk (P12 :: P20 :: nil) = 2  /\ rk (P12 :: P21 :: nil) = 2  /\ rk (P12 :: P22 :: nil) = 2  /\ rk (P12 :: P23 :: nil) = 2  /\ rk (P12 :: P24 :: nil) = 2  /\ rk (P12 :: P25 :: nil) = 2  /\ rk (P12 :: P26 :: nil) = 2  /\ rk (P12 :: P27 :: nil) = 2  /\ rk (P12 :: P28 :: nil) = 2  /\ rk (P12 :: P29 :: nil) = 2  /\ rk (P12 :: P30 :: nil) = 2  /\ rk (P13 :: P14 :: nil) = 2  /\ rk (P13 :: P15 :: nil) = 2  /\ rk (P13 :: P16 :: nil) = 2  /\ rk (P13 :: P17 :: nil) = 2  /\ rk (P13 :: P18 :: nil) = 2  /\ rk (P13 :: P19 :: nil) = 2  /\ rk (P13 :: P20 :: nil) = 2  /\ rk (P13 :: P21 :: nil) = 2  /\ rk (P13 :: P22 :: nil) = 2  /\ rk (P13 :: P23 :: nil) = 2  /\ rk (P13 :: P24 :: nil) = 2  /\ rk (P13 :: P25 :: nil) = 2  /\ rk (P13 :: P26 :: nil) = 2  /\ rk (P13 :: P27 :: nil) = 2  /\ rk (P13 :: P28 :: nil) = 2  /\ rk (P13 :: P29 :: nil) = 2  /\ rk (P13 :: P30 :: nil) = 2  /\ rk (P14 :: P15 :: nil) = 2  /\ rk (P14 :: P16 :: nil) = 2  /\ rk (P14 :: P17 :: nil) = 2  /\ rk (P14 :: P18 :: nil) = 2  /\ rk (P14 :: P19 :: nil) = 2  /\ rk (P14 :: P20 :: nil) = 2  /\ rk (P14 :: P21 :: nil) = 2  /\ rk (P14 :: P22 :: nil) = 2  /\ rk (P14 :: P23 :: nil) = 2  /\ rk (P14 :: P24 :: nil) = 2  /\ rk (P14 :: P25 :: nil) = 2  /\ rk (P14 :: P26 :: nil) = 2  /\ rk (P14 :: P27 :: nil) = 2  /\ rk (P14 :: P28 :: nil) = 2  /\ rk (P14 :: P29 :: nil) = 2  /\ rk (P14 :: P30 :: nil) = 2  /\ rk (P15 :: P16 :: nil) = 2  /\ rk (P15 :: P17 :: nil) = 2  /\ rk (P15 :: P18 :: nil) = 2  /\ rk (P15 :: P19 :: nil) = 2  /\ rk (P15 :: P20 :: nil) = 2  /\ rk (P15 :: P21 :: nil) = 2  /\ rk (P15 :: P22 :: nil) = 2  /\ rk (P15 :: P23 :: nil) = 2  /\ rk (P15 :: P24 :: nil) = 2  /\ rk (P15 :: P25 :: nil) = 2  /\ rk (P15 :: P26 :: nil) = 2  /\ rk (P15 :: P27 :: nil) = 2  /\ rk (P15 :: P28 :: nil) = 2  /\ rk (P15 :: P29 :: nil) = 2  /\ rk (P15 :: P30 :: nil) = 2  /\ rk (P16 :: P17 :: nil) = 2  /\ rk (P16 :: P18 :: nil) = 2  /\ rk (P16 :: P19 :: nil) = 2  /\ rk (P16 :: P20 :: nil) = 2  /\ rk (P16 :: P21 :: nil) = 2  /\ rk (P16 :: P22 :: nil) = 2  /\ rk (P16 :: P23 :: nil) = 2  /\ rk (P16 :: P24 :: nil) = 2  /\ rk (P16 :: P25 :: nil) = 2  /\ rk (P16 :: P26 :: nil) = 2  /\ rk (P16 :: P27 :: nil) = 2  /\ rk (P16 :: P28 :: nil) = 2  /\ rk (P16 :: P29 :: nil) = 2  /\ rk (P16 :: P30 :: nil) = 2  /\ rk (P17 :: P18 :: nil) = 2  /\ rk (P17 :: P19 :: nil) = 2  /\ rk (P17 :: P20 :: nil) = 2  /\ rk (P17 :: P21 :: nil) = 2  /\ rk (P17 :: P22 :: nil) = 2  /\ rk (P17 :: P23 :: nil) = 2  /\ rk (P17 :: P24 :: nil) = 2  /\ rk (P17 :: P25 :: nil) = 2  /\ rk (P17 :: P26 :: nil) = 2  /\ rk (P17 :: P27 :: nil) = 2  /\ rk (P17 :: P28 :: nil) = 2  /\ rk (P17 :: P29 :: nil) = 2  /\ rk (P17 :: P30 :: nil) = 2  /\ rk (P18 :: P19 :: nil) = 2  /\ rk (P18 :: P20 :: nil) = 2  /\ rk (P18 :: P21 :: nil) = 2  /\ rk (P18 :: P22 :: nil) = 2  /\ rk (P18 :: P23 :: nil) = 2  /\ rk (P18 :: P24 :: nil) = 2  /\ rk (P18 :: P25 :: nil) = 2  /\ rk (P18 :: P26 :: nil) = 2  /\ rk (P18 :: P27 :: nil) = 2  /\ rk (P18 :: P28 :: nil) = 2  /\ rk (P18 :: P29 :: nil) = 2  /\ rk (P18 :: P30 :: nil) = 2  /\ rk (P19 :: P20 :: nil) = 2  /\ rk (P19 :: P21 :: nil) = 2  /\ rk (P19 :: P22 :: nil) = 2  /\ rk (P19 :: P23 :: nil) = 2  /\ rk (P19 :: P24 :: nil) = 2  /\ rk (P19 :: P25 :: nil) = 2  /\ rk (P19 :: P26 :: nil) = 2  /\ rk (P19 :: P27 :: nil) = 2  /\ rk (P19 :: P28 :: nil) = 2  /\ rk (P19 :: P29 :: nil) = 2  /\ rk (P19 :: P30 :: nil) = 2  /\ rk (P20 :: P21 :: nil) = 2  /\ rk (P20 :: P22 :: nil) = 2  /\ rk (P20 :: P23 :: nil) = 2  /\ rk (P20 :: P24 :: nil) = 2  /\ rk (P20 :: P25 :: nil) = 2  /\ rk (P20 :: P26 :: nil) = 2  /\ rk (P20 :: P27 :: nil) = 2  /\ rk (P20 :: P28 :: nil) = 2  /\ rk (P20 :: P29 :: nil) = 2  /\ rk (P20 :: P30 :: nil) = 2  /\ rk (P21 :: P22 :: nil) = 2  /\ rk (P21 :: P23 :: nil) = 2  /\ rk (P21 :: P24 :: nil) = 2  /\ rk (P21 :: P25 :: nil) = 2  /\ rk (P21 :: P26 :: nil) = 2  /\ rk (P21 :: P27 :: nil) = 2  /\ rk (P21 :: P28 :: nil) = 2  /\ rk (P21 :: P29 :: nil) = 2  /\ rk (P21 :: P30 :: nil) = 2  /\ rk (P22 :: P23 :: nil) = 2  /\ rk (P22 :: P24 :: nil) = 2  /\ rk (P22 :: P25 :: nil) = 2  /\ rk (P22 :: P26 :: nil) = 2  /\ rk (P22 :: P27 :: nil) = 2  /\ rk (P22 :: P28 :: nil) = 2  /\ rk (P22 :: P29 :: nil) = 2  /\ rk (P22 :: P30 :: nil) = 2  /\ rk (P23 :: P24 :: nil) = 2  /\ rk (P23 :: P25 :: nil) = 2  /\ rk (P23 :: P26 :: nil) = 2  /\ rk (P23 :: P27 :: nil) = 2  /\ rk (P23 :: P28 :: nil) = 2  /\ rk (P23 :: P29 :: nil) = 2  /\ rk (P23 :: P30 :: nil) = 2  /\ rk (P24 :: P25 :: nil) = 2  /\ rk (P24 :: P26 :: nil) = 2  /\ rk (P24 :: P27 :: nil) = 2  /\ rk (P24 :: P28 :: nil) = 2  /\ rk (P24 :: P29 :: nil) = 2  /\ rk (P24 :: P30 :: nil) = 2  /\ rk (P25 :: P26 :: nil) = 2  /\ rk (P25 :: P27 :: nil) = 2  /\ rk (P25 :: P28 :: nil) = 2  /\ rk (P25 :: P29 :: nil) = 2  /\ rk (P25 :: P30 :: nil) = 2  /\ rk (P26 :: P27 :: nil) = 2  /\ rk (P26 :: P28 :: nil) = 2  /\ rk (P26 :: P29 :: nil) = 2  /\ rk (P26 :: P30 :: nil) = 2  /\ rk (P27 :: P28 :: nil) = 2  /\ rk (P27 :: P29 :: nil) = 2  /\ rk (P27 :: P30 :: nil) = 2  /\ rk (P28 :: P29 :: nil) = 2  /\ rk (P28 :: P30 :: nil) = 2  /\ rk (P29 :: P30 :: nil) = 2 .

Parameter rk_lines : rk (P0 :: P1 :: P3 :: P8 :: P12 :: P18 :: nil) = 2 /\ rk (P0 :: P2 :: P7 :: P11 :: P17 :: P30 :: nil) = 2 /\ rk (P1 :: P6 :: P10 :: P16 :: P29 :: P30 :: nil) = 2 /\ rk (P0 :: P5 :: P9 :: P15 :: P28 :: P29 :: nil) = 2 /\ rk (P4 :: P8 :: P14 :: P27 :: P28 :: P30 :: nil) = 2 /\ rk (P3 :: P7 :: P13 :: P26 :: P27 :: P29 :: nil) = 2 /\ rk (P2 :: P6 :: P12 :: P25 :: P26 :: P28 :: nil) = 2 /\ rk (P1 :: P5 :: P11 :: P24 :: P25 :: P27 :: nil) = 2 /\ rk (P0 :: P4 :: P10 :: P23 :: P24 :: P26 :: nil) = 2 /\ rk (P3 :: P9 :: P22 :: P23 :: P25 :: P30 :: nil) = 2 /\ rk (P2 :: P8 :: P21 :: P22 :: P24 :: P29 :: nil) = 2 /\ rk (P1 :: P7 :: P20 :: P21 :: P23 :: P28 :: nil) = 2 /\ rk (P0 :: P6 :: P19 :: P20 :: P22 :: P27 :: nil) = 2 /\ rk (P5 :: P18 :: P19 :: P21 :: P26 :: P30 :: nil) = 2 /\ rk (P4 :: P17 :: P18 :: P20 :: P25 :: P29 :: nil) = 2 /\ rk (P3 :: P16 :: P17 :: P19 :: P24 :: P28 :: nil) = 2 /\ rk (P2 :: P15 :: P16 :: P18 :: P23 :: P27 :: nil) = 2 /\ rk (P1 :: P14 :: P15 :: P17 :: P22 :: P26 :: nil) = 2 /\ rk (P0 :: P13 :: P14 :: P16 :: P21 :: P25 :: nil) = 2 /\ rk (P12 :: P13 :: P15 :: P20 :: P24 :: P30 :: nil) = 2 /\ rk (P11 :: P12 :: P14 :: P19 :: P23 :: P29 :: nil) = 2 /\ rk (P10 :: P11 :: P13 :: P18 :: P22 :: P28 :: nil) = 2 /\ rk (P9 :: P10 :: P12 :: P17 :: P21 :: P27 :: nil) = 2 /\ rk (P8 :: P9 :: P11 :: P16 :: P20 :: P26 :: nil) = 2 /\ rk (P7 :: P8 :: P10 :: P15 :: P19 :: P25 :: nil) = 2 /\ rk (P6 :: P7 :: P9 :: P14 :: P18 :: P24 :: nil) = 2 /\ rk (P5 :: P6 :: P8 :: P13 :: P17 :: P23 :: nil) = 2 /\ rk (P4 :: P5 :: P7 :: P12 :: P16 :: P22 :: nil) = 2 /\ rk (P3 :: P4 :: P6 :: P11 :: P15 :: P21 :: nil) = 2 /\ rk (P2 :: P3 :: P5 :: P10 :: P14 :: P20 :: nil) = 2 /\ rk (P1 :: P2 :: P4 :: P9 :: P13 :: P19 :: nil) = 2.

Parameter rk_lines' :  rk(P0 :: P1 :: P3 ::nil) = 2
 /\  rk(P0 :: P1 :: P8 ::nil) = 2
 /\  rk(P0 :: P1 :: P12 ::nil) = 2
 /\  rk(P0 :: P1 :: P18 ::nil) = 2
 /\  rk(P0 :: P3 :: P8 ::nil) = 2
 /\  rk(P0 :: P3 :: P12 ::nil) = 2
 /\  rk(P0 :: P3 :: P18 ::nil) = 2
 /\  rk(P0 :: P8 :: P12 ::nil) = 2
 /\  rk(P0 :: P8 :: P18 ::nil) = 2
 /\  rk(P0 :: P12 :: P18 ::nil) = 2
 /\  rk(P1 :: P3 :: P8 ::nil) = 2
 /\  rk(P1 :: P3 :: P12 ::nil) = 2
 /\  rk(P1 :: P3 :: P18 ::nil) = 2
 /\  rk(P1 :: P8 :: P12 ::nil) = 2
 /\  rk(P1 :: P8 :: P18 ::nil) = 2
 /\  rk(P1 :: P12 :: P18 ::nil) = 2
 /\  rk(P3 :: P8 :: P12 ::nil) = 2
 /\  rk(P3 :: P8 :: P18 ::nil) = 2
 /\  rk(P3 :: P12 :: P18 ::nil) = 2
 /\  rk(P8 :: P12 :: P18 ::nil) = 2
 /\  rk(P0 :: P2 :: P7 ::nil) = 2
 /\  rk(P0 :: P2 :: P11 ::nil) = 2
 /\  rk(P0 :: P2 :: P17 ::nil) = 2
 /\  rk(P0 :: P2 :: P30 ::nil) = 2
 /\  rk(P0 :: P7 :: P11 ::nil) = 2
 /\  rk(P0 :: P7 :: P17 ::nil) = 2
 /\  rk(P0 :: P7 :: P30 ::nil) = 2
 /\  rk(P0 :: P11 :: P17 ::nil) = 2
 /\  rk(P0 :: P11 :: P30 ::nil) = 2
 /\  rk(P0 :: P17 :: P30 ::nil) = 2
 /\  rk(P2 :: P7 :: P11 ::nil) = 2
 /\  rk(P2 :: P7 :: P17 ::nil) = 2
 /\  rk(P2 :: P7 :: P30 ::nil) = 2
 /\  rk(P2 :: P11 :: P17 ::nil) = 2
 /\  rk(P2 :: P11 :: P30 ::nil) = 2
 /\  rk(P2 :: P17 :: P30 ::nil) = 2
 /\  rk(P7 :: P11 :: P17 ::nil) = 2
 /\  rk(P7 :: P11 :: P30 ::nil) = 2
 /\  rk(P7 :: P17 :: P30 ::nil) = 2
 /\  rk(P11 :: P17 :: P30 ::nil) = 2
 /\  rk(P1 :: P6 :: P10 ::nil) = 2
 /\  rk(P1 :: P6 :: P16 ::nil) = 2
 /\  rk(P1 :: P6 :: P29 ::nil) = 2
 /\  rk(P1 :: P6 :: P30 ::nil) = 2
 /\  rk(P1 :: P10 :: P16 ::nil) = 2
 /\  rk(P1 :: P10 :: P29 ::nil) = 2
 /\  rk(P1 :: P10 :: P30 ::nil) = 2
 /\  rk(P1 :: P16 :: P29 ::nil) = 2
 /\  rk(P1 :: P16 :: P30 ::nil) = 2
 /\  rk(P1 :: P29 :: P30 ::nil) = 2
 /\  rk(P6 :: P10 :: P16 ::nil) = 2
 /\  rk(P6 :: P10 :: P29 ::nil) = 2
 /\  rk(P6 :: P10 :: P30 ::nil) = 2
 /\  rk(P6 :: P16 :: P29 ::nil) = 2
 /\  rk(P6 :: P16 :: P30 ::nil) = 2
 /\  rk(P6 :: P29 :: P30 ::nil) = 2
 /\  rk(P10 :: P16 :: P29 ::nil) = 2
 /\  rk(P10 :: P16 :: P30 ::nil) = 2
 /\  rk(P10 :: P29 :: P30 ::nil) = 2
 /\  rk(P16 :: P29 :: P30 ::nil) = 2
 /\  rk(P0 :: P5 :: P9 ::nil) = 2
 /\  rk(P0 :: P5 :: P15 ::nil) = 2
 /\  rk(P0 :: P5 :: P28 ::nil) = 2
 /\  rk(P0 :: P5 :: P29 ::nil) = 2
 /\  rk(P0 :: P9 :: P15 ::nil) = 2
 /\  rk(P0 :: P9 :: P28 ::nil) = 2
 /\  rk(P0 :: P9 :: P29 ::nil) = 2
 /\  rk(P0 :: P15 :: P28 ::nil) = 2
 /\  rk(P0 :: P15 :: P29 ::nil) = 2
 /\  rk(P0 :: P28 :: P29 ::nil) = 2
 /\  rk(P5 :: P9 :: P15 ::nil) = 2
 /\  rk(P5 :: P9 :: P28 ::nil) = 2
 /\  rk(P5 :: P9 :: P29 ::nil) = 2
 /\  rk(P5 :: P15 :: P28 ::nil) = 2
 /\  rk(P5 :: P15 :: P29 ::nil) = 2
 /\  rk(P5 :: P28 :: P29 ::nil) = 2
 /\  rk(P9 :: P15 :: P28 ::nil) = 2
 /\  rk(P9 :: P15 :: P29 ::nil) = 2
 /\  rk(P9 :: P28 :: P29 ::nil) = 2
 /\  rk(P15 :: P28 :: P29 ::nil) = 2
 /\  rk(P4 :: P8 :: P14 ::nil) = 2
 /\  rk(P4 :: P8 :: P27 ::nil) = 2
 /\  rk(P4 :: P8 :: P28 ::nil) = 2
 /\  rk(P4 :: P8 :: P30 ::nil) = 2
 /\  rk(P4 :: P14 :: P27 ::nil) = 2
 /\  rk(P4 :: P14 :: P28 ::nil) = 2
 /\  rk(P4 :: P14 :: P30 ::nil) = 2
 /\  rk(P4 :: P27 :: P28 ::nil) = 2
 /\  rk(P4 :: P27 :: P30 ::nil) = 2
 /\  rk(P4 :: P28 :: P30 ::nil) = 2
 /\  rk(P8 :: P14 :: P27 ::nil) = 2
 /\  rk(P8 :: P14 :: P28 ::nil) = 2
 /\  rk(P8 :: P14 :: P30 ::nil) = 2
 /\  rk(P8 :: P27 :: P28 ::nil) = 2
 /\  rk(P8 :: P27 :: P30 ::nil) = 2
 /\  rk(P8 :: P28 :: P30 ::nil) = 2
 /\  rk(P14 :: P27 :: P28 ::nil) = 2
 /\  rk(P14 :: P27 :: P30 ::nil) = 2
 /\  rk(P14 :: P28 :: P30 ::nil) = 2
 /\  rk(P27 :: P28 :: P30 ::nil) = 2
 /\  rk(P3 :: P7 :: P13 ::nil) = 2
 /\  rk(P3 :: P7 :: P26 ::nil) = 2
 /\  rk(P3 :: P7 :: P27 ::nil) = 2
 /\  rk(P3 :: P7 :: P29 ::nil) = 2
 /\  rk(P3 :: P13 :: P26 ::nil) = 2
 /\  rk(P3 :: P13 :: P27 ::nil) = 2
 /\  rk(P3 :: P13 :: P29 ::nil) = 2
 /\  rk(P3 :: P26 :: P27 ::nil) = 2
 /\  rk(P3 :: P26 :: P29 ::nil) = 2
 /\  rk(P3 :: P27 :: P29 ::nil) = 2
 /\  rk(P7 :: P13 :: P26 ::nil) = 2
 /\  rk(P7 :: P13 :: P27 ::nil) = 2
 /\  rk(P7 :: P13 :: P29 ::nil) = 2
 /\  rk(P7 :: P26 :: P27 ::nil) = 2
 /\  rk(P7 :: P26 :: P29 ::nil) = 2
 /\  rk(P7 :: P27 :: P29 ::nil) = 2
 /\  rk(P13 :: P26 :: P27 ::nil) = 2
 /\  rk(P13 :: P26 :: P29 ::nil) = 2
 /\  rk(P13 :: P27 :: P29 ::nil) = 2
 /\  rk(P26 :: P27 :: P29 ::nil) = 2
 /\  rk(P2 :: P6 :: P12 ::nil) = 2
 /\  rk(P2 :: P6 :: P25 ::nil) = 2
 /\  rk(P2 :: P6 :: P26 ::nil) = 2
 /\  rk(P2 :: P6 :: P28 ::nil) = 2
 /\  rk(P2 :: P12 :: P25 ::nil) = 2
 /\  rk(P2 :: P12 :: P26 ::nil) = 2
 /\  rk(P2 :: P12 :: P28 ::nil) = 2
 /\  rk(P2 :: P25 :: P26 ::nil) = 2
 /\  rk(P2 :: P25 :: P28 ::nil) = 2
 /\  rk(P2 :: P26 :: P28 ::nil) = 2
 /\  rk(P6 :: P12 :: P25 ::nil) = 2
 /\  rk(P6 :: P12 :: P26 ::nil) = 2
 /\  rk(P6 :: P12 :: P28 ::nil) = 2
 /\  rk(P6 :: P25 :: P26 ::nil) = 2
 /\  rk(P6 :: P25 :: P28 ::nil) = 2
 /\  rk(P6 :: P26 :: P28 ::nil) = 2
 /\  rk(P12 :: P25 :: P26 ::nil) = 2
 /\  rk(P12 :: P25 :: P28 ::nil) = 2
 /\  rk(P12 :: P26 :: P28 ::nil) = 2
 /\  rk(P25 :: P26 :: P28 ::nil) = 2
 /\  rk(P1 :: P5 :: P11 ::nil) = 2
 /\  rk(P1 :: P5 :: P24 ::nil) = 2
 /\  rk(P1 :: P5 :: P25 ::nil) = 2
 /\  rk(P1 :: P5 :: P27 ::nil) = 2
 /\  rk(P1 :: P11 :: P24 ::nil) = 2
 /\  rk(P1 :: P11 :: P25 ::nil) = 2
 /\  rk(P1 :: P11 :: P27 ::nil) = 2
 /\  rk(P1 :: P24 :: P25 ::nil) = 2
 /\  rk(P1 :: P24 :: P27 ::nil) = 2
 /\  rk(P1 :: P25 :: P27 ::nil) = 2
 /\  rk(P5 :: P11 :: P24 ::nil) = 2
 /\  rk(P5 :: P11 :: P25 ::nil) = 2
 /\  rk(P5 :: P11 :: P27 ::nil) = 2
 /\  rk(P5 :: P24 :: P25 ::nil) = 2
 /\  rk(P5 :: P24 :: P27 ::nil) = 2
 /\  rk(P5 :: P25 :: P27 ::nil) = 2
 /\  rk(P11 :: P24 :: P25 ::nil) = 2
 /\  rk(P11 :: P24 :: P27 ::nil) = 2
 /\  rk(P11 :: P25 :: P27 ::nil) = 2
 /\  rk(P24 :: P25 :: P27 ::nil) = 2
 /\  rk(P0 :: P4 :: P10 ::nil) = 2
 /\  rk(P0 :: P4 :: P23 ::nil) = 2
 /\  rk(P0 :: P4 :: P24 ::nil) = 2
 /\  rk(P0 :: P4 :: P26 ::nil) = 2
 /\  rk(P0 :: P10 :: P23 ::nil) = 2
 /\  rk(P0 :: P10 :: P24 ::nil) = 2
 /\  rk(P0 :: P10 :: P26 ::nil) = 2
 /\  rk(P0 :: P23 :: P24 ::nil) = 2
 /\  rk(P0 :: P23 :: P26 ::nil) = 2
 /\  rk(P0 :: P24 :: P26 ::nil) = 2
 /\  rk(P4 :: P10 :: P23 ::nil) = 2
 /\  rk(P4 :: P10 :: P24 ::nil) = 2
 /\  rk(P4 :: P10 :: P26 ::nil) = 2
 /\  rk(P4 :: P23 :: P24 ::nil) = 2
 /\  rk(P4 :: P23 :: P26 ::nil) = 2
 /\  rk(P4 :: P24 :: P26 ::nil) = 2
 /\  rk(P10 :: P23 :: P24 ::nil) = 2
 /\  rk(P10 :: P23 :: P26 ::nil) = 2
 /\  rk(P10 :: P24 :: P26 ::nil) = 2
 /\  rk(P23 :: P24 :: P26 ::nil) = 2
 /\  rk(P3 :: P9 :: P22 ::nil) = 2
 /\  rk(P3 :: P9 :: P23 ::nil) = 2
 /\  rk(P3 :: P9 :: P25 ::nil) = 2
 /\  rk(P3 :: P9 :: P30 ::nil) = 2
 /\  rk(P3 :: P22 :: P23 ::nil) = 2
 /\  rk(P3 :: P22 :: P25 ::nil) = 2
 /\  rk(P3 :: P22 :: P30 ::nil) = 2
 /\  rk(P3 :: P23 :: P25 ::nil) = 2
 /\  rk(P3 :: P23 :: P30 ::nil) = 2
 /\  rk(P3 :: P25 :: P30 ::nil) = 2
 /\  rk(P9 :: P22 :: P23 ::nil) = 2
 /\  rk(P9 :: P22 :: P25 ::nil) = 2
 /\  rk(P9 :: P22 :: P30 ::nil) = 2
 /\  rk(P9 :: P23 :: P25 ::nil) = 2
 /\  rk(P9 :: P23 :: P30 ::nil) = 2
 /\  rk(P9 :: P25 :: P30 ::nil) = 2
 /\  rk(P22 :: P23 :: P25 ::nil) = 2
 /\  rk(P22 :: P23 :: P30 ::nil) = 2
 /\  rk(P22 :: P25 :: P30 ::nil) = 2
 /\  rk(P23 :: P25 :: P30 ::nil) = 2
 /\  rk(P2 :: P8 :: P21 ::nil) = 2
 /\  rk(P2 :: P8 :: P22 ::nil) = 2
 /\  rk(P2 :: P8 :: P24 ::nil) = 2
 /\  rk(P2 :: P8 :: P29 ::nil) = 2
 /\  rk(P2 :: P21 :: P22 ::nil) = 2
 /\  rk(P2 :: P21 :: P24 ::nil) = 2
 /\  rk(P2 :: P21 :: P29 ::nil) = 2
 /\  rk(P2 :: P22 :: P24 ::nil) = 2
 /\  rk(P2 :: P22 :: P29 ::nil) = 2
 /\  rk(P2 :: P24 :: P29 ::nil) = 2
 /\  rk(P8 :: P21 :: P22 ::nil) = 2
 /\  rk(P8 :: P21 :: P24 ::nil) = 2
 /\  rk(P8 :: P21 :: P29 ::nil) = 2
 /\  rk(P8 :: P22 :: P24 ::nil) = 2
 /\  rk(P8 :: P22 :: P29 ::nil) = 2
 /\  rk(P8 :: P24 :: P29 ::nil) = 2
 /\  rk(P21 :: P22 :: P24 ::nil) = 2
 /\  rk(P21 :: P22 :: P29 ::nil) = 2
 /\  rk(P21 :: P24 :: P29 ::nil) = 2
 /\  rk(P22 :: P24 :: P29 ::nil) = 2
 /\  rk(P1 :: P7 :: P20 ::nil) = 2
 /\  rk(P1 :: P7 :: P21 ::nil) = 2
 /\  rk(P1 :: P7 :: P23 ::nil) = 2
 /\  rk(P1 :: P7 :: P28 ::nil) = 2
 /\  rk(P1 :: P20 :: P21 ::nil) = 2
 /\  rk(P1 :: P20 :: P23 ::nil) = 2
 /\  rk(P1 :: P20 :: P28 ::nil) = 2
 /\  rk(P1 :: P21 :: P23 ::nil) = 2
 /\  rk(P1 :: P21 :: P28 ::nil) = 2
 /\  rk(P1 :: P23 :: P28 ::nil) = 2
 /\  rk(P7 :: P20 :: P21 ::nil) = 2
 /\  rk(P7 :: P20 :: P23 ::nil) = 2
 /\  rk(P7 :: P20 :: P28 ::nil) = 2
 /\  rk(P7 :: P21 :: P23 ::nil) = 2
 /\  rk(P7 :: P21 :: P28 ::nil) = 2
 /\  rk(P7 :: P23 :: P28 ::nil) = 2
 /\  rk(P20 :: P21 :: P23 ::nil) = 2
 /\  rk(P20 :: P21 :: P28 ::nil) = 2
 /\  rk(P20 :: P23 :: P28 ::nil) = 2
 /\  rk(P21 :: P23 :: P28 ::nil) = 2
 /\  rk(P0 :: P6 :: P19 ::nil) = 2
 /\  rk(P0 :: P6 :: P20 ::nil) = 2
 /\  rk(P0 :: P6 :: P22 ::nil) = 2
 /\  rk(P0 :: P6 :: P27 ::nil) = 2
 /\  rk(P0 :: P19 :: P20 ::nil) = 2
 /\  rk(P0 :: P19 :: P22 ::nil) = 2
 /\  rk(P0 :: P19 :: P27 ::nil) = 2
 /\  rk(P0 :: P20 :: P22 ::nil) = 2
 /\  rk(P0 :: P20 :: P27 ::nil) = 2
 /\  rk(P0 :: P22 :: P27 ::nil) = 2
 /\  rk(P6 :: P19 :: P20 ::nil) = 2
 /\  rk(P6 :: P19 :: P22 ::nil) = 2
 /\  rk(P6 :: P19 :: P27 ::nil) = 2
 /\  rk(P6 :: P20 :: P22 ::nil) = 2
 /\  rk(P6 :: P20 :: P27 ::nil) = 2
 /\  rk(P6 :: P22 :: P27 ::nil) = 2
 /\  rk(P19 :: P20 :: P22 ::nil) = 2
 /\  rk(P19 :: P20 :: P27 ::nil) = 2
 /\  rk(P19 :: P22 :: P27 ::nil) = 2
 /\  rk(P20 :: P22 :: P27 ::nil) = 2
 /\  rk(P5 :: P18 :: P19 ::nil) = 2
 /\  rk(P5 :: P18 :: P21 ::nil) = 2
 /\  rk(P5 :: P18 :: P26 ::nil) = 2
 /\  rk(P5 :: P18 :: P30 ::nil) = 2
 /\  rk(P5 :: P19 :: P21 ::nil) = 2
 /\  rk(P5 :: P19 :: P26 ::nil) = 2
 /\  rk(P5 :: P19 :: P30 ::nil) = 2
 /\  rk(P5 :: P21 :: P26 ::nil) = 2
 /\  rk(P5 :: P21 :: P30 ::nil) = 2
 /\  rk(P5 :: P26 :: P30 ::nil) = 2
 /\  rk(P18 :: P19 :: P21 ::nil) = 2
 /\  rk(P18 :: P19 :: P26 ::nil) = 2
 /\  rk(P18 :: P19 :: P30 ::nil) = 2
 /\  rk(P18 :: P21 :: P26 ::nil) = 2
 /\  rk(P18 :: P21 :: P30 ::nil) = 2
 /\  rk(P18 :: P26 :: P30 ::nil) = 2
 /\  rk(P19 :: P21 :: P26 ::nil) = 2
 /\  rk(P19 :: P21 :: P30 ::nil) = 2
 /\  rk(P19 :: P26 :: P30 ::nil) = 2
 /\  rk(P21 :: P26 :: P30 ::nil) = 2
 /\  rk(P4 :: P17 :: P18 ::nil) = 2
 /\  rk(P4 :: P17 :: P20 ::nil) = 2
 /\  rk(P4 :: P17 :: P25 ::nil) = 2
 /\  rk(P4 :: P17 :: P29 ::nil) = 2
 /\  rk(P4 :: P18 :: P20 ::nil) = 2
 /\  rk(P4 :: P18 :: P25 ::nil) = 2
 /\  rk(P4 :: P18 :: P29 ::nil) = 2
 /\  rk(P4 :: P20 :: P25 ::nil) = 2
 /\  rk(P4 :: P20 :: P29 ::nil) = 2
 /\  rk(P4 :: P25 :: P29 ::nil) = 2
 /\  rk(P17 :: P18 :: P20 ::nil) = 2
 /\  rk(P17 :: P18 :: P25 ::nil) = 2
 /\  rk(P17 :: P18 :: P29 ::nil) = 2
 /\  rk(P17 :: P20 :: P25 ::nil) = 2
 /\  rk(P17 :: P20 :: P29 ::nil) = 2
 /\  rk(P17 :: P25 :: P29 ::nil) = 2
 /\  rk(P18 :: P20 :: P25 ::nil) = 2
 /\  rk(P18 :: P20 :: P29 ::nil) = 2
 /\  rk(P18 :: P25 :: P29 ::nil) = 2
 /\  rk(P20 :: P25 :: P29 ::nil) = 2
 /\  rk(P3 :: P16 :: P17 ::nil) = 2
 /\  rk(P3 :: P16 :: P19 ::nil) = 2
 /\  rk(P3 :: P16 :: P24 ::nil) = 2
 /\  rk(P3 :: P16 :: P28 ::nil) = 2
 /\  rk(P3 :: P17 :: P19 ::nil) = 2
 /\  rk(P3 :: P17 :: P24 ::nil) = 2
 /\  rk(P3 :: P17 :: P28 ::nil) = 2
 /\  rk(P3 :: P19 :: P24 ::nil) = 2
 /\  rk(P3 :: P19 :: P28 ::nil) = 2
 /\  rk(P3 :: P24 :: P28 ::nil) = 2
 /\  rk(P16 :: P17 :: P19 ::nil) = 2
 /\  rk(P16 :: P17 :: P24 ::nil) = 2
 /\  rk(P16 :: P17 :: P28 ::nil) = 2
 /\  rk(P16 :: P19 :: P24 ::nil) = 2
 /\  rk(P16 :: P19 :: P28 ::nil) = 2
 /\  rk(P16 :: P24 :: P28 ::nil) = 2
 /\  rk(P17 :: P19 :: P24 ::nil) = 2
 /\  rk(P17 :: P19 :: P28 ::nil) = 2
 /\  rk(P17 :: P24 :: P28 ::nil) = 2
 /\  rk(P19 :: P24 :: P28 ::nil) = 2
 /\  rk(P2 :: P15 :: P16 ::nil) = 2
 /\  rk(P2 :: P15 :: P18 ::nil) = 2
 /\  rk(P2 :: P15 :: P23 ::nil) = 2
 /\  rk(P2 :: P15 :: P27 ::nil) = 2
 /\  rk(P2 :: P16 :: P18 ::nil) = 2
 /\  rk(P2 :: P16 :: P23 ::nil) = 2
 /\  rk(P2 :: P16 :: P27 ::nil) = 2
 /\  rk(P2 :: P18 :: P23 ::nil) = 2
 /\  rk(P2 :: P18 :: P27 ::nil) = 2
 /\  rk(P2 :: P23 :: P27 ::nil) = 2
 /\  rk(P15 :: P16 :: P18 ::nil) = 2
 /\  rk(P15 :: P16 :: P23 ::nil) = 2
 /\  rk(P15 :: P16 :: P27 ::nil) = 2
 /\  rk(P15 :: P18 :: P23 ::nil) = 2
 /\  rk(P15 :: P18 :: P27 ::nil) = 2
 /\  rk(P15 :: P23 :: P27 ::nil) = 2
 /\  rk(P16 :: P18 :: P23 ::nil) = 2
 /\  rk(P16 :: P18 :: P27 ::nil) = 2
 /\  rk(P16 :: P23 :: P27 ::nil) = 2
 /\  rk(P18 :: P23 :: P27 ::nil) = 2
 /\  rk(P1 :: P14 :: P15 ::nil) = 2
 /\  rk(P1 :: P14 :: P17 ::nil) = 2
 /\  rk(P1 :: P14 :: P22 ::nil) = 2
 /\  rk(P1 :: P14 :: P26 ::nil) = 2
 /\  rk(P1 :: P15 :: P17 ::nil) = 2
 /\  rk(P1 :: P15 :: P22 ::nil) = 2
 /\  rk(P1 :: P15 :: P26 ::nil) = 2
 /\  rk(P1 :: P17 :: P22 ::nil) = 2
 /\  rk(P1 :: P17 :: P26 ::nil) = 2
 /\  rk(P1 :: P22 :: P26 ::nil) = 2
 /\  rk(P14 :: P15 :: P17 ::nil) = 2
 /\  rk(P14 :: P15 :: P22 ::nil) = 2
 /\  rk(P14 :: P15 :: P26 ::nil) = 2
 /\  rk(P14 :: P17 :: P22 ::nil) = 2
 /\  rk(P14 :: P17 :: P26 ::nil) = 2
 /\  rk(P14 :: P22 :: P26 ::nil) = 2
 /\  rk(P15 :: P17 :: P22 ::nil) = 2
 /\  rk(P15 :: P17 :: P26 ::nil) = 2
 /\  rk(P15 :: P22 :: P26 ::nil) = 2
 /\  rk(P17 :: P22 :: P26 ::nil) = 2
 /\  rk(P0 :: P13 :: P14 ::nil) = 2
 /\  rk(P0 :: P13 :: P16 ::nil) = 2
 /\  rk(P0 :: P13 :: P21 ::nil) = 2
 /\  rk(P0 :: P13 :: P25 ::nil) = 2
 /\  rk(P0 :: P14 :: P16 ::nil) = 2
 /\  rk(P0 :: P14 :: P21 ::nil) = 2
 /\  rk(P0 :: P14 :: P25 ::nil) = 2
 /\  rk(P0 :: P16 :: P21 ::nil) = 2
 /\  rk(P0 :: P16 :: P25 ::nil) = 2
 /\  rk(P0 :: P21 :: P25 ::nil) = 2
 /\  rk(P13 :: P14 :: P16 ::nil) = 2
 /\  rk(P13 :: P14 :: P21 ::nil) = 2
 /\  rk(P13 :: P14 :: P25 ::nil) = 2
 /\  rk(P13 :: P16 :: P21 ::nil) = 2
 /\  rk(P13 :: P16 :: P25 ::nil) = 2
 /\  rk(P13 :: P21 :: P25 ::nil) = 2
 /\  rk(P14 :: P16 :: P21 ::nil) = 2
 /\  rk(P14 :: P16 :: P25 ::nil) = 2
 /\  rk(P14 :: P21 :: P25 ::nil) = 2
 /\  rk(P16 :: P21 :: P25 ::nil) = 2
 /\  rk(P12 :: P13 :: P15 ::nil) = 2
 /\  rk(P12 :: P13 :: P20 ::nil) = 2
 /\  rk(P12 :: P13 :: P24 ::nil) = 2
 /\  rk(P12 :: P13 :: P30 ::nil) = 2
 /\  rk(P12 :: P15 :: P20 ::nil) = 2
 /\  rk(P12 :: P15 :: P24 ::nil) = 2
 /\  rk(P12 :: P15 :: P30 ::nil) = 2
 /\  rk(P12 :: P20 :: P24 ::nil) = 2
 /\  rk(P12 :: P20 :: P30 ::nil) = 2
 /\  rk(P12 :: P24 :: P30 ::nil) = 2
 /\  rk(P13 :: P15 :: P20 ::nil) = 2
 /\  rk(P13 :: P15 :: P24 ::nil) = 2
 /\  rk(P13 :: P15 :: P30 ::nil) = 2
 /\  rk(P13 :: P20 :: P24 ::nil) = 2
 /\  rk(P13 :: P20 :: P30 ::nil) = 2
 /\  rk(P13 :: P24 :: P30 ::nil) = 2
 /\  rk(P15 :: P20 :: P24 ::nil) = 2
 /\  rk(P15 :: P20 :: P30 ::nil) = 2
 /\  rk(P15 :: P24 :: P30 ::nil) = 2
 /\  rk(P20 :: P24 :: P30 ::nil) = 2
 /\  rk(P11 :: P12 :: P14 ::nil) = 2
 /\  rk(P11 :: P12 :: P19 ::nil) = 2
 /\  rk(P11 :: P12 :: P23 ::nil) = 2
 /\  rk(P11 :: P12 :: P29 ::nil) = 2
 /\  rk(P11 :: P14 :: P19 ::nil) = 2
 /\  rk(P11 :: P14 :: P23 ::nil) = 2
 /\  rk(P11 :: P14 :: P29 ::nil) = 2
 /\  rk(P11 :: P19 :: P23 ::nil) = 2
 /\  rk(P11 :: P19 :: P29 ::nil) = 2
 /\  rk(P11 :: P23 :: P29 ::nil) = 2
 /\  rk(P12 :: P14 :: P19 ::nil) = 2
 /\  rk(P12 :: P14 :: P23 ::nil) = 2
 /\  rk(P12 :: P14 :: P29 ::nil) = 2
 /\  rk(P12 :: P19 :: P23 ::nil) = 2
 /\  rk(P12 :: P19 :: P29 ::nil) = 2
 /\  rk(P12 :: P23 :: P29 ::nil) = 2
 /\  rk(P14 :: P19 :: P23 ::nil) = 2
 /\  rk(P14 :: P19 :: P29 ::nil) = 2
 /\  rk(P14 :: P23 :: P29 ::nil) = 2
 /\  rk(P19 :: P23 :: P29 ::nil) = 2
 /\  rk(P10 :: P11 :: P13 ::nil) = 2
 /\  rk(P10 :: P11 :: P18 ::nil) = 2
 /\  rk(P10 :: P11 :: P22 ::nil) = 2
 /\  rk(P10 :: P11 :: P28 ::nil) = 2
 /\  rk(P10 :: P13 :: P18 ::nil) = 2
 /\  rk(P10 :: P13 :: P22 ::nil) = 2
 /\  rk(P10 :: P13 :: P28 ::nil) = 2
 /\  rk(P10 :: P18 :: P22 ::nil) = 2
 /\  rk(P10 :: P18 :: P28 ::nil) = 2
 /\  rk(P10 :: P22 :: P28 ::nil) = 2
 /\  rk(P11 :: P13 :: P18 ::nil) = 2
 /\  rk(P11 :: P13 :: P22 ::nil) = 2
 /\  rk(P11 :: P13 :: P28 ::nil) = 2
 /\  rk(P11 :: P18 :: P22 ::nil) = 2
 /\  rk(P11 :: P18 :: P28 ::nil) = 2
 /\  rk(P11 :: P22 :: P28 ::nil) = 2
 /\  rk(P13 :: P18 :: P22 ::nil) = 2
 /\  rk(P13 :: P18 :: P28 ::nil) = 2
 /\  rk(P13 :: P22 :: P28 ::nil) = 2
 /\  rk(P18 :: P22 :: P28 ::nil) = 2
 /\  rk(P9 :: P10 :: P12 ::nil) = 2
 /\  rk(P9 :: P10 :: P17 ::nil) = 2
 /\  rk(P9 :: P10 :: P21 ::nil) = 2
 /\  rk(P9 :: P10 :: P27 ::nil) = 2
 /\  rk(P9 :: P12 :: P17 ::nil) = 2
 /\  rk(P9 :: P12 :: P21 ::nil) = 2
 /\  rk(P9 :: P12 :: P27 ::nil) = 2
 /\  rk(P9 :: P17 :: P21 ::nil) = 2
 /\  rk(P9 :: P17 :: P27 ::nil) = 2
 /\  rk(P9 :: P21 :: P27 ::nil) = 2
 /\  rk(P10 :: P12 :: P17 ::nil) = 2
 /\  rk(P10 :: P12 :: P21 ::nil) = 2
 /\  rk(P10 :: P12 :: P27 ::nil) = 2
 /\  rk(P10 :: P17 :: P21 ::nil) = 2
 /\  rk(P10 :: P17 :: P27 ::nil) = 2
 /\  rk(P10 :: P21 :: P27 ::nil) = 2
 /\  rk(P12 :: P17 :: P21 ::nil) = 2
 /\  rk(P12 :: P17 :: P27 ::nil) = 2
 /\  rk(P12 :: P21 :: P27 ::nil) = 2
 /\  rk(P17 :: P21 :: P27 ::nil) = 2
 /\  rk(P8 :: P9 :: P11 ::nil) = 2
 /\  rk(P8 :: P9 :: P16 ::nil) = 2
 /\  rk(P8 :: P9 :: P20 ::nil) = 2
 /\  rk(P8 :: P9 :: P26 ::nil) = 2
 /\  rk(P8 :: P11 :: P16 ::nil) = 2
 /\  rk(P8 :: P11 :: P20 ::nil) = 2
 /\  rk(P8 :: P11 :: P26 ::nil) = 2
 /\  rk(P8 :: P16 :: P20 ::nil) = 2
 /\  rk(P8 :: P16 :: P26 ::nil) = 2
 /\  rk(P8 :: P20 :: P26 ::nil) = 2
 /\  rk(P9 :: P11 :: P16 ::nil) = 2
 /\  rk(P9 :: P11 :: P20 ::nil) = 2
 /\  rk(P9 :: P11 :: P26 ::nil) = 2
 /\  rk(P9 :: P16 :: P20 ::nil) = 2
 /\  rk(P9 :: P16 :: P26 ::nil) = 2
 /\  rk(P9 :: P20 :: P26 ::nil) = 2
 /\  rk(P11 :: P16 :: P20 ::nil) = 2
 /\  rk(P11 :: P16 :: P26 ::nil) = 2
 /\  rk(P11 :: P20 :: P26 ::nil) = 2
 /\  rk(P16 :: P20 :: P26 ::nil) = 2
 /\  rk(P7 :: P8 :: P10 ::nil) = 2
 /\  rk(P7 :: P8 :: P15 ::nil) = 2
 /\  rk(P7 :: P8 :: P19 ::nil) = 2
 /\  rk(P7 :: P8 :: P25 ::nil) = 2
 /\  rk(P7 :: P10 :: P15 ::nil) = 2
 /\  rk(P7 :: P10 :: P19 ::nil) = 2
 /\  rk(P7 :: P10 :: P25 ::nil) = 2
 /\  rk(P7 :: P15 :: P19 ::nil) = 2
 /\  rk(P7 :: P15 :: P25 ::nil) = 2
 /\  rk(P7 :: P19 :: P25 ::nil) = 2
 /\  rk(P8 :: P10 :: P15 ::nil) = 2
 /\  rk(P8 :: P10 :: P19 ::nil) = 2
 /\  rk(P8 :: P10 :: P25 ::nil) = 2
 /\  rk(P8 :: P15 :: P19 ::nil) = 2
 /\  rk(P8 :: P15 :: P25 ::nil) = 2
 /\  rk(P8 :: P19 :: P25 ::nil) = 2
 /\  rk(P10 :: P15 :: P19 ::nil) = 2
 /\  rk(P10 :: P15 :: P25 ::nil) = 2
 /\  rk(P10 :: P19 :: P25 ::nil) = 2
 /\  rk(P15 :: P19 :: P25 ::nil) = 2
 /\  rk(P6 :: P7 :: P9 ::nil) = 2
 /\  rk(P6 :: P7 :: P14 ::nil) = 2
 /\  rk(P6 :: P7 :: P18 ::nil) = 2
 /\  rk(P6 :: P7 :: P24 ::nil) = 2
 /\  rk(P6 :: P9 :: P14 ::nil) = 2
 /\  rk(P6 :: P9 :: P18 ::nil) = 2
 /\  rk(P6 :: P9 :: P24 ::nil) = 2
 /\  rk(P6 :: P14 :: P18 ::nil) = 2
 /\  rk(P6 :: P14 :: P24 ::nil) = 2
 /\  rk(P6 :: P18 :: P24 ::nil) = 2
 /\  rk(P7 :: P9 :: P14 ::nil) = 2
 /\  rk(P7 :: P9 :: P18 ::nil) = 2
 /\  rk(P7 :: P9 :: P24 ::nil) = 2
 /\  rk(P7 :: P14 :: P18 ::nil) = 2
 /\  rk(P7 :: P14 :: P24 ::nil) = 2
 /\  rk(P7 :: P18 :: P24 ::nil) = 2
 /\  rk(P9 :: P14 :: P18 ::nil) = 2
 /\  rk(P9 :: P14 :: P24 ::nil) = 2
 /\  rk(P9 :: P18 :: P24 ::nil) = 2
 /\  rk(P14 :: P18 :: P24 ::nil) = 2
 /\  rk(P5 :: P6 :: P8 ::nil) = 2
 /\  rk(P5 :: P6 :: P13 ::nil) = 2
 /\  rk(P5 :: P6 :: P17 ::nil) = 2
 /\  rk(P5 :: P6 :: P23 ::nil) = 2
 /\  rk(P5 :: P8 :: P13 ::nil) = 2
 /\  rk(P5 :: P8 :: P17 ::nil) = 2
 /\  rk(P5 :: P8 :: P23 ::nil) = 2
 /\  rk(P5 :: P13 :: P17 ::nil) = 2
 /\  rk(P5 :: P13 :: P23 ::nil) = 2
 /\  rk(P5 :: P17 :: P23 ::nil) = 2
 /\  rk(P6 :: P8 :: P13 ::nil) = 2
 /\  rk(P6 :: P8 :: P17 ::nil) = 2
 /\  rk(P6 :: P8 :: P23 ::nil) = 2
 /\  rk(P6 :: P13 :: P17 ::nil) = 2
 /\  rk(P6 :: P13 :: P23 ::nil) = 2
 /\  rk(P6 :: P17 :: P23 ::nil) = 2
 /\  rk(P8 :: P13 :: P17 ::nil) = 2
 /\  rk(P8 :: P13 :: P23 ::nil) = 2
 /\  rk(P8 :: P17 :: P23 ::nil) = 2
 /\  rk(P13 :: P17 :: P23 ::nil) = 2
 /\  rk(P4 :: P5 :: P7 ::nil) = 2
 /\  rk(P4 :: P5 :: P12 ::nil) = 2
 /\  rk(P4 :: P5 :: P16 ::nil) = 2
 /\  rk(P4 :: P5 :: P22 ::nil) = 2
 /\  rk(P4 :: P7 :: P12 ::nil) = 2
 /\  rk(P4 :: P7 :: P16 ::nil) = 2
 /\  rk(P4 :: P7 :: P22 ::nil) = 2
 /\  rk(P4 :: P12 :: P16 ::nil) = 2
 /\  rk(P4 :: P12 :: P22 ::nil) = 2
 /\  rk(P4 :: P16 :: P22 ::nil) = 2
 /\  rk(P5 :: P7 :: P12 ::nil) = 2
 /\  rk(P5 :: P7 :: P16 ::nil) = 2
 /\  rk(P5 :: P7 :: P22 ::nil) = 2
 /\  rk(P5 :: P12 :: P16 ::nil) = 2
 /\  rk(P5 :: P12 :: P22 ::nil) = 2
 /\  rk(P5 :: P16 :: P22 ::nil) = 2
 /\  rk(P7 :: P12 :: P16 ::nil) = 2
 /\  rk(P7 :: P12 :: P22 ::nil) = 2
 /\  rk(P7 :: P16 :: P22 ::nil) = 2
 /\  rk(P12 :: P16 :: P22 ::nil) = 2
 /\  rk(P3 :: P4 :: P6 ::nil) = 2
 /\  rk(P3 :: P4 :: P11 ::nil) = 2
 /\  rk(P3 :: P4 :: P15 ::nil) = 2
 /\  rk(P3 :: P4 :: P21 ::nil) = 2
 /\  rk(P3 :: P6 :: P11 ::nil) = 2
 /\  rk(P3 :: P6 :: P15 ::nil) = 2
 /\  rk(P3 :: P6 :: P21 ::nil) = 2
 /\  rk(P3 :: P11 :: P15 ::nil) = 2
 /\  rk(P3 :: P11 :: P21 ::nil) = 2
 /\  rk(P3 :: P15 :: P21 ::nil) = 2
 /\  rk(P4 :: P6 :: P11 ::nil) = 2
 /\  rk(P4 :: P6 :: P15 ::nil) = 2
 /\  rk(P4 :: P6 :: P21 ::nil) = 2
 /\  rk(P4 :: P11 :: P15 ::nil) = 2
 /\  rk(P4 :: P11 :: P21 ::nil) = 2
 /\  rk(P4 :: P15 :: P21 ::nil) = 2
 /\  rk(P6 :: P11 :: P15 ::nil) = 2
 /\  rk(P6 :: P11 :: P21 ::nil) = 2
 /\  rk(P6 :: P15 :: P21 ::nil) = 2
 /\  rk(P11 :: P15 :: P21 ::nil) = 2
 /\  rk(P2 :: P3 :: P5 ::nil) = 2
 /\  rk(P2 :: P3 :: P10 ::nil) = 2
 /\  rk(P2 :: P3 :: P14 ::nil) = 2
 /\  rk(P2 :: P3 :: P20 ::nil) = 2
 /\  rk(P2 :: P5 :: P10 ::nil) = 2
 /\  rk(P2 :: P5 :: P14 ::nil) = 2
 /\  rk(P2 :: P5 :: P20 ::nil) = 2
 /\  rk(P2 :: P10 :: P14 ::nil) = 2
 /\  rk(P2 :: P10 :: P20 ::nil) = 2
 /\  rk(P2 :: P14 :: P20 ::nil) = 2
 /\  rk(P3 :: P5 :: P10 ::nil) = 2
 /\  rk(P3 :: P5 :: P14 ::nil) = 2
 /\  rk(P3 :: P5 :: P20 ::nil) = 2
 /\  rk(P3 :: P10 :: P14 ::nil) = 2
 /\  rk(P3 :: P10 :: P20 ::nil) = 2
 /\  rk(P3 :: P14 :: P20 ::nil) = 2
 /\  rk(P5 :: P10 :: P14 ::nil) = 2
 /\  rk(P5 :: P10 :: P20 ::nil) = 2
 /\  rk(P5 :: P14 :: P20 ::nil) = 2
 /\  rk(P10 :: P14 :: P20 ::nil) = 2
 /\  rk(P1 :: P2 :: P4 ::nil) = 2
 /\  rk(P1 :: P2 :: P9 ::nil) = 2
 /\  rk(P1 :: P2 :: P13 ::nil) = 2
 /\  rk(P1 :: P2 :: P19 ::nil) = 2
 /\  rk(P1 :: P4 :: P9 ::nil) = 2
 /\  rk(P1 :: P4 :: P13 ::nil) = 2
 /\  rk(P1 :: P4 :: P19 ::nil) = 2
 /\  rk(P1 :: P9 :: P13 ::nil) = 2
 /\  rk(P1 :: P9 :: P19 ::nil) = 2
 /\  rk(P1 :: P13 :: P19 ::nil) = 2
 /\  rk(P2 :: P4 :: P9 ::nil) = 2
 /\  rk(P2 :: P4 :: P13 ::nil) = 2
 /\  rk(P2 :: P4 :: P19 ::nil) = 2
 /\  rk(P2 :: P9 :: P13 ::nil) = 2
 /\  rk(P2 :: P9 :: P19 ::nil) = 2
 /\  rk(P2 :: P13 :: P19 ::nil) = 2
 /\  rk(P4 :: P9 :: P13 ::nil) = 2
 /\  rk(P4 :: P9 :: P19 ::nil) = 2
 /\  rk(P4 :: P13 :: P19 ::nil) = 2
 /\  rk(P9 :: P13 :: P19 ::nil) = 2
.

Parameter rk_planes : 
rk ( P0 :: P2 :: P7 ::nil )= 3 /\ rk ( P0 :: P2 :: P11 ::nil )= 3 /\ rk ( P0 :: P2 :: P17 ::nil )= 3 /\ rk ( P0 :: P2 :: P30 ::nil )= 3 /\ rk ( P0 :: P4 :: P10 ::nil )= 3 /\ rk ( P0 :: P4 :: P23 ::nil )= 3 /\ rk ( P0 :: P4 :: P24 ::nil )= 3 /\ rk ( P0 :: P4 :: P26 ::nil )= 3 /\ rk ( P0 :: P5 :: P9 ::nil )= 3 /\ rk ( P0 :: P5 :: P15 ::nil )= 3 /\ rk ( P0 :: P5 :: P28 ::nil )= 3 /\ rk ( P0 :: P5 :: P29 ::nil )= 3 /\ rk ( P0 :: P6 :: P19 ::nil )= 3 /\ rk ( P0 :: P6 :: P20 ::nil )= 3 /\ rk ( P0 :: P6 :: P22 ::nil )= 3 /\ rk ( P0 :: P6 :: P27 ::nil )= 3 /\ rk ( P0 :: P7 :: P11 ::nil )= 3 /\ rk ( P0 :: P7 :: P17 ::nil )= 3 /\ rk ( P0 :: P7 :: P30 ::nil )= 3 /\ rk ( P0 :: P9 :: P15 ::nil )= 3 /\ rk ( P0 :: P9 :: P28 ::nil )= 3 /\ rk ( P0 :: P9 :: P29 ::nil )= 3 /\ rk ( P0 :: P10 :: P23 ::nil )= 3 /\ rk ( P0 :: P10 :: P24 ::nil )= 3 /\ rk ( P0 :: P10 :: P26 ::nil )= 3 /\ rk ( P0 :: P11 :: P17 ::nil )= 3 /\ rk ( P0 :: P11 :: P30 ::nil )= 3 /\ rk ( P0 :: P13 :: P14 ::nil )= 3 /\ rk ( P0 :: P13 :: P16 ::nil )= 3 /\ rk ( P0 :: P13 :: P21 ::nil )= 3 /\ rk ( P0 :: P13 :: P25 ::nil )= 3 /\ rk ( P0 :: P14 :: P16 ::nil )= 3 /\ rk ( P0 :: P14 :: P21 ::nil )= 3 /\ rk ( P0 :: P14 :: P25 ::nil )= 3 /\ rk ( P0 :: P15 :: P28 ::nil )= 3 /\ rk ( P0 :: P15 :: P29 ::nil )= 3 /\ rk ( P0 :: P16 :: P21 ::nil )= 3 /\ rk ( P0 :: P16 :: P25 ::nil )= 3 /\ rk ( P0 :: P17 :: P30 ::nil )= 3 /\ rk ( P0 :: P19 :: P20 ::nil )= 3 /\ rk ( P0 :: P19 :: P22 ::nil )= 3 /\ rk ( P0 :: P19 :: P27 ::nil )= 3 /\ rk ( P0 :: P20 :: P22 ::nil )= 3 /\ rk ( P0 :: P20 :: P27 ::nil )= 3 /\ rk ( P0 :: P21 :: P25 ::nil )= 3 /\ rk ( P0 :: P22 :: P27 ::nil )= 3 /\ rk ( P0 :: P23 :: P24 ::nil )= 3 /\ rk ( P0 :: P23 :: P26 ::nil )= 3 /\ rk ( P0 :: P24 :: P26 ::nil )= 3 /\ rk ( P0 :: P28 :: P29 ::nil )= 3 /\ rk ( P1 :: P2 :: P4 ::nil )= 3 /\ rk ( P1 :: P2 :: P9 ::nil )= 3 /\ rk ( P1 :: P2 :: P13 ::nil )= 3 /\ rk ( P1 :: P2 :: P19 ::nil )= 3 /\ rk ( P1 :: P4 :: P9 ::nil )= 3 /\ rk ( P1 :: P4 :: P13 ::nil )= 3 /\ rk ( P1 :: P4 :: P19 ::nil )= 3 /\ rk ( P1 :: P5 :: P11 ::nil )= 3 /\ rk ( P1 :: P5 :: P24 ::nil )= 3 /\ rk ( P1 :: P5 :: P25 ::nil )= 3 /\ rk ( P1 :: P5 :: P27 ::nil )= 3 /\ rk ( P1 :: P6 :: P10 ::nil )= 3 /\ rk ( P1 :: P6 :: P16 ::nil )= 3 /\ rk ( P1 :: P6 :: P29 ::nil )= 3 /\ rk ( P1 :: P6 :: P30 ::nil )= 3 /\ rk ( P1 :: P7 :: P20 ::nil )= 3 /\ rk ( P1 :: P7 :: P21 ::nil )= 3 /\ rk ( P1 :: P7 :: P23 ::nil )= 3 /\ rk ( P1 :: P7 :: P28 ::nil )= 3 /\ rk ( P1 :: P9 :: P13 ::nil )= 3 /\ rk ( P1 :: P9 :: P19 ::nil )= 3 /\ rk ( P1 :: P10 :: P16 ::nil )= 3 /\ rk ( P1 :: P10 :: P29 ::nil )= 3 /\ rk ( P1 :: P10 :: P30 ::nil )= 3 /\ rk ( P1 :: P11 :: P24 ::nil )= 3 /\ rk ( P1 :: P11 :: P25 ::nil )= 3 /\ rk ( P1 :: P11 :: P27 ::nil )= 3 /\ rk ( P1 :: P13 :: P19 ::nil )= 3 /\ rk ( P1 :: P14 :: P15 ::nil )= 3 /\ rk ( P1 :: P14 :: P17 ::nil )= 3 /\ rk ( P1 :: P14 :: P22 ::nil )= 3 /\ rk ( P1 :: P14 :: P26 ::nil )= 3 /\ rk ( P1 :: P15 :: P17 ::nil )= 3 /\ rk ( P1 :: P15 :: P22 ::nil )= 3 /\ rk ( P1 :: P15 :: P26 ::nil )= 3 /\ rk ( P1 :: P16 :: P29 ::nil )= 3 /\ rk ( P1 :: P16 :: P30 ::nil )= 3 /\ rk ( P1 :: P17 :: P22 ::nil )= 3 /\ rk ( P1 :: P17 :: P26 ::nil )= 3 /\ rk ( P1 :: P20 :: P21 ::nil )= 3 /\ rk ( P1 :: P20 :: P23 ::nil )= 3 /\ rk ( P1 :: P20 :: P28 ::nil )= 3 /\ rk ( P1 :: P21 :: P23 ::nil )= 3 /\ rk ( P1 :: P21 :: P28 ::nil )= 3 /\ rk ( P1 :: P22 :: P26 ::nil )= 3 /\ rk ( P1 :: P23 :: P28 ::nil )= 3 /\ rk ( P1 :: P24 :: P25 ::nil )= 3 /\ rk ( P1 :: P24 :: P27 ::nil )= 3 /\ rk ( P1 :: P25 :: P27 ::nil )= 3 /\ rk ( P1 :: P29 :: P30 ::nil )= 3 /\ rk ( P2 :: P3 :: P5 ::nil )= 3 /\ rk ( P2 :: P3 :: P10 ::nil )= 3 /\ rk ( P2 :: P3 :: P14 ::nil )= 3 /\ rk ( P2 :: P3 :: P20 ::nil )= 3 /\ rk ( P2 :: P4 :: P9 ::nil )= 3 /\ rk ( P2 :: P4 :: P13 ::nil )= 3 /\ rk ( P2 :: P4 :: P19 ::nil )= 3 /\ rk ( P2 :: P5 :: P10 ::nil )= 3 /\ rk ( P2 :: P5 :: P14 ::nil )= 3 /\ rk ( P2 :: P5 :: P20 ::nil )= 3 /\ rk ( P2 :: P6 :: P12 ::nil )= 3 /\ rk ( P2 :: P6 :: P25 ::nil )= 3 /\ rk ( P2 :: P6 :: P26 ::nil )= 3 /\ rk ( P2 :: P6 :: P28 ::nil )= 3 /\ rk ( P2 :: P7 :: P11 ::nil )= 3 /\ rk ( P2 :: P7 :: P17 ::nil )= 3 /\ rk ( P2 :: P7 :: P30 ::nil )= 3 /\ rk ( P2 :: P8 :: P21 ::nil )= 3 /\ rk ( P2 :: P8 :: P22 ::nil )= 3 /\ rk ( P2 :: P8 :: P24 ::nil )= 3 /\ rk ( P2 :: P8 :: P29 ::nil )= 3 /\ rk ( P2 :: P9 :: P13 ::nil )= 3 /\ rk ( P2 :: P9 :: P19 ::nil )= 3 /\ rk ( P2 :: P10 :: P14 ::nil )= 3 /\ rk ( P2 :: P10 :: P20 ::nil )= 3 /\ rk ( P2 :: P11 :: P17 ::nil )= 3 /\ rk ( P2 :: P11 :: P30 ::nil )= 3 /\ rk ( P2 :: P12 :: P25 ::nil )= 3 /\ rk ( P2 :: P12 :: P26 ::nil )= 3 /\ rk ( P2 :: P12 :: P28 ::nil )= 3 /\ rk ( P2 :: P13 :: P19 ::nil )= 3 /\ rk ( P2 :: P14 :: P20 ::nil )= 3 /\ rk ( P2 :: P15 :: P16 ::nil )= 3 /\ rk ( P2 :: P15 :: P18 ::nil )= 3 /\ rk ( P2 :: P15 :: P23 ::nil )= 3 /\ rk ( P2 :: P15 :: P27 ::nil )= 3 /\ rk ( P2 :: P16 :: P18 ::nil )= 3 /\ rk ( P2 :: P16 :: P23 ::nil )= 3 /\ rk ( P2 :: P16 :: P27 ::nil )= 3 /\ rk ( P2 :: P17 :: P30 ::nil )= 3 /\ rk ( P2 :: P18 :: P23 ::nil )= 3 /\ rk ( P2 :: P18 :: P27 ::nil )= 3 /\ rk ( P2 :: P21 :: P22 ::nil )= 3 /\ rk ( P2 :: P21 :: P24 ::nil )= 3 /\ rk ( P2 :: P21 :: P29 ::nil )= 3 /\ rk ( P2 :: P22 :: P24 ::nil )= 3 /\ rk ( P2 :: P22 :: P29 ::nil )= 3 /\ rk ( P2 :: P23 :: P27 ::nil )= 3 /\ rk ( P2 :: P24 :: P29 ::nil )= 3 /\ rk ( P2 :: P25 :: P26 ::nil )= 3 /\ rk ( P2 :: P25 :: P28 ::nil )= 3 /\ rk ( P2 :: P26 :: P28 ::nil )= 3 /\ rk ( P3 :: P4 :: P6 ::nil )= 3 /\ rk ( P3 :: P4 :: P11 ::nil )= 3 /\ rk ( P3 :: P4 :: P15 ::nil )= 3 /\ rk ( P3 :: P4 :: P21 ::nil )= 3 /\ rk ( P3 :: P5 :: P10 ::nil )= 3 /\ rk ( P3 :: P5 :: P14 ::nil )= 3 /\ rk ( P3 :: P5 :: P20 ::nil )= 3 /\ rk ( P3 :: P6 :: P11 ::nil )= 3 /\ rk ( P3 :: P6 :: P15 ::nil )= 3 /\ rk ( P3 :: P6 :: P21 ::nil )= 3 /\ rk ( P3 :: P7 :: P13 ::nil )= 3 /\ rk ( P3 :: P7 :: P26 ::nil )= 3 /\ rk ( P3 :: P7 :: P27 ::nil )= 3 /\ rk ( P3 :: P7 :: P29 ::nil )= 3 /\ rk ( P3 :: P9 :: P22 ::nil )= 3 /\ rk ( P3 :: P9 :: P23 ::nil )= 3 /\ rk ( P3 :: P9 :: P25 ::nil )= 3 /\ rk ( P3 :: P9 :: P30 ::nil )= 3 /\ rk ( P3 :: P10 :: P14 ::nil )= 3 /\ rk ( P3 :: P10 :: P20 ::nil )= 3 /\ rk ( P3 :: P11 :: P15 ::nil )= 3 /\ rk ( P3 :: P11 :: P21 ::nil )= 3 /\ rk ( P3 :: P13 :: P26 ::nil )= 3 /\ rk ( P3 :: P13 :: P27 ::nil )= 3 /\ rk ( P3 :: P13 :: P29 ::nil )= 3 /\ rk ( P3 :: P14 :: P20 ::nil )= 3 /\ rk ( P3 :: P15 :: P21 ::nil )= 3 /\ rk ( P3 :: P16 :: P17 ::nil )= 3 /\ rk ( P3 :: P16 :: P19 ::nil )= 3 /\ rk ( P3 :: P16 :: P24 ::nil )= 3 /\ rk ( P3 :: P16 :: P28 ::nil )= 3 /\ rk ( P3 :: P17 :: P19 ::nil )= 3 /\ rk ( P3 :: P17 :: P24 ::nil )= 3 /\ rk ( P3 :: P17 :: P28 ::nil )= 3 /\ rk ( P3 :: P19 :: P24 ::nil )= 3 /\ rk ( P3 :: P19 :: P28 ::nil )= 3 /\ rk ( P3 :: P22 :: P23 ::nil )= 3 /\ rk ( P3 :: P22 :: P25 ::nil )= 3 /\ rk ( P3 :: P22 :: P30 ::nil )= 3 /\ rk ( P3 :: P23 :: P25 ::nil )= 3 /\ rk ( P3 :: P23 :: P30 ::nil )= 3 /\ rk ( P3 :: P24 :: P28 ::nil )= 3 /\ rk ( P3 :: P25 :: P30 ::nil )= 3 /\ rk ( P3 :: P26 :: P27 ::nil )= 3 /\ rk ( P3 :: P26 :: P29 ::nil )= 3 /\ rk ( P3 :: P27 :: P29 ::nil )= 3 /\ rk ( P4 :: P5 :: P7 ::nil )= 3 /\ rk ( P4 :: P5 :: P12 ::nil )= 3 /\ rk ( P4 :: P5 :: P16 ::nil )= 3 /\ rk ( P4 :: P5 :: P22 ::nil )= 3 /\ rk ( P4 :: P6 :: P11 ::nil )= 3 /\ rk ( P4 :: P6 :: P15 ::nil )= 3 /\ rk ( P4 :: P6 :: P21 ::nil )= 3 /\ rk ( P4 :: P7 :: P12 ::nil )= 3 /\ rk ( P4 :: P7 :: P16 ::nil )= 3 /\ rk ( P4 :: P7 :: P22 ::nil )= 3 /\ rk ( P4 :: P8 :: P14 ::nil )= 3 /\ rk ( P4 :: P8 :: P27 ::nil )= 3 /\ rk ( P4 :: P8 :: P28 ::nil )= 3 /\ rk ( P4 :: P8 :: P30 ::nil )= 3 /\ rk ( P4 :: P9 :: P13 ::nil )= 3 /\ rk ( P4 :: P9 :: P19 ::nil )= 3 /\ rk ( P4 :: P10 :: P23 ::nil )= 3 /\ rk ( P4 :: P10 :: P24 ::nil )= 3 /\ rk ( P4 :: P10 :: P26 ::nil )= 3 /\ rk ( P4 :: P11 :: P15 ::nil )= 3 /\ rk ( P4 :: P11 :: P21 ::nil )= 3 /\ rk ( P4 :: P12 :: P16 ::nil )= 3 /\ rk ( P4 :: P12 :: P22 ::nil )= 3 /\ rk ( P4 :: P13 :: P19 ::nil )= 3 /\ rk ( P4 :: P14 :: P27 ::nil )= 3 /\ rk ( P4 :: P14 :: P28 ::nil )= 3 /\ rk ( P4 :: P14 :: P30 ::nil )= 3 /\ rk ( P4 :: P15 :: P21 ::nil )= 3 /\ rk ( P4 :: P16 :: P22 ::nil )= 3 /\ rk ( P4 :: P17 :: P18 ::nil )= 3 /\ rk ( P4 :: P17 :: P20 ::nil )= 3 /\ rk ( P4 :: P17 :: P25 ::nil )= 3 /\ rk ( P4 :: P17 :: P29 ::nil )= 3 /\ rk ( P4 :: P18 :: P20 ::nil )= 3 /\ rk ( P4 :: P18 :: P25 ::nil )= 3 /\ rk ( P4 :: P18 :: P29 ::nil )= 3 /\ rk ( P4 :: P20 :: P25 ::nil )= 3 /\ rk ( P4 :: P20 :: P29 ::nil )= 3 /\ rk ( P4 :: P23 :: P24 ::nil )= 3 /\ rk ( P4 :: P23 :: P26 ::nil )= 3 /\ rk ( P4 :: P24 :: P26 ::nil )= 3 /\ rk ( P4 :: P25 :: P29 ::nil )= 3 /\ rk ( P4 :: P27 :: P28 ::nil )= 3 /\ rk ( P4 :: P27 :: P30 ::nil )= 3 /\ rk ( P4 :: P28 :: P30 ::nil )= 3 /\ rk ( P5 :: P6 :: P8 ::nil )= 3 /\ rk ( P5 :: P6 :: P13 ::nil )= 3 /\ rk ( P5 :: P6 :: P17 ::nil )= 3 /\ rk ( P5 :: P6 :: P23 ::nil )= 3 /\ rk ( P5 :: P7 :: P12 ::nil )= 3 /\ rk ( P5 :: P7 :: P16 ::nil )= 3 /\ rk ( P5 :: P7 :: P22 ::nil )= 3 /\ rk ( P5 :: P8 :: P13 ::nil )= 3 /\ rk ( P5 :: P8 :: P17 ::nil )= 3 /\ rk ( P5 :: P8 :: P23 ::nil )= 3 /\ rk ( P5 :: P9 :: P15 ::nil )= 3 /\ rk ( P5 :: P9 :: P28 ::nil )= 3 /\ rk ( P5 :: P9 :: P29 ::nil )= 3 /\ rk ( P5 :: P10 :: P14 ::nil )= 3 /\ rk ( P5 :: P10 :: P20 ::nil )= 3 /\ rk ( P5 :: P11 :: P24 ::nil )= 3 /\ rk ( P5 :: P11 :: P25 ::nil )= 3 /\ rk ( P5 :: P11 :: P27 ::nil )= 3 /\ rk ( P5 :: P12 :: P16 ::nil )= 3 /\ rk ( P5 :: P12 :: P22 ::nil )= 3 /\ rk ( P5 :: P13 :: P17 ::nil )= 3 /\ rk ( P5 :: P13 :: P23 ::nil )= 3 /\ rk ( P5 :: P14 :: P20 ::nil )= 3 /\ rk ( P5 :: P15 :: P28 ::nil )= 3 /\ rk ( P5 :: P15 :: P29 ::nil )= 3 /\ rk ( P5 :: P16 :: P22 ::nil )= 3 /\ rk ( P5 :: P17 :: P23 ::nil )= 3 /\ rk ( P5 :: P18 :: P19 ::nil )= 3 /\ rk ( P5 :: P18 :: P21 ::nil )= 3 /\ rk ( P5 :: P18 :: P26 ::nil )= 3 /\ rk ( P5 :: P18 :: P30 ::nil )= 3 /\ rk ( P5 :: P19 :: P21 ::nil )= 3 /\ rk ( P5 :: P19 :: P26 ::nil )= 3 /\ rk ( P5 :: P19 :: P30 ::nil )= 3 /\ rk ( P5 :: P21 :: P26 ::nil )= 3 /\ rk ( P5 :: P21 :: P30 ::nil )= 3 /\ rk ( P5 :: P24 :: P25 ::nil )= 3 /\ rk ( P5 :: P24 :: P27 ::nil )= 3 /\ rk ( P5 :: P25 :: P27 ::nil )= 3 /\ rk ( P5 :: P26 :: P30 ::nil )= 3 /\ rk ( P5 :: P28 :: P29 ::nil )= 3 /\ rk ( P6 :: P7 :: P9 ::nil )= 3 /\ rk ( P6 :: P7 :: P14 ::nil )= 3 /\ rk ( P6 :: P7 :: P18 ::nil )= 3 /\ rk ( P6 :: P7 :: P24 ::nil )= 3 /\ rk ( P6 :: P8 :: P13 ::nil )= 3 /\ rk ( P6 :: P8 :: P17 ::nil )= 3 /\ rk ( P6 :: P8 :: P23 ::nil )= 3 /\ rk ( P6 :: P9 :: P14 ::nil )= 3 /\ rk ( P6 :: P9 :: P18 ::nil )= 3 /\ rk ( P6 :: P9 :: P24 ::nil )= 3 /\ rk ( P6 :: P10 :: P16 ::nil )= 3 /\ rk ( P6 :: P10 :: P29 ::nil )= 3 /\ rk ( P6 :: P10 :: P30 ::nil )= 3 /\ rk ( P6 :: P11 :: P15 ::nil )= 3 /\ rk ( P6 :: P11 :: P21 ::nil )= 3 /\ rk ( P6 :: P12 :: P25 ::nil )= 3 /\ rk ( P6 :: P12 :: P26 ::nil )= 3 /\ rk ( P6 :: P12 :: P28 ::nil )= 3 /\ rk ( P6 :: P13 :: P17 ::nil )= 3 /\ rk ( P6 :: P13 :: P23 ::nil )= 3 /\ rk ( P6 :: P14 :: P18 ::nil )= 3 /\ rk ( P6 :: P14 :: P24 ::nil )= 3 /\ rk ( P6 :: P15 :: P21 ::nil )= 3 /\ rk ( P6 :: P16 :: P29 ::nil )= 3 /\ rk ( P6 :: P16 :: P30 ::nil )= 3 /\ rk ( P6 :: P17 :: P23 ::nil )= 3 /\ rk ( P6 :: P18 :: P24 ::nil )= 3 /\ rk ( P6 :: P19 :: P20 ::nil )= 3 /\ rk ( P6 :: P19 :: P22 ::nil )= 3 /\ rk ( P6 :: P19 :: P27 ::nil )= 3 /\ rk ( P6 :: P20 :: P22 ::nil )= 3 /\ rk ( P6 :: P20 :: P27 ::nil )= 3 /\ rk ( P6 :: P22 :: P27 ::nil )= 3 /\ rk ( P6 :: P25 :: P26 ::nil )= 3 /\ rk ( P6 :: P25 :: P28 ::nil )= 3 /\ rk ( P6 :: P26 :: P28 ::nil )= 3 /\ rk ( P6 :: P29 :: P30 ::nil )= 3 /\ rk ( P7 :: P8 :: P10 ::nil )= 3 /\ rk ( P7 :: P8 :: P15 ::nil )= 3 /\ rk ( P7 :: P8 :: P19 ::nil )= 3 /\ rk ( P7 :: P8 :: P25 ::nil )= 3 /\ rk ( P7 :: P9 :: P14 ::nil )= 3 /\ rk ( P7 :: P9 :: P18 ::nil )= 3 /\ rk ( P7 :: P9 :: P24 ::nil )= 3 /\ rk ( P7 :: P10 :: P15 ::nil )= 3 /\ rk ( P7 :: P10 :: P19 ::nil )= 3 /\ rk ( P7 :: P10 :: P25 ::nil )= 3 /\ rk ( P7 :: P11 :: P17 ::nil )= 3 /\ rk ( P7 :: P11 :: P30 ::nil )= 3 /\ rk ( P7 :: P12 :: P16 ::nil )= 3 /\ rk ( P7 :: P12 :: P22 ::nil )= 3 /\ rk ( P7 :: P13 :: P26 ::nil )= 3 /\ rk ( P7 :: P13 :: P27 ::nil )= 3 /\ rk ( P7 :: P13 :: P29 ::nil )= 3 /\ rk ( P7 :: P14 :: P18 ::nil )= 3 /\ rk ( P7 :: P14 :: P24 ::nil )= 3 /\ rk ( P7 :: P15 :: P19 ::nil )= 3 /\ rk ( P7 :: P15 :: P25 ::nil )= 3 /\ rk ( P7 :: P16 :: P22 ::nil )= 3 /\ rk ( P7 :: P17 :: P30 ::nil )= 3 /\ rk ( P7 :: P18 :: P24 ::nil )= 3 /\ rk ( P7 :: P19 :: P25 ::nil )= 3 /\ rk ( P7 :: P20 :: P21 ::nil )= 3 /\ rk ( P7 :: P20 :: P23 ::nil )= 3 /\ rk ( P7 :: P20 :: P28 ::nil )= 3 /\ rk ( P7 :: P21 :: P23 ::nil )= 3 /\ rk ( P7 :: P21 :: P28 ::nil )= 3 /\ rk ( P7 :: P23 :: P28 ::nil )= 3 /\ rk ( P7 :: P26 :: P27 ::nil )= 3 /\ rk ( P7 :: P26 :: P29 ::nil )= 3 /\ rk ( P7 :: P27 :: P29 ::nil )= 3 /\ rk ( P8 :: P9 :: P11 ::nil )= 3 /\ rk ( P8 :: P9 :: P16 ::nil )= 3 /\ rk ( P8 :: P9 :: P20 ::nil )= 3 /\ rk ( P8 :: P9 :: P26 ::nil )= 3 /\ rk ( P8 :: P10 :: P15 ::nil )= 3 /\ rk ( P8 :: P10 :: P19 ::nil )= 3 /\ rk ( P8 :: P10 :: P25 ::nil )= 3 /\ rk ( P8 :: P11 :: P16 ::nil )= 3 /\ rk ( P8 :: P11 :: P20 ::nil )= 3 /\ rk ( P8 :: P11 :: P26 ::nil )= 3 /\ rk ( P8 :: P13 :: P17 ::nil )= 3 /\ rk ( P8 :: P13 :: P23 ::nil )= 3 /\ rk ( P8 :: P14 :: P27 ::nil )= 3 /\ rk ( P8 :: P14 :: P28 ::nil )= 3 /\ rk ( P8 :: P14 :: P30 ::nil )= 3 /\ rk ( P8 :: P15 :: P19 ::nil )= 3 /\ rk ( P8 :: P15 :: P25 ::nil )= 3 /\ rk ( P8 :: P16 :: P20 ::nil )= 3 /\ rk ( P8 :: P16 :: P26 ::nil )= 3 /\ rk ( P8 :: P17 :: P23 ::nil )= 3 /\ rk ( P8 :: P19 :: P25 ::nil )= 3 /\ rk ( P8 :: P20 :: P26 ::nil )= 3 /\ rk ( P8 :: P21 :: P22 ::nil )= 3 /\ rk ( P8 :: P21 :: P24 ::nil )= 3 /\ rk ( P8 :: P21 :: P29 ::nil )= 3 /\ rk ( P8 :: P22 :: P24 ::nil )= 3 /\ rk ( P8 :: P22 :: P29 ::nil )= 3 /\ rk ( P8 :: P24 :: P29 ::nil )= 3 /\ rk ( P8 :: P27 :: P28 ::nil )= 3 /\ rk ( P8 :: P27 :: P30 ::nil )= 3 /\ rk ( P8 :: P28 :: P30 ::nil )= 3 /\ rk ( P9 :: P10 :: P12 ::nil )= 3 /\ rk ( P9 :: P10 :: P17 ::nil )= 3 /\ rk ( P9 :: P10 :: P21 ::nil )= 3 /\ rk ( P9 :: P10 :: P27 ::nil )= 3 /\ rk ( P9 :: P11 :: P16 ::nil )= 3 /\ rk ( P9 :: P11 :: P20 ::nil )= 3 /\ rk ( P9 :: P11 :: P26 ::nil )= 3 /\ rk ( P9 :: P12 :: P17 ::nil )= 3 /\ rk ( P9 :: P12 :: P21 ::nil )= 3 /\ rk ( P9 :: P12 :: P27 ::nil )= 3 /\ rk ( P9 :: P13 :: P19 ::nil )= 3 /\ rk ( P9 :: P14 :: P18 ::nil )= 3 /\ rk ( P9 :: P14 :: P24 ::nil )= 3 /\ rk ( P9 :: P15 :: P28 ::nil )= 3 /\ rk ( P9 :: P15 :: P29 ::nil )= 3 /\ rk ( P9 :: P16 :: P20 ::nil )= 3 /\ rk ( P9 :: P16 :: P26 ::nil )= 3 /\ rk ( P9 :: P17 :: P21 ::nil )= 3 /\ rk ( P9 :: P17 :: P27 ::nil )= 3 /\ rk ( P9 :: P18 :: P24 ::nil )= 3 /\ rk ( P9 :: P20 :: P26 ::nil )= 3 /\ rk ( P9 :: P21 :: P27 ::nil )= 3 /\ rk ( P9 :: P22 :: P23 ::nil )= 3 /\ rk ( P9 :: P22 :: P25 ::nil )= 3 /\ rk ( P9 :: P22 :: P30 ::nil )= 3 /\ rk ( P9 :: P23 :: P25 ::nil )= 3 /\ rk ( P9 :: P23 :: P30 ::nil )= 3 /\ rk ( P9 :: P25 :: P30 ::nil )= 3 /\ rk ( P9 :: P28 :: P29 ::nil )= 3 /\ rk ( P10 :: P11 :: P13 ::nil )= 3 /\ rk ( P10 :: P11 :: P18 ::nil )= 3 /\ rk ( P10 :: P11 :: P22 ::nil )= 3 /\ rk ( P10 :: P11 :: P28 ::nil )= 3 /\ rk ( P10 :: P12 :: P17 ::nil )= 3 /\ rk ( P10 :: P12 :: P21 ::nil )= 3 /\ rk ( P10 :: P12 :: P27 ::nil )= 3 /\ rk ( P10 :: P13 :: P18 ::nil )= 3 /\ rk ( P10 :: P13 :: P22 ::nil )= 3 /\ rk ( P10 :: P13 :: P28 ::nil )= 3 /\ rk ( P10 :: P14 :: P20 ::nil )= 3 /\ rk ( P10 :: P15 :: P19 ::nil )= 3 /\ rk ( P10 :: P15 :: P25 ::nil )= 3 /\ rk ( P10 :: P16 :: P29 ::nil )= 3 /\ rk ( P10 :: P16 :: P30 ::nil )= 3 /\ rk ( P10 :: P17 :: P21 ::nil )= 3 /\ rk ( P10 :: P17 :: P27 ::nil )= 3 /\ rk ( P10 :: P18 :: P22 ::nil )= 3 /\ rk ( P10 :: P18 :: P28 ::nil )= 3 /\ rk ( P10 :: P19 :: P25 ::nil )= 3 /\ rk ( P10 :: P21 :: P27 ::nil )= 3 /\ rk ( P10 :: P22 :: P28 ::nil )= 3 /\ rk ( P10 :: P23 :: P24 ::nil )= 3 /\ rk ( P10 :: P23 :: P26 ::nil )= 3 /\ rk ( P10 :: P24 :: P26 ::nil )= 3 /\ rk ( P10 :: P29 :: P30 ::nil )= 3 /\ rk ( P11 :: P12 :: P14 ::nil )= 3 /\ rk ( P11 :: P12 :: P19 ::nil )= 3 /\ rk ( P11 :: P12 :: P23 ::nil )= 3 /\ rk ( P11 :: P12 :: P29 ::nil )= 3 /\ rk ( P11 :: P13 :: P18 ::nil )= 3 /\ rk ( P11 :: P13 :: P22 ::nil )= 3 /\ rk ( P11 :: P13 :: P28 ::nil )= 3 /\ rk ( P11 :: P14 :: P19 ::nil )= 3 /\ rk ( P11 :: P14 :: P23 ::nil )= 3 /\ rk ( P11 :: P14 :: P29 ::nil )= 3 /\ rk ( P11 :: P15 :: P21 ::nil )= 3 /\ rk ( P11 :: P16 :: P20 ::nil )= 3 /\ rk ( P11 :: P16 :: P26 ::nil )= 3 /\ rk ( P11 :: P17 :: P30 ::nil )= 3 /\ rk ( P11 :: P18 :: P22 ::nil )= 3 /\ rk ( P11 :: P18 :: P28 ::nil )= 3 /\ rk ( P11 :: P19 :: P23 ::nil )= 3 /\ rk ( P11 :: P19 :: P29 ::nil )= 3 /\ rk ( P11 :: P20 :: P26 ::nil )= 3 /\ rk ( P11 :: P22 :: P28 ::nil )= 3 /\ rk ( P11 :: P23 :: P29 ::nil )= 3 /\ rk ( P11 :: P24 :: P25 ::nil )= 3 /\ rk ( P11 :: P24 :: P27 ::nil )= 3 /\ rk ( P11 :: P25 :: P27 ::nil )= 3 /\ rk ( P12 :: P13 :: P15 ::nil )= 3 /\ rk ( P12 :: P13 :: P20 ::nil )= 3 /\ rk ( P12 :: P13 :: P24 ::nil )= 3 /\ rk ( P12 :: P13 :: P30 ::nil )= 3 /\ rk ( P12 :: P14 :: P19 ::nil )= 3 /\ rk ( P12 :: P14 :: P23 ::nil )= 3 /\ rk ( P12 :: P14 :: P29 ::nil )= 3 /\ rk ( P12 :: P15 :: P20 ::nil )= 3 /\ rk ( P12 :: P15 :: P24 ::nil )= 3 /\ rk ( P12 :: P15 :: P30 ::nil )= 3 /\ rk ( P12 :: P16 :: P22 ::nil )= 3 /\ rk ( P12 :: P17 :: P21 ::nil )= 3 /\ rk ( P12 :: P17 :: P27 ::nil )= 3 /\ rk ( P12 :: P19 :: P23 ::nil )= 3 /\ rk ( P12 :: P19 :: P29 ::nil )= 3 /\ rk ( P12 :: P20 :: P24 ::nil )= 3 /\ rk ( P12 :: P20 :: P30 ::nil )= 3 /\ rk ( P12 :: P21 :: P27 ::nil )= 3 /\ rk ( P12 :: P23 :: P29 ::nil )= 3 /\ rk ( P12 :: P24 :: P30 ::nil )= 3 /\ rk ( P12 :: P25 :: P26 ::nil )= 3 /\ rk ( P12 :: P25 :: P28 ::nil )= 3 /\ rk ( P12 :: P26 :: P28 ::nil )= 3 /\ rk ( P13 :: P14 :: P16 ::nil )= 3 /\ rk ( P13 :: P14 :: P21 ::nil )= 3 /\ rk ( P13 :: P14 :: P25 ::nil )= 3 /\ rk ( P13 :: P15 :: P20 ::nil )= 3 /\ rk ( P13 :: P15 :: P24 ::nil )= 3 /\ rk ( P13 :: P15 :: P30 ::nil )= 3 /\ rk ( P13 :: P16 :: P21 ::nil )= 3 /\ rk ( P13 :: P16 :: P25 ::nil )= 3 /\ rk ( P13 :: P17 :: P23 ::nil )= 3 /\ rk ( P13 :: P18 :: P22 ::nil )= 3 /\ rk ( P13 :: P18 :: P28 ::nil )= 3 /\ rk ( P13 :: P20 :: P24 ::nil )= 3 /\ rk ( P13 :: P20 :: P30 ::nil )= 3 /\ rk ( P13 :: P21 :: P25 ::nil )= 3 /\ rk ( P13 :: P22 :: P28 ::nil )= 3 /\ rk ( P13 :: P24 :: P30 ::nil )= 3 /\ rk ( P13 :: P26 :: P27 ::nil )= 3 /\ rk ( P13 :: P26 :: P29 ::nil )= 3 /\ rk ( P13 :: P27 :: P29 ::nil )= 3 /\ rk ( P14 :: P15 :: P17 ::nil )= 3 /\ rk ( P14 :: P15 :: P22 ::nil )= 3 /\ rk ( P14 :: P15 :: P26 ::nil )= 3 /\ rk ( P14 :: P16 :: P21 ::nil )= 3 /\ rk ( P14 :: P16 :: P25 ::nil )= 3 /\ rk ( P14 :: P17 :: P22 ::nil )= 3 /\ rk ( P14 :: P17 :: P26 ::nil )= 3 /\ rk ( P14 :: P18 :: P24 ::nil )= 3 /\ rk ( P14 :: P19 :: P23 ::nil )= 3 /\ rk ( P14 :: P19 :: P29 ::nil )= 3 /\ rk ( P14 :: P21 :: P25 ::nil )= 3 /\ rk ( P14 :: P22 :: P26 ::nil )= 3 /\ rk ( P14 :: P23 :: P29 ::nil )= 3 /\ rk ( P14 :: P27 :: P28 ::nil )= 3 /\ rk ( P14 :: P27 :: P30 ::nil )= 3 /\ rk ( P14 :: P28 :: P30 ::nil )= 3 /\ rk ( P15 :: P16 :: P18 ::nil )= 3 /\ rk ( P15 :: P16 :: P23 ::nil )= 3 /\ rk ( P15 :: P16 :: P27 ::nil )= 3 /\ rk ( P15 :: P17 :: P22 ::nil )= 3 /\ rk ( P15 :: P17 :: P26 ::nil )= 3 /\ rk ( P15 :: P18 :: P23 ::nil )= 3 /\ rk ( P15 :: P18 :: P27 ::nil )= 3 /\ rk ( P15 :: P19 :: P25 ::nil )= 3 /\ rk ( P15 :: P20 :: P24 ::nil )= 3 /\ rk ( P15 :: P20 :: P30 ::nil )= 3 /\ rk ( P15 :: P22 :: P26 ::nil )= 3 /\ rk ( P15 :: P23 :: P27 ::nil )= 3 /\ rk ( P15 :: P24 :: P30 ::nil )= 3 /\ rk ( P15 :: P28 :: P29 ::nil )= 3 /\ rk ( P16 :: P17 :: P19 ::nil )= 3 /\ rk ( P16 :: P17 :: P24 ::nil )= 3 /\ rk ( P16 :: P17 :: P28 ::nil )= 3 /\ rk ( P16 :: P18 :: P23 ::nil )= 3 /\ rk ( P16 :: P18 :: P27 ::nil )= 3 /\ rk ( P16 :: P19 :: P24 ::nil )= 3 /\ rk ( P16 :: P19 :: P28 ::nil )= 3 /\ rk ( P16 :: P20 :: P26 ::nil )= 3 /\ rk ( P16 :: P21 :: P25 ::nil )= 3 /\ rk ( P16 :: P23 :: P27 ::nil )= 3 /\ rk ( P16 :: P24 :: P28 ::nil )= 3 /\ rk ( P16 :: P29 :: P30 ::nil )= 3 /\ rk ( P17 :: P18 :: P20 ::nil )= 3 /\ rk ( P17 :: P18 :: P25 ::nil )= 3 /\ rk ( P17 :: P18 :: P29 ::nil )= 3 /\ rk ( P17 :: P19 :: P24 ::nil )= 3 /\ rk ( P17 :: P19 :: P28 ::nil )= 3 /\ rk ( P17 :: P20 :: P25 ::nil )= 3 /\ rk ( P17 :: P20 :: P29 ::nil )= 3 /\ rk ( P17 :: P21 :: P27 ::nil )= 3 /\ rk ( P17 :: P22 :: P26 ::nil )= 3 /\ rk ( P17 :: P24 :: P28 ::nil )= 3 /\ rk ( P17 :: P25 :: P29 ::nil )= 3 /\ rk ( P18 :: P19 :: P21 ::nil )= 3 /\ rk ( P18 :: P19 :: P26 ::nil )= 3 /\ rk ( P18 :: P19 :: P30 ::nil )= 3 /\ rk ( P18 :: P20 :: P25 ::nil )= 3 /\ rk ( P18 :: P20 :: P29 ::nil )= 3 /\ rk ( P18 :: P21 :: P26 ::nil )= 3 /\ rk ( P18 :: P21 :: P30 ::nil )= 3 /\ rk ( P18 :: P22 :: P28 ::nil )= 3 /\ rk ( P18 :: P23 :: P27 ::nil )= 3 /\ rk ( P18 :: P25 :: P29 ::nil )= 3 /\ rk ( P18 :: P26 :: P30 ::nil )= 3 /\ rk ( P19 :: P20 :: P22 ::nil )= 3 /\ rk ( P19 :: P20 :: P27 ::nil )= 3 /\ rk ( P19 :: P21 :: P26 ::nil )= 3 /\ rk ( P19 :: P21 :: P30 ::nil )= 3 /\ rk ( P19 :: P22 :: P27 ::nil )= 3 /\ rk ( P19 :: P23 :: P29 ::nil )= 3 /\ rk ( P19 :: P24 :: P28 ::nil )= 3 /\ rk ( P19 :: P26 :: P30 ::nil )= 3 /\ rk ( P20 :: P21 :: P23 ::nil )= 3 /\ rk ( P20 :: P21 :: P28 ::nil )= 3 /\ rk ( P20 :: P22 :: P27 ::nil )= 3 /\ rk ( P20 :: P23 :: P28 ::nil )= 3 /\ rk ( P20 :: P24 :: P30 ::nil )= 3 /\ rk ( P20 :: P25 :: P29 ::nil )= 3 /\ rk ( P21 :: P22 :: P24 ::nil )= 3 /\ rk ( P21 :: P22 :: P29 ::nil )= 3 /\ rk ( P21 :: P23 :: P28 ::nil )= 3 /\ rk ( P21 :: P24 :: P29 ::nil )= 3 /\ rk ( P21 :: P26 :: P30 ::nil )= 3 /\ rk ( P22 :: P23 :: P25 ::nil )= 3 /\ rk ( P22 :: P23 :: P30 ::nil )= 3 /\ rk ( P22 :: P24 :: P29 ::nil )= 3 /\ rk ( P22 :: P25 :: P30 ::nil )= 3 /\ rk ( P23 :: P24 :: P26 ::nil )= 3 /\ rk ( P23 :: P25 :: P30 ::nil )= 3 /\ rk ( P24 :: P25 :: P27 ::nil )= 3 /\ rk ( P25 :: P26 :: P28 ::nil )= 3 /\ rk ( P26 :: P27 :: P29 ::nil )= 3 /\ rk ( P27 :: P28 :: P30 ::nil )= 3.

Parameter is_only_31_pts : forall P,
{P=P0}+{P=P1}+{P=P2}+{P=P3}+{P=P4}+{P=P5}+{P=P6}+{P=P7}+{P=P8}+{P=P9}+{P=P10}+{P=P11}+{P=P12}+{P=P13}+{P=P14}+{P=P15}+{P=P16}+{P=P17}+{P=P18}+{P=P19}+{P=P20}+{P=P21}+{P=P22}+{P=P23}+{P=P24}+{P=P25}+{P=P26}+{P=P27}+{P=P28}+{P=P29}+{P=P30}.

 Ltac case_clear_2 P :=
let HP0:=fresh in let HP1:=fresh in let HP2:=fresh in let HP3:=fresh in let HP4:=fresh in let HP5:=fresh in let HP6:=fresh in let HP7:=fresh in let HP8:=fresh in let HP9:=fresh in let HP10:=fresh in let HP11:=fresh in let HP12:=fresh in let HP13:=fresh in let HP14:=fresh in let HP15:=fresh in let HP16:=fresh in let HP17:=fresh in let HP18:=fresh in let HP19:=fresh in let HP20:=fresh in let HP21:=fresh in let HP22:=fresh in let HP23:=fresh in let HP24:=fresh in let HP25:=fresh in let HP26:=fresh in let HP27:=fresh in let HP28:=fresh in let HP29:=fresh in let HP30:=fresh in destruct  (is_only_31_pts P) as 
[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[P0 | HP1 ]| HP2 ]| HP3 ]| HP4 ]| HP5 ]| HP6 ]| HP7 ]| HP8 ]| HP9 ]| HP10 ]| HP11 ]| HP12 ]| HP13 ]| HP14 ]| HP15 ]| HP16 ]| HP17 ]| HP18 ]| HP19 ]| HP20 ]| HP21 ]| HP22 ]| HP23 ]| HP24 ]| HP25 ]| HP26 ]| HP27 ]| HP28 ]| HP29 ]| HP30 ]; subst P.

Parameter P2nat : Point -> nat.
Parameter P2nat_0 : P2nat P0 = 0.
Parameter P2nat_1 : P2nat P1 = 1.
Parameter P2nat_2 : P2nat P2 = 2.
Parameter P2nat_3 : P2nat P3 = 3.
Parameter P2nat_4 : P2nat P4 = 4.
Parameter P2nat_5 : P2nat P5 = 5.
Parameter P2nat_6 : P2nat P6 = 6.
Parameter P2nat_7 : P2nat P7 = 7.
Parameter P2nat_8 : P2nat P8 = 8.
Parameter P2nat_9 : P2nat P9 = 9.
Parameter P2nat_10 : P2nat P10 = 10.
Parameter P2nat_11 : P2nat P11 = 11.
Parameter P2nat_12 : P2nat P12 = 12.
Parameter P2nat_13 : P2nat P13 = 13.
Parameter P2nat_14 : P2nat P14 = 14.
Parameter P2nat_15 : P2nat P15 = 15.
Parameter P2nat_16 : P2nat P16 = 16.
Parameter P2nat_17 : P2nat P17 = 17.
Parameter P2nat_18 : P2nat P18 = 18.
Parameter P2nat_19 : P2nat P19 = 19.
Parameter P2nat_20 : P2nat P20 = 20.
Parameter P2nat_21 : P2nat P21 = 21.
Parameter P2nat_22 : P2nat P22 = 22.
Parameter P2nat_23 : P2nat P23 = 23.
Parameter P2nat_24 : P2nat P24 = 24.
Parameter P2nat_25 : P2nat P25 = 25.
Parameter P2nat_26 : P2nat P26 = 26.
Parameter P2nat_27 : P2nat P27 = 27.
Parameter P2nat_28 : P2nat P28 = 28.
Parameter P2nat_29 : P2nat P29 = 29.
Parameter P2nat_30 : P2nat P30 = 30.
Definition leP (x y: Point) : bool := leb (P2nat x) (P2nat y).

Hint Rewrite -> P2nat_0 P2nat_1 P2nat_2 P2nat_3 P2nat_4 P2nat_5 P2nat_6 P2nat_7 P2nat_8 P2nat_9 P2nat_10 P2nat_11 P2nat_12 P2nat_13 P2nat_14 P2nat_15 P2nat_16 P2nat_17 P2nat_18 P2nat_19 P2nat_20 P2nat_21 P2nat_22 P2nat_23 P2nat_24 P2nat_25 P2nat_26 P2nat_27 P2nat_28 P2nat_29 P2nat_30 : order.


Lemma leP_total : forall A B, leP A B || leP B A.
Proof.
intros A B; unfold leP; apply Bool.orb_true_iff;
destruct (le_ge_dec (P2nat A) (P2nat B));
  [left; apply leb_correct; assumption |
right; apply leb_correct; unfold ge in *; assumption].
Qed.


Ltac solve_ex_p tac := first [
 tac P0 |  tac P1 |  tac P2 |  tac P3 |  tac P4 |  tac P5 |  tac P6 |  tac P7 |  tac P8 |  tac P9 |  tac P10 |  tac P11 |  tac P12 |  tac P13 |  tac P14 |  tac P15 |  tac P16 |  tac P17 |  tac P18 |  tac P19 |  tac P20 |  tac P21 |  tac P22 |  tac P23 |  tac P24 |  tac P25 |  tac P26 |  tac P27 |  tac P28 |  tac P29 |  tac P30 ].

(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.06.0/bin/coqtop" *)
(* coq-load-path: (("/Users/magaud/containers/theories" "Containers") ("/Users/magaud/galapagos/dev/trunk/ProjectiveGeometry/Dev" "ProjectiveGeometry.Dev")) *)
(* suffixes: .v *)
(* End: *)

(** rk-singleton : The rank of a point is always greater than one  **) 
Lemma rk_singleton_ge : forall P, rk (P :: nil) >= 1.
Proof.
intros.
assert(HH := rk_points);use HH.
case_clear_2 P ;solve [intuition].
Qed.

Lemma rk_singleton_1 : forall A, rk(A :: nil) <= 1.
Proof.
intros.
apply matroid1_b_useful.
solve [intuition].
Qed.

Lemma rk_couple_ge_alt : forall P Q, rk(P :: Q :: nil) = 2 -> rk(P :: Q :: nil) >=2.
Proof.
intuition.
Qed.

(** rk-couple : The rank of a two distinct points is always greater than one  **) 
Lemma rk_couple_ge : forall P Q, ~ P = Q -> rk(P :: Q :: nil) >= 2.
Proof.
intros.
assert(HH := rk_distinct_points);use HH.
apply rk_couple_ge_alt.
case_clear_2 P;case_clear_2 Q;solve [equal_degens | assumption | rewrite couple_equal;assumption].
Qed.

Lemma rk_couple_2 : forall P Q, rk(P :: Q :: nil) <= 2.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma rk_couple : forall P Q : Point,~ P = Q -> rk(P :: Q :: nil) = 2.
Proof.
intros.
assert(HH := rk_couple_2 P Q).
assert(HH0 := rk_couple_ge P Q H).
omega.
Qed.

Lemma couple_rk1 : forall P Q, rk(P :: Q :: nil) = 2 -> ~ P = Q.
Proof.
intros.
intro.
rewrite H0 in H.
assert(HH : equivlist (Q :: Q :: nil) (Q :: nil));[my_inO|].
rewrite HH in H.
assert(HH0 := rk_singleton_1 Q).
omega.
Qed.

Lemma triple_rk2_1 : forall P R, rk(P :: R :: nil) = 2 -> rk(P :: P :: R :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (P :: P :: R :: nil) (P :: R :: nil));[my_inO|];rewrite HH;intuition.
Qed.

Lemma triple_rk2_2 : forall P R, rk(P :: R :: nil) = 2 -> rk(P :: R :: P :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (P :: R :: P :: nil) (P :: R :: nil));[my_inO|];rewrite HH;intuition.
Qed.

Lemma triple_rk2_3 : forall P R, rk(P :: R :: nil) = 2 -> rk(R :: P :: P :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (R :: P :: P :: nil) (P :: R :: nil));[my_inO|];rewrite HH;intuition.
Qed.

Ltac rk_couple_triple_bis_bis :=
  match goal with
  
| H : rk(?A :: ?B :: nil) = 2 |- rk(?A :: ?B :: nil) = 2 => assumption
| H : rk(?B :: ?A :: nil) = 2 |- rk(?A :: ?B :: nil) = 2 => rewrite couple_equal in H;assumption                          

| H : rk(?A :: ?B :: ?C :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => assumption
| H : rk(?A :: ?C :: ?B :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_1 in H;assumption
| H : rk(?B :: ?A :: ?C :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_2 in H;assumption
| H : rk(?B :: ?C :: ?A :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_3 in H;assumption
| H : rk(?C :: ?A :: ?B :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_4 in H;assumption
| H : rk(?C :: ?B :: ?A :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_5 in H;assumption
end.
Ltac degens_rk2' :=
  solve[ first [apply triple_rk2_1 | apply triple_rk2_2 | apply triple_rk2_3];rk_couple_triple_bis_bis].

Ltac solve_ex_1 L t := solve [exists L; t ].

(*                           | exists L; repeat split;solve [ assumption |  degens_rk2' | rk_couple_triple_bis_bis ]].*)

Ltac solve_ex_p_1 t := first [
 solve_ex_1 P0 t |  solve_ex_1 P1 t|  solve_ex_1 P2 t|  solve_ex_1 P3 t|  solve_ex_1 P4 t|  solve_ex_1 P5 t|  solve_ex_1 P6 t|  solve_ex_1 P7 t|  solve_ex_1 P8 t|  solve_ex_1 P9 t|  solve_ex_1 P10 t|  solve_ex_1 P11 t|  solve_ex_1 P12 t|  solve_ex_1 P13 t|  solve_ex_1 P14 t|  solve_ex_1 P15 t|  solve_ex_1 P16 t|  solve_ex_1 P17 t|  solve_ex_1 P18 t|  solve_ex_1 P19 t |  solve_ex_1 P20 t|  solve_ex_1 P21 t|  solve_ex_1 P22 t|  solve_ex_1 P23 t|  solve_ex_1 P24 t|  solve_ex_1 P25 t|  solve_ex_1 P26 t|  solve_ex_1 P27 t|  solve_ex_1 P28 t|  solve_ex_1 P29 t|  solve_ex_1 P30 t].

Ltac my_inA :=
  intuition;unfold incl in *;unfold equivlist in *; simpl;
  repeat match goal with
  |[H : _ |- _] => progress intros
  |[H : _ |- _] => progress intro
  |[H : _ |- _] => progress intuition
  |[H : _ |- _] => split;intuition
  |[H : In _ (?P ::  _ ) |- _] => inversion H;clear H
  |[H : _ = _ |- _] => rewrite <-H
  |[H : In _ nil |- _] => inversion H
         end.

Lemma rk_13_12 : forall A B C U, rk(A::C::B::U)=rk(A::B::C::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.
Lemma rk_23_12 : forall A B C U, rk(C::A::B::U)=rk(A::B::C::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.
Lemma rk_sym12 : forall A B U, rk(A::B::U)=rk(B::A::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym13 : forall A B C U, rk(A::B::C::U)=rk(C::B::A::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym23 : forall A B C U, rk(A::B::C::U)=rk(A::C::B::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Ltac split3 := split; [ assumption | split; solve [assumption | rk_couple_triple_bis_bis ]].
Ltac solver := repeat split;solve [ assumption |  degens_rk2' | rk_couple_triple_bis_bis ].

Ltac my_rk_three_points_on_lines :=
  match goal with
| H : _ |- exists R, rk (?P :: ?P :: _ :: nil) = 2 /\ _ /\ _ => solve_ex_p_1 solver

| H : rk(?P::?Q::?T1::nil)= 2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   solve [ exists T1 ; split3 ]
         
| H : rk(?P::?T1::?Q::nil)= 2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_13_12 in H; solve [ exists T1 ; split3 ]

| H : rk(?T1::?P::?Q::nil)= 2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_23_12 in H; solve [ exists T1 ; split3 ]

| H : rk(?Q::?P::?T1::nil)= 2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_sym12 in H; solve [ exists T1 ; split3 ]
            
| H : rk(?Q::?T1::?P::nil)= 2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_sym13 in H; rewrite rk_13_12 in H; solve [ exists T1 ; split3 ]

| H : rk(?T1::?Q::?P::nil)= 2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_sym23 in H; rewrite rk_23_12 in H; solve [ exists T1 ; split3 ]
                             
end.

(** rk-three_point_on_lines : Each lines contains at least three points **)
Lemma rk_three_points_on_lines : forall P Q, exists R, 
rk (P :: Q :: R :: nil) = 2 /\ rk (Q :: R :: nil) = 2 /\ rk (P :: R :: nil) = 2.
Proof.
  Admitted.
(*intros.
assert(HH := rk_distinct_points);assert(HH0 := rk_lines');use HH;use HH0.
time (case_clear_2 P;case_clear_2 Q ; my_rk_three_points_on_lines).
Time Qed.*)

(* proofs are completed up to here *)

Ltac rk_inter_simplify (*P Q R S*) X X' Y Y' :=
match goal with
| H : _ |- exists J, rk (_ :: Y :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => solve_ex_1 Y
| H : _ |- exists J, rk (Y :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => solve_ex_1 Y
| H : _ |- exists J, rk (_ :: Y' :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => solve_ex_1 Y'
| H : _ |- exists J, rk (Y' :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 =>  solve_ex_1 Y'
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: X :: _ :: nil) = 2 => solve_ex_1 X
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (X :: _ :: _ :: nil) = 2 =>  solve_ex_1 X
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: X' :: _ :: nil) = 2 => solve_ex_1 X'
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (X' :: _ :: _ :: nil) = 2 => solve_ex_1 X'
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => solve [solve_ex_1 X | solve_ex_1 X']
end.

Ltac rk_inter_simplify_bis P Q R S X X' :=
match goal with
| H : rk(R :: S :: ?Y :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(R :: ?Y :: S :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(R :: ?Y :: ?Y' :: S :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(S :: R :: ?Y :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(S :: ?Y :: R :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(S :: ?Y :: ?Y' :: R :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: R :: S :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: R :: ?Y' :: S :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: S :: R :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: S :: ?Y' :: R :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: ?Y' :: R :: S :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: ?Y' :: S :: R :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
end.
Ltac solver2 := split;solve [ assumption |  degens_rk2' | rk_couple_triple_bis_bis ].

Ltac solve_all := solve_ex_p_1 solver2.


  
(*Ltac rk_inter_simplify_bis_bis_bis :=
match goal with
(*| H : _ |- exists J, rk (?P :: ?P :: _ :: nil) = 2 /\ rk (?P :: ?P :: _ :: nil) = 2 => solve_ex_p_1 *)
| H : _ |- exists J, rk (?P :: ?P :: _ :: nil) = 2 /\ rk (?Q :: ?Q :: _ :: nil) = 2 => solve_all

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?P :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?Q :: ?Q :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?Q :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?Q :: _ :: nil) = 2 /\ rk (?Q :: ?P :: _ :: nil) = 2 => solve_ex_1 P

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?R :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?R :: ?R :: _ :: nil) = 2 /\ rk (?P :: ?Q :: _ :: nil) = 2 => solve_ex_1 P

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?P :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?R :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?R :: ?P :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?P :: ?R :: _ :: nil) = 2 => solve_ex_1 P

(*| H : _ |- exists J, rk(?Q :: _ :: _ :: nil)= 2 /\ rk(?Q::_::_::nil)= 2 => solve_ex_1 Q
| H : _ |- exists J, rk(?Q :: _ :: _ :: nil)= 2 /\ rk(_::?Q::_::nil)= 2 => solve_ex_1 Q
| H : _ |- exists J, rk(?Q :: _ :: _ :: nil)= 2 /\ rk(_::_::?Q::nil)= 2 => solve_ex_1 Q
*)

| H : rk(?P :: ?Q :: ?X :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => solve_ex_1 X (*rk_inter_simplify_bis P Q R S X *)

| H : rk(?Q :: ?P :: ?X :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rewrite rk_sym12 in H; solve_ex_1 X (*rk_inter_simplify_bis P Q R S X *)

| H : rk(?P :: ?X :: ?Q :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => solve_ex_1 X (*rk_inter_simplify_bis P Q R S X *)
| H : rk(?Q :: ?P :: ?X :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => solve_ex_1 X(*rk_inter_simplify_bis P Q R S X *)
| H : rk(?Q :: ?X :: ?P :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => solve_ex_1 X(*rk_inter_simplify_bis P Q R S X*)

| H : rk(?X :: ?P :: ?Q  :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => solve_ex_1 X(*rk_inter_simplify_bis P Q R S X*)
| H : rk(?X :: ?Q :: ?P ::  nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => solve_ex_1 X(*rk_inter_simplify_bis P Q R S X*)
end.
*)
Lemma symL : forall A B C D, (exists J, rk (A::B::J::nil)= 2 /\ rk (C::D::J::nil)= 2) -> exists J, rk (B::A::J::nil)= 2/\rk(C::D::J::nil)= 2.
Proof.
  intros A B C D Hex; destruct Hex as [J [HJ1 HJ2]]; exists J; split; [rewrite <- HJ1 | rewrite <- HJ2]; apply rk_compat; split; my_inA.
Qed.

Lemma symR : forall A B C D, (exists J, rk (A::B::J::nil)= 2 /\ rk (C::D::J::nil)= 2) -> exists J, rk (A::B::J::nil)= 2/\rk(D::C::J::nil)= 2.
Proof.
  intros A B C D Hex; destruct Hex as [J [HJ1 HJ2]]; exists J; split; [rewrite <- HJ1 | rewrite <- HJ2]; apply rk_compat; split; my_inA.
Qed.

Lemma symLR : forall A B C D, (exists J, rk (A::B::J::nil)= 2 /\ rk (C::D::J::nil)= 2) -> exists J, rk (B::A::J::nil)= 2/\rk(D::C::J::nil)= 2.
Proof.
  intros A B C D Hex; destruct Hex as [J [HJ1 HJ2]]; exists J; split; [rewrite <- HJ1 | rewrite <- HJ2]; apply rk_compat; split; my_inA.
Qed.

(*Ltac rk_triple_bis A B C :=
match goal with
| H : rk(A :: B :: C :: nil) = _ |- _ => assumption
| H : rk(A :: C :: B :: nil) = _ |- _ => rewrite <-triple_equal_1 in H;assumption
| H : rk(B :: A :: C :: nil) = _ |- _ => rewrite <-triple_equal_2 in H;assumption
| H : rk(B :: C :: A :: nil) = _ |- _ => rewrite <-triple_equal_3 in H;assumption
| H : rk(C :: A :: B :: nil) = _ |- _ => rewrite <-triple_equal_4 in H;assumption
| H : rk(C :: B :: A :: nil) = _ |- _ => rewrite <-triple_equal_5 in H;assumption
end.
 *)

Ltac solve_T T := solve [exists T; split;
                                solve [
                                    assumption |
                                    (*rewrite triple_equal_1 ;assumption |
                                    rewrite triple_equal_2 ;assumption |
                                    rewrite triple_equal_3 ;assumption | 
                                    rewrite triple_equal_4 ;assumption |
                                    rewrite triple_equal_5 ;assumption |*)
                                    degens_rk2'(*|degens_rk2'*) | rk_couple_triple_bis_bis ]].

Lemma a1 : forall C E D,     rk(C::E::D::nil)= 2 -> rk(C::D::E::nil)= 2.
Proof.
Admitted.

Lemma a2 : forall C E D, rk(E::C::D::nil)= 2 -> rk(C::D::E::nil)= 2.
Proof.
Admitted.

Lemma a3 : forall A B T, rk(B::T::A::nil)= 2 -> rk(A::B::T::nil)= 2.
Proof.
Admitted.

Lemma sym12 : forall C E D, rk(E::C::D::nil)= 2 -> rk(C::E::D::nil)= 2.
Proof.
Admitted.

Ltac findhyps := match goal with
            
            | H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?P :: _ :: nil) = 2 => solve_T P
            | H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?Q :: ?Q :: _ :: nil) = 2 => solve_T P
            | H : _ |- exists J, rk (?Q :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?Q :: _ :: nil) = 2 => solve_T P
            | H : _ |- exists J, rk (?Q :: ?Q :: _ :: nil) = 2 /\ rk (?Q :: ?P :: _ :: nil) = 2 => solve_T P

            | H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?R :: _ :: nil) = 2 => solve_T P
            | H : _ |- exists J, rk (?R :: ?R :: _ :: nil) = 2 /\ rk (?P :: ?Q :: _ :: nil) = 2 => solve_T P
                     
            | H:rk(?A::?B::?T::nil)= 2, H':rk(?C::?D::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
                    
            | H:rk(?A::?B::?T::nil)= 2, H':rk(?C::_::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?A::?B::?T::nil)= 2, H':rk(_::?C::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?B::?A::?T::nil)= 2, H':rk(_::?C::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?B::?A::?T::nil)= 2, H':rk(?C::_::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?B::?A::?T::nil)= 2, H':rk(?C::?D::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
                    
            | H:rk(?T::?A::?B::nil)= 2, H':rk(?C::?D::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H:rk(?T::?A::?B::nil)= 2, H':rk(?C::?D::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?T::?A::?B::nil)= 2, H':rk(?C::_::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

                
            | H:rk(?T::?B::?A::nil)= 2, H':rk(_::?C::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?T::?B::?A::nil)= 2, H':rk(?C::?D::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?T::?B::?A::nil)= 2, H':rk(?C::_::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?A::?T::?B::nil)= 2, H':rk(?C::?D::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H:rk(?A::?T::?B::nil)= 2, H':rk(?C::_::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?A::?T::?B::nil)= 2, H':rk(_::?C::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?B::?T::?A::nil)= 2, H':rk(?C::?D::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H:rk(?B::?T::?A::nil)= 2, H':rk(?C::_::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H:rk(?B::?T::?A::nil)= 2, H':rk(_::?C::?D::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]


                    (**)
            | H:rk(?A::?B::?T::nil)= 2, H':rk(?D::?C::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
                    
            | H:rk(?A::?B::?T::nil)= 2, H':rk(?D::_::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?A::?B::?T::nil)= 2, H':rk(_::?D::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]              

            | H:rk(?B::?A::?T::nil)= 2, H':rk(_::?D::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?B::?A::?T::nil)= 2, H':rk(?D::_::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?B::?A::?T::nil)= 2, H':rk(?D::?C::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?T::?A::?B::nil)= 2, H':rk(_::?D::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?T::?A::?B::nil)= 2, H':rk(?D::?C::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]


            | H:rk(?T::?A::?B::nil)= 2, H':rk(?D::_::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

                
            | H:rk(?T::?B::?A::nil)= 2, H':rk(_::?D::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H:rk(?T::?B::?A::nil)= 2, H':rk(?D::?C::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?T::?B::?A::nil)= 2, H':rk(?D::_::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?A::?T::?B::nil)= 2, H':rk(?D::?C::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H:rk(?A::?T::?B::nil)= 2, H':rk(?D::_::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H:rk(?A::?T::?B::nil)= 2, H':rk(_::?D::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]

            | H:rk(?B::?T::?A::nil)= 2, H':rk(?D::?C::_::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H:rk(?B::?T::?A::nil)= 2, H':rk(?D::_::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H:rk(?B::?T::?A::nil)= 2, H':rk(_::?D::?C::nil)= 2 |- exists J : Point,
                rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
              solve [solve_T T | solve_T A | solve_T B | solve_T C | solve_T D]
            | H : _ |- exists J, rk (?P :: ?P :: _ :: nil) = 2 /\ rk (?Q :: ?Q :: _ :: nil) = 2 => solve_all
                 end.

Ltac perform A B :=
  match goal with
  |  H:rk(A::B::?T::nil)= 2 |- _ => solve_T T
  |  H:rk(A::?T::B::nil)= 2 |- _ => solve_T T
  |  H:rk(?T::A::B::nil)= 2 |- _ => solve_T T

  |  H:rk(B::A::?T::nil)= 2 |- _ => solve_T T
  |  H:rk(B::?T::A::nil)= 2 |- _ => solve_T T
  |  H:rk(?T::B::A::nil)= 2 |- _ => solve_T T
  end.

Ltac better_tac :=
  match goal with
  | H:_ |-
    exists J : Point, rk (?A :: ?B :: J :: nil) = 2 /\ rk (?C :: ?D :: J :: nil) = 2 =>
    solve [perform A B | solve_T A | solve_T B | solve_T C | solve_T D | perform C D | solve_all]
  end.

(** rk-inter : Two lines always intersect in the plane **)
Lemma rk_inter : forall P Q R S, exists J, rk (P :: Q :: J :: nil) = 2 /\ rk (R :: S :: J :: nil) = 2.
Proof.
intros A B C D; intros.

Require Import wlog.

wlog2 A B leP leP_total ltac:(firstorder rk_couple_triple_bis_bis) idtac.
wlog2 C D leP leP_total ltac:(firstorder rk_couple_triple_bis_bis) idtac.
assert(HH := rk_distinct_points);assert(HH0 := rk_lines');use HH;use HH0.
time (unfold leP; intros P Q HPQ; case_clear_2 P;case_clear_2 Q; autorewrite with order in HPQ; try discriminate).
(* 60 s and 496 goals instead on 961 *)
(*par:time (intros R S HRS; case_clear_2 R; case_clear_2 S; autorewrite with order in HRS; try solve [discriminate | better_tac]).*)
Time Qed.

(** rk-lower_dim : There exist three points which are not collinear **)
Lemma rk_lower_dim : exists P0 P1 P2, rk( P0 :: P1 :: P2 :: nil) >=3.
Proof.
intros.
assert(HH := rk_planes);use HH.
exists P0;exists P2;exists P7;intuition.
Qed.

End s_fanoPlaneModelRkPG25.

(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.06.0/bin/coqtop" *)
(* coq-load-path: (("/Users/magaud/containers/theories" "Containers") ("/Users/magaud/galapagos/dev/trunk/ProjectiveGeometry/Dev" "ProjectiveGeometry.Dev")) *)
(* suffixes: .v *)
(* End: *)


