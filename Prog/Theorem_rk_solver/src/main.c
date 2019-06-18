
#include "set.h"
#include "parties.h"

// 4 pts
//~ Lemma example0 : forall A B A' O : Point,
       //~ rk (triple A B O) = 3 ->
       //~ rk (triple A A' O) = 2 ->
       //~ rk (triple A A') = 2 ->
       //~ rk (couple A' O) = 2 ->
       //~ rk (triple A A' B) = 3.
graph example0 (graph g) {
	
	g.effectiveAllocPow = 4;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[10]->e = setMinMax(g.tab[10]->e,3,3); // 1 2 4
	g.tab[10]->color = -1;
	g.tab[12]->e = setMinMax(g.tab[12]->e,2,2); // 1 3 4
	g.tab[12]->color = -1;
	g.tab[4]->e = setMinMax(g.tab[4]->e,2,2); // 1 3
	g.tab[4]->color = -1;
	g.tab[11]->e = setMinMax(g.tab[11]->e,2,2); // 3 4
	g.tab[11]->color = -1;
	return g; // 1 2 3 = 3
}

// 3 pts
//~ Lemma rk_line_unification : forall A B C,
//~ rk(couple A B) = 2 -> rk(couple A C) = 2 -> 
//~ rk(couple B C) = 2 -> rk(triple A B C) <= 2 -> rk(triple A B C) = 2.
graph example01 (graph g) {
	
	g.effectiveAllocPow = 3;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[2]->e = setMinMax(g.tab[2]->e,2,2); // 1 2
	g.tab[2]->color = -1;
	g.tab[4]->e = setMinMax(g.tab[4]->e,2,2); // 1 3
	g.tab[4]->color = -1;
	g.tab[5]->e = setMinMax(g.tab[5]->e,2,2); // 2 3
	g.tab[5]->color = -1;
	g.tab[6]->e = setMax(g.tab[6]->e,2); // 1 2 3
	g.tab[6]->color = -1;
	return g; // 1 2 3 = 2
}

// 4 pts
//~ Lemma example02 : forall A B C D : Point,
       //~ rk (triple B C) = 2 ->
       //~ rk (triple A B C) = 2 ->
       //~ rk (triple B C D) = 2 ->
       //~ rk (triple A B C D) = 2.
graph example02 (graph g) {  
	g.effectiveAllocPow = 4;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[5]->e = setMinMax(g.tab[5]->e,2,2); // 2 3
	g.tab[5]->color = -1;
	g.tab[6]->e = setMinMax(g.tab[6]->e,2,2); // 2 3 4
	g.tab[6]->color = -1;
	g.tab[13]->e = setMinMax(g.tab[13]->e,2,2); // 2 3 4
	g.tab[13]->color = -1;
	return g; // 1 2 3 4 = 2 
}    

// 4 pts
//~ Lemma example01 : forall A B C D : Point,
       //~ rk (triple A B C) = 3 ->
       //~ rk (triple B C D) = 3 ->
       //~ rk (triple A B C D) = 4 ->
       //~ rk (triple B C) = 2.
graph example03 (graph g) {  
	g.effectiveAllocPow = 4;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[6]->e = setMinMax(g.tab[6]->e,3,3); // 1 2 3
	g.tab[6]->color = -1;
	g.tab[13]->e = setMinMax(g.tab[13]->e,3,3); // 2 3 4
	g.tab[13]->color = -1;
	g.tab[14]->e = setMinMax(g.tab[14]->e,4,4); // 1 2 3 4
	g.tab[14]->color = -1;
	return g; // 2 3 = 2 
}

// 5 pts - equal points
//~ Lemma rk_test_equal_pts : forall P1 P2 P3 P4,
                     //~ rk(P1 :: P2 :: P3 :: nil) = 3 ->
                     //~ rk(P3 :: P4 :: nil) = 1 ->
                     //~ rk(P1 :: P2 :: P4 :: nil) = 3.
graph example04 (graph g) {
	
	g.effectiveAllocPow = 4;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[6]->e = setMinMax(g.tab[6]->e,3,3); // 1 2 3
	g.tab[6]->color = -1;
	g.tab[11]->e = setMinMax(g.tab[11]->e,1,1); // 3 5
	g.tab[11]->color = -1;
	return g; // 1 2 4 = 3
}   

// 5 pts
//~ Lemma l1_scheme : forall A' B' : Point,
       //~ forall A B : Point,
       //~ forall O : Point,
       //~ rk (triple A B O) = 3 ->
       //~ rk (triple A A' O) = 2 ->
       //~ rk (triple B B' O) = 2 ->
       //~ rk (couple A' O) = 2 ->
       //~ rk (couple B' O) = 2  ->  rk (triple A' B' O) = 3.
graph example1 (graph g) {
	
	g.effectiveAllocPow = 5;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[18]->e = setMinMax(g.tab[18]->e,3,3); // 1 2 5
	g.tab[18]->color = -1;
	g.tab[20]->e = setMinMax(g.tab[20]->e,2,2); // 1 3 5
	g.tab[20]->color = -1;
	g.tab[25]->e = setMinMax(g.tab[25]->e,2,2); // 2 4 5
	g.tab[25]->color = -1;
	g.tab[19]->e = setMinMax(g.tab[19]->e,2,2); // 3 5
	g.tab[19]->color = -1;
	g.tab[23]->e = setMinMax(g.tab[23]->e,2,2); // 4 5
	g.tab[23]->color = -1;
	return g; // 3 4 5 = 3
}

// 5 pts
//~ Lemma rABOo_scheme : 
       //~ forall A B : Point,
       //~ forall O P : Point,
       //~ rk (add P (triple A B O)) >= 4 ->
       //~ forall o : Point,
       //~ rk (triple o O P) = 2 ->
       //~ rk (couple O o) = 2 -> rk (add o (triple A B O)) >= 4.
graph example2 (graph g) {
	
	g.effectiveAllocPow = 5;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[14]->e = setMinMax(g.tab[14]->e,4,4); // 1 2 3 4
	g.tab[14]->color = -1;
	g.tab[27]->e = setMinMax(g.tab[27]->e,2,2); // 3 4 5
	g.tab[27]->color = -1;
	g.tab[19]->e = setMinMax(g.tab[19]->e,2,2); // 3 5
	g.tab[19]->color = -1;
	return g; // 1 2 3 5 = 4
}


// 8 pts
//~ Lemma subl2rABMP_scheme
     //~ : forall A' B' C'distincts A B C O0 : Point,
       //~ rk (union (triple A B C) (union (triple A' B' C') (singleton O0))) = 3 ->
       //~ rk (triple A B O0) = 3 ->
       //~ forall M : Point,
       //~ M = C ((\/ M = A' \/ M = B' \/ M = C')) ->
       //~ rk (add M (triple A B O0)) = 3.
graph example5 (graph g) {
	
	g.effectiveAllocPow = 8;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[126]->e = setMinMax(g.tab[126]->e,3,3); // 1 2 3 4 5 6 7
	g.tab[126]->color = -1;
	g.tab[66]->e = setMinMax(g.tab[66]->e,3,3); // 1 2 7
	g.tab[66]->color = -1;
	g.tab[131]->e = setMinMax(g.tab[131]->e,1,1); // 3 8
	g.tab[131]->color = -1;
	return g; // 1 2 3 7 8 = 3
}

// 10 pts
 //~ forall A' B' C' A B C O : Point,
       //~ rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       //~ rk (couple C C') = 2 ->
       //~ forall P : Point,
       //~ rk (add P (triple A B O)) >= 4 ->
       //~ forall o : Point,
       //~ rk (triple o O P) = 2 ->
       //~ rk (couple O o) = 2 ->
       //~ forall c : Point,
       //~ rk (triple o C c) = 2 ->
       //~ rk (triple P C' c) = 2 -> rk (union (triple C C' o) (couple P c)) = 3.    
graph example6 (graph g) {
	
	g.effectiveAllocPow = 10;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[126]->e = setMinMax(g.tab[126]->e,3,3); // 1 2 3 4 5 6 7
	g.tab[126]->color = -1;
	
	g.tab[35]->e = setMinMax(g.tab[35]->e,2,2); // 3 6
	g.tab[35]->color = -1;
	
	g.tab[194]->e = setMinMax(g.tab[194]->e,4,4); // 1 2 7 8
	g.tab[194]->color = -1;
	
	g.tab[447]->e = setMinMax(g.tab[447]->e,2,2); // 7 8 9
	g.tab[447]->color = -1;
	
	g.tab[319]->e = setMinMax(g.tab[319]->e,2,2); // 7 9
	g.tab[319]->color = -1;
	
	g.tab[771]->e = setMinMax(g.tab[771]->e,2,2); // 3 9 10
	g.tab[771]->color = -1;
	
	g.tab[671]->e = setMinMax(g.tab[671]->e,2,2); // 6 8 10
	g.tab[671]->color = -1;
	
	return g; // 3 6 8 9 10 = 3
}

// Pasch colinearity
graph pasch_extended (graph g) {
	
	g.effectiveAllocPow = 7;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[2]->e = setMinMax(g.tab[2]->e,2,2); // 1 2
	g.tab[2]->color = -1;
	
	g.tab[4]->e = setMinMax(g.tab[4]->e,2,2); // 1 3
	g.tab[4]->color = -1;
	
	g.tab[8]->e = setMinMax(g.tab[8]->e,2,2); // 1 4
	g.tab[8]->color = -1;
	
	g.tab[5]->e = setMinMax(g.tab[5]->e,2,2); // 2 3
	g.tab[5]->color = -1;
	
	g.tab[9]->e = setMinMax(g.tab[9]->e,2,2); // 2 4
	g.tab[9]->color = -1;
	
	g.tab[11]->e = setMinMax(g.tab[11]->e,2,2); // 3 4
	g.tab[11]->color = -1;
	
	g.tab[6]->e = setMinMax(g.tab[14]->e,3,3); // 1 2 3
	g.tab[6]->color = -1;
	
	g.tab[10]->e = setMinMax(g.tab[14]->e,3,3); // 1 2 4
	g.tab[10]->color = -1;
	
	g.tab[12]->e = setMinMax(g.tab[14]->e,3,3); // 1 3 4
	g.tab[12]->color = -1;
	
	g.tab[13]->e = setMinMax(g.tab[14]->e,3,3); // 2 3 4
	g.tab[13]->color = -1;
	
	g.tab[18]->e = setMinMax(g.tab[18]->e,2,2); // 1 2 5
	g.tab[18]->color = -1;
	
	g.tab[27]->e = setMinMax(g.tab[27]->e,2,2); // 3 4 5
	g.tab[27]->color = -1;
	
	g.tab[36]->e = setMinMax(g.tab[36]->e,2,2); // 1 3 6
	g.tab[36]->color = -1;
	
	g.tab[41]->e = setMinMax(g.tab[41]->e,2,2); // 2 4 6
	g.tab[41]->color = -1;
	
	g.tab[72]->e = setMinMax(g.tab[72]->e,2,2); // 1 4 7
	g.tab[72]->color = -1;
	
	g.tab[69]->e = setMinMax(g.tab[69]->e,2,2); // 2 3 7
	g.tab[69]->color = -1;
	
	return g; // 5 6 7 = 3 ?
}
	
// Pappus configuration - 9 pts
graph pappus (graph g) {
	
	g.effectiveAllocPow = 9;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[2]->e = setMinMax(g.tab[2]->e,2,2);
	g.tab[2]->color = -1;
	g.tab[4]->e = setMinMax(g.tab[4]->e,2,2);
	g.tab[4]->color = -1;
	g.tab[5]->e = setMinMax(g.tab[5]->e,2,2);
	g.tab[5]->color = -1;
	g.tab[8]->e = setMinMax(g.tab[8]->e,2,2);
	g.tab[8]->color = -1;
	g.tab[9]->e = setMinMax(g.tab[9]->e,2,2);
	g.tab[9]->color = -1;
	g.tab[11]->e = setMinMax(g.tab[11]->e,2,2);
	g.tab[11]->color = -1;
	g.tab[16]->e = setMinMax(g.tab[16]->e,2,2);
	g.tab[16]->color = -1;
	g.tab[17]->e = setMinMax(g.tab[17]->e,2,2);
	g.tab[17]->color = -1;
	g.tab[19]->e = setMinMax(g.tab[19]->e,2,2);
	g.tab[19]->color = -1;
	g.tab[23]->e = setMinMax(g.tab[23]->e,2,2);
	g.tab[23]->color = -1;
	g.tab[32]->e = setMinMax(g.tab[32]->e,2,2);
	g.tab[32]->color = -1;
	g.tab[33]->e = setMinMax(g.tab[33]->e,2,2);
	g.tab[33]->color = -1;
	g.tab[35]->e = setMinMax(g.tab[35]->e,2,2);
	g.tab[35]->color = -1;
	g.tab[39]->e = setMinMax(g.tab[39]->e,2,2);
	g.tab[39]->color = -1;
	g.tab[47]->e = setMinMax(g.tab[47]->e,2,2);
	g.tab[47]->color = -1;
	g.tab[62]->e = setMinMax(g.tab[62]->e,3,3);
	g.tab[62]->color = -1;
	
	g.tab[6]->e = setMinMax(g.tab[6]->e,2,2);
	g.tab[6]->color = -1;
	g.tab[55]->e = setMinMax(g.tab[55]->e,2,2);
	g.tab[55]->color = -1;
	
	g.tab[80]->e = setMinMax(g.tab[80]->e,2,2);
	g.tab[80]->color = -1;
	g.tab[73]->e = setMinMax(g.tab[73]->e,2,2);
	g.tab[73]->color = -1;
	
	g.tab[160]->e = setMinMax(g.tab[160]->e,2,2);
	g.tab[160]->color = -1;
	g.tab[139]->e = setMinMax(g.tab[139]->e,2,2);
	g.tab[139]->color = -1;
	
	g.tab[289]->e = setMinMax(g.tab[289]->e,2,2);
	g.tab[289]->color = -1;
	g.tab[275]->e = setMinMax(g.tab[275]->e,2,2);
	g.tab[275]->color = -1;
	return g;
}

// Desargues 10 pts - 3D
graph desargues3D (graph g) {
	
	g.effectiveAllocPow = 10;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[8]->e = setMin(g.tab[8]->e,2); // 1 4
	g.tab[8]->e = setMax(g.tab[8]->e,2); // 1 4
	g.tab[8]->color = -1;
	
	g.tab[17]->e = setMin(g.tab[17]->e,2); // 2 5
	g.tab[17]->e = setMax(g.tab[17]->e,2); // 2 5
	g.tab[17]->color = -1;
	
	g.tab[35]->e = setMin(g.tab[35]->e,2); // 3 6
	g.tab[35]->e = setMax(g.tab[35]->e,2); // 3 6
	g.tab[35]->color = -1;
	
	g.tab[72]->e = setMin(g.tab[72]->e,2); // 1 4 7
	g.tab[72]->e = setMax(g.tab[72]->e,2); // 1 4 7
	g.tab[72]->color = -1;
	
	g.tab[81]->e = setMin(g.tab[81]->e,2); // 2 5 7
	g.tab[81]->e = setMax(g.tab[81]->e,2); // 2 5 7
	g.tab[81]->color = -1;
	
	g.tab[99]->e = setMin(g.tab[99]->e,2); // 3 6 7
	g.tab[99]->e = setMax(g.tab[99]->e,2); // 3 6 7
	g.tab[99]->color = -1;
	
	g.tab[6]->e = setMin(g.tab[6]->e,3); // 1 2 3
	g.tab[6]->e = setMax(g.tab[6]->e,3); // 1 2 3
	g.tab[6]->color = -1;
	
	g.tab[55]->e = setMin(g.tab[55]->e,3); // 4 5 6
	g.tab[55]->e = setMax(g.tab[55]->e,3); // 4 5 6
	g.tab[55]->color = -1;
		
	g.tab[14]->e = setMin(g.tab[14]->e,4); // 1 2 3 4
	g.tab[14]->e = setMax(g.tab[14]->e,4); // 1 2 3 4
	g.tab[14]->color = -1;
	
	// degenerate cases with two equal points
	//~ g.tab[62]->e = setMin(g.tab[62]->e,4); // 1 2 3 4 5 6
	//~ g.tab[62]->e = setMax(g.tab[62]->e,4); // 1 2 3 4 5 6
	
	g.tab[514]->e = setMin(g.tab[514]->e,2); // 1 2 10
	g.tab[514]->e = setMax(g.tab[514]->e,2); // 1 2 10
	g.tab[514]->color = -1;
	
	g.tab[535]->e = setMin(g.tab[535]->e,2); // 4 5 10
	g.tab[535]->e = setMax(g.tab[535]->e,2); // 4 5 10
	g.tab[535]->color = -1;
	
	g.tab[260]->e = setMin(g.tab[260]->e,2); // 1 3 9
	g.tab[260]->e = setMax(g.tab[260]->e,2); // 1 3 9
	g.tab[260]->color = -1;
	
	g.tab[295]->e = setMin(g.tab[295]->e,2); // 4 6 9
	g.tab[295]->e = setMax(g.tab[295]->e,2); // 4 6 9
	g.tab[295]->color = -1;
	
	g.tab[133]->e = setMin(g.tab[133]->e,2); // 2 3 8
	g.tab[133]->e = setMax(g.tab[133]->e,2); // 2 3 8
	g.tab[133]->color = -1;
	
	g.tab[175]->e = setMin(g.tab[175]->e,2); // 5 6 8
	g.tab[175]->e = setMax(g.tab[175]->e,2); // 5 6 8
	g.tab[175]->color = -1;

	return g; // 8 9 10 = 2
}

// // Desargues 15 pts - 2D
graph desargues2D (graph g) {
	
	g.effectiveAllocPow = 15;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	g.tab[72]->e = setMinMax(g.tab[72]->e,2,2); // 1 4 7
	g.tab[72]->color = -1;
	g.tab[81]->e = setMinMax(g.tab[81]->e,2,2); // 2 5 7
	g.tab[81]->color = -1;
	g.tab[99]->e = setMinMax(g.tab[99]->e,2,2); // 3 6 7
	g.tab[99]->color = -1;
	
	g.tab[8]->e = setMinMax(g.tab[8]->e,2,2); // 1 4
	g.tab[8]->color = -1;
	g.tab[17]->e = setMinMax(g.tab[17]->e,2,2); // 2 5
	g.tab[17]->color = -1;
	g.tab[35]->e = setMinMax(g.tab[35]->e,2,2); // 3 6
	g.tab[35]->color = -1;
	
	g.tab[71]->e = setMinMax(g.tab[71]->e,2,2); // 4 7
	g.tab[71]->color = -1;
	g.tab[79]->e = setMinMax(g.tab[79]->e,2,2); // 5 7
	g.tab[79]->color = -1;
	g.tab[95]->e = setMinMax(g.tab[95]->e,2,2); // 6 7
	g.tab[95]->color = -1;
			
	g.tab[6]->e = setMinMax(g.tab[6]->e,3,3); // 1 2 3
	g.tab[6]->color = -1;
	g.tab[55]->e = setMinMax(g.tab[55]->e,3,3); // 4 5 6
	g.tab[55]->color = -1;
	g.tab[126]->e = setMinMax(g.tab[126]->e,3,3); // 1 2 3 4 5 6 7
	g.tab[126]->color = -1;
	
	g.tab[1030]->e = setMinMax(g.tab[1030]->e,4,4); // 1 2 3 11 = 4
	g.tab[1030]->color = -1;
	g.tab[2054]->e = setMinMax(g.tab[2054]->e,4,4); // 1 2 3 12 = 4
	g.tab[2054]->color = -1;
	g.tab[3071]->e = setMinMax(g.tab[3071]->e,2,2); // 11 12 = 2
	g.tab[3071]->color = -1;
	g.tab[3135]->e = setMinMax(g.tab[3135]->e,2,2); // 7 11 12 = 2
	g.tab[3135]->color = -1;

	g.tab[2176]->e = setMinMax(g.tab[2176]->e,2,2); // 1 8 12 = 2
	g.tab[2176]->color = -1;
	g.tab[2305]->e = setMinMax(g.tab[2305]->e,2,2); // 2 9 12 = 2
	g.tab[2305]->color = -1;
	g.tab[2563]->e = setMinMax(g.tab[2563]->e,2,2); // 3 10 12 = 2
	g.tab[2563]->color = -1;
	
	g.tab[1159]->e = setMinMax(g.tab[1159]->e,2,2); // 4 8 11 = 2
	g.tab[1159]->color = -1;
	g.tab[1295]->e = setMinMax(g.tab[1295]->e,2,2); // 5 9 11 = 2
	g.tab[1295]->color = -1;
	g.tab[1567]->e = setMinMax(g.tab[1567]->e,2,2); // 6 10 11 = 2
	g.tab[1567]->color = -1;
	
	g.tab[8831]->e = setMinMax(g.tab[8831]->e,2,2); // 8 10 14 = 2
	g.tab[8831]->color = -1;
	g.tab[8231]->e = setMinMax(g.tab[8231]->e,2,2); // 4 6 14 = 2
	g.tab[8231]->color = -1;
	
	g.tab[4863]->e = setMinMax(g.tab[4863]->e,2,2); // 9 10 13 = 2
	g.tab[4863]->color = -1;
	g.tab[4143]->e = setMinMax(g.tab[4143]->e,2,2); // 5 6 13 = 2
	g.tab[4143]->color = -1;
	
	g.tab[16767]->e = setMinMax(g.tab[16767]->e,2,2); // 8 9 15 = 2
	g.tab[16767]->color = -1;
	g.tab[16407]->e = setMinMax(g.tab[16407]->e,2,2); // 4 5 15 = 2
	g.tab[16407]->color = -1;
	
	return g; // 13 14 15 = 2
}

// Harmonic Conjugate 14 pts
graph harmonic (graph g) {
	
	g.effectiveAllocPow = 14;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	// Line A B C
	g.tab[6]->e = setMinMax(g.tab[6]->e,2,2); // 1 2 3
	g.tab[6]->color = -1;
	
	// ~ A B
	g.tab[2]->e = setMinMax(g.tab[2]->e,2,2); // 1 2
	g.tab[2]->color = -1;
	
	// ~ A C
	g.tab[4]->e = setMinMax(g.tab[4]->e,2,2); // 1 3
	g.tab[4]->color = -1;
	
	// ~ B C
	g.tab[5]->e = setMinMax(g.tab[5]->e,2,2); // 2 3
	g.tab[5]->color = -1;
	
	// Plane P Q R
	g.tab[55]->e = setMinMax(g.tab[55]->e,3,3); // 4 5 6
	g.tab[55]->color = -1;
	
	// Plane P' Q' R'
	g.tab[895]->e = setMinMax(g.tab[895]->e,3,3); // 8 9 10
	g.tab[895]->color = -1;
	
	// two distinct planes 1 2 4 8
	g.tab[138]->e = setMinMax(g.tab[138]->e,4,4); // 1 2 4 8
	g.tab[138]->color = -1;
	
	// Plane A B R
	g.tab[10]->e = setMinMax(g.tab[10]->e,3,3); // 1 2 4
	g.tab[10]->color = -1;
	
	// Plane A B Q
	g.tab[18]->e = setMinMax(g.tab[18]->e,3,3); // 1 2 5
	g.tab[18]->color = -1;
	
	// Line A Q R
	g.tab[24]->e = setMinMax(g.tab[24]->e,2,2); // 1 4 5
	g.tab[24]->color = -1;
	
	// Line B P R
	g.tab[41]->e = setMinMax(g.tab[41]->e,2,2); // 2 4 6
	g.tab[41]->color = -1;
			
	// Line C P Q
	g.tab[51]->e = setMinMax(g.tab[51]->e,2,2); // 3 5 6
	g.tab[51]->color = -1;
	
	// Line A P U 
	g.tab[96]->e = setMinMax(g.tab[96]->e,2,2); // 1 6 7
	g.tab[96]->color = -1;
	
	// Line B Q U
	g.tab[81]->e = setMinMax(g.tab[81]->e,2,2); // 2 5 7
	g.tab[81]->color = -1;
	
	// Line D R U
	g.tab[2119]->e = setMinMax(g.tab[2119]->e,2,2); // 4 7 12
	g.tab[2119]->color = -1;
	
	// Plane A B R'
	g.tab[130]->e = setMinMax(g.tab[130]->e,3,3); // 1 2 8
	g.tab[130]->color = -1;
	
	// Plane A B Q'
	g.tab[258]->e = setMinMax(g.tab[258]->e,3,3); // 1 2 9
	g.tab[258]->color = -1;
	
	// Line A Q' R'
	g.tab[384]->e = setMinMax(g.tab[384]->e,2,2); // 1 8 9
	g.tab[384]->color = -1;
	
	// Line B P' R'
	g.tab[641]->e = setMinMax(g.tab[641]->e,2,2); // 2 8 10
	g.tab[641]->color = -1;
			
	// Line C P' Q'
	g.tab[771]->e = setMinMax(g.tab[771]->e,2,2); // 3 9 10
	g.tab[771]->color = -1;
	
	// Line A P' U' 
	g.tab[1536]->e = setMinMax(g.tab[1536]->e,2,2); // 1 10 11
	g.tab[1536]->color = -1;
	
	// Line B Q' U'
	g.tab[1281]->e = setMinMax(g.tab[1281]->e,2,2); // 2 9 11
	g.tab[1281]->color = -1;
	
	// Line D' R' U'
	g.tab[5247]->e = setMinMax(g.tab[5247]->e,2,2); // 8 11 13
	g.tab[5247]->color = -1;
	
	// Line A B C D D'
	g.tab[6150]->e = setMinMax(g.tab[6150]->e,2,2); // 1 2 3 12 13
	g.tab[6150]->color = -1;
	
	// Line P P' O
	g.tab[8735]->e = setMinMax(g.tab[8735]->e,2,2); // 6 10 14
	g.tab[8735]->color = -1;
	
	// Line Q Q' O
	g.tab[8463]->e = setMinMax(g.tab[8463]->e,2,2); // 5 9 14
	g.tab[8463]->color = -1;
	
	return g; // 12 13 = 1
}

// Harmonic Conjugate 14 pts
graph harmonic_part1 (graph g) {
	
	g.effectiveAllocPow = 11;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	// Line A B C
	g.tab[6]->e = setMinMax(g.tab[6]->e,2,2); // 1 2 3
	g.tab[6]->color = -1;
	
	// ~ A B
	g.tab[2]->e = setMinMax(g.tab[2]->e,2,2); // 1 2
	g.tab[2]->color = -1;
	
	// ~ A C
	g.tab[4]->e = setMinMax(g.tab[4]->e,2,2); // 1 3
	g.tab[4]->color = -1;
	
	// ~ B C
	g.tab[5]->e = setMinMax(g.tab[5]->e,2,2); // 2 3
	g.tab[5]->color = -1;
	
	// Plane P Q R
	g.tab[55]->e = setMinMax(g.tab[55]->e,3,3); // 4 5 6
	g.tab[55]->color = -1;
	
	// Plane P' Q' R'
	g.tab[895]->e = setMinMax(g.tab[895]->e,3,3); // 8 9 10
	g.tab[895]->color = -1;
	
	// two distinct planes 1 2 4 8
	g.tab[138]->e = setMinMax(g.tab[138]->e,4,4); // 1 2 4 8
	g.tab[138]->color = -1;
	
	// Plane A B R
	g.tab[10]->e = setMinMax(g.tab[10]->e,3,3); // 1 2 4
	g.tab[10]->color = -1;
	
	// Plane A B Q
	g.tab[18]->e = setMinMax(g.tab[18]->e,3,3); // 1 2 5
	g.tab[18]->color = -1;
	
	// Line A Q R
	g.tab[24]->e = setMinMax(g.tab[24]->e,2,2); // 1 4 5
	g.tab[24]->color = -1;
	
	// Line B P R
	g.tab[41]->e = setMinMax(g.tab[41]->e,2,2); // 2 4 6
	g.tab[41]->color = -1;
			
	// Line C P Q
	g.tab[51]->e = setMinMax(g.tab[51]->e,2,2); // 3 5 6
	g.tab[51]->color = -1;
	
	// Line A P U 
	g.tab[96]->e = setMinMax(g.tab[96]->e,2,2); // 1 6 7
	g.tab[96]->color = -1;
	
	// Line B Q U
	g.tab[81]->e = setMinMax(g.tab[81]->e,2,2); // 2 5 7
	g.tab[81]->color = -1;
	
	// Plane A B R'
	g.tab[130]->e = setMinMax(g.tab[130]->e,3,3); // 1 2 8
	g.tab[130]->color = -1;
	
	// Plane A B Q'
	g.tab[258]->e = setMinMax(g.tab[258]->e,3,3); // 1 2 9
	g.tab[258]->color = -1;
	
	// Line A Q' R'
	g.tab[384]->e = setMinMax(g.tab[384]->e,2,2); // 1 8 9
	g.tab[384]->color = -1;
	
	// Line B P' R'
	g.tab[641]->e = setMinMax(g.tab[641]->e,2,2); // 2 8 10
	g.tab[641]->color = -1;
			
	// Line C P' Q'
	g.tab[771]->e = setMinMax(g.tab[771]->e,2,2); // 3 9 10
	g.tab[771]->color = -1;
	
	// Line A P' U' 
	g.tab[1536]->e = setMinMax(g.tab[1536]->e,2,2); // 1 10 11
	g.tab[1536]->color = -1;
	
	// Line B Q' U'
	g.tab[1281]->e = setMinMax(g.tab[1281]->e,2,2); // 2 9 11
	g.tab[1281]->color = -1;

	return g; // first convergence
}

// Harmonic Conjugate 14 pts
graph harmonic_part2 (graph g) {
	
	g.effectiveAllocPow = 13;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	// Line D R U
	g.tab[2119]->e = setMinMax(g.tab[2119]->e,2,2); // 4 7 12
	g.tab[2119]->color = -1;

	// Line D' R' U'
	g.tab[5247]->e = setMinMax(g.tab[5247]->e,2,2); // 8 11 13
	g.tab[5247]->color = -1;

	// Line A B C D D'
	g.tab[6150]->e = setMinMax(g.tab[6150]->e,2,2); // 1 2 3 12 13
	g.tab[6150]->color = -1;
	
	return g; // second convergence
}

// Harmonic Conjugate 14 pts
graph harmonic_part3 (graph g) {
	
	g.effectiveAllocPow = 14;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	//~ // Line P P' O
	g.tab[8735]->e = setMinMax(g.tab[8735]->e,2,2); // 6 10 14
	g.tab[8735]->color = -1;
	
	// Line Q Q' O
	g.tab[8463]->e = setMinMax(g.tab[8463]->e,2,2); // 5 9 14
	g.tab[8463]->color = -1;
	
	return g; // 12 13 = 1
}

// Dandelin Gallucci - 19 pts
graph dg (graph g) {
	
	g.effectiveAllocPow = 19;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	// line a & b
	g.tab[437]->e = setMinMax(g.tab[437]->e,4,4);
	g.tab[437]->color = -1;
	
	// line a & c
	g.tab[364]->e = setMinMax(g.tab[364]->e,4,4);
	g.tab[364]->color = -1;
	
	// line b & c
	g.tab[218]->e = setMinMax(g.tab[218]->e,4,4);
	g.tab[218]->color = -1;
	
	// line a' & b'
	g.tab[62]->e = setMinMax(g.tab[62]->e,4,4);
	g.tab[62]->color = -1;
	
	// line a' & c'
	g.tab[454]->e = setMinMax(g.tab[454]->e,4,4);
	g.tab[454]->color = -1;
	
	// line b' & c'
	g.tab[503]->e = setMinMax(g.tab[503]->e,4,4);
	g.tab[503]->color = -1;
	
	// line c 12 7 4 1
	g.tab[2120]->e = setMinMax(g.tab[2120]->e,2,2);
	g.tab[2120]->color = -1;
	
	// line b 11 8 5 2
	g.tab[1169]->e = setMinMax(g.tab[1169]->e,2,2);
	g.tab[1169]->color = -1;
	
	// line a 10 9 6 3
	g.tab[803]->e = setMinMax(g.tab[803]->e,2,2);
	g.tab[803]->color = -1;
	
	// line c' 15 9 8 7
	g.tab[16831]->e = setMinMax(g.tab[16831]->e,2,2);
	g.tab[16831]->color = -1;
	
	// line b' 6 5 4
	g.tab[55]->e = setMinMax(g.tab[55]->e,2,2);
	g.tab[55]->color = -1;
	
	// line a' 13 3 2 1
	g.tab[4102]->e = setMinMax(g.tab[4102]->e,2,2);
	g.tab[4102]->color = -1;
	
	// line e 16 15 14 13
	g.tab[61439]->e = setMinMax(g.tab[61439]->e,2,2);
	g.tab[61439]->color = -1;
	
	// line e' 16 12 11 10
	g.tab[36351]->e = setMinMax(g.tab[36351]->e,2,2);
	g.tab[36351]->color = -1;
	
	// plane 14 9 6 5 4 3
	g.tab[8507]->e = setMinMax(g.tab[8507]->e,3,3);
	g.tab[8507]->color = -1;
	
	// line a & e'
	g.tab[28963]->e = setMinMax(g.tab[28963]->e,4,4);
	g.tab[28963]->color = -1;
	
	// line b & e'
	g.tab[28817]->e = setMinMax(g.tab[28817]->e,4,4);
	g.tab[28817]->color = -1;
	
	// line c & e'
	g.tab[28744]->e = setMinMax(g.tab[28744]->e,4,4);
	g.tab[28744]->color = -1;
	
	// line a' & e
	g.tab[3590]->e = setMinMax(g.tab[3590]->e,4,4);
	g.tab[3590]->color = -1;
	
	// line b' & e
	g.tab[3639]->e = setMinMax(g.tab[3639]->e,4,4);
	g.tab[3639]->color = -1;
	
	// line c' & e
	g.tab[4031]->e = setMinMax(g.tab[4031]->e,4,4);
	g.tab[4031]->color = -1;
	
	// line 17 13 12
	g.tab[71679]->e = setMinMax(g.tab[71679]->e,2,2);
	g.tab[71679]->color = -1;
	
	// line 17 15 10
	g.tab[82431]->e = setMinMax(g.tab[82431]->e,2,2);
	g.tab[82431]->color = -1;
	
	// line 18 13 11
	g.tab[136191]->e = setMinMax(g.tab[136191]->e,2,2);
	g.tab[136191]->color = -1;
	
	// line 18 14 10
	g.tab[139775]->e = setMinMax(g.tab[139775]->e,2,2);
	g.tab[139775]->color = -1;
	
	// line 19 14 12
	g.tab[272383]->e = setMinMax(g.tab[272383]->e,2,2);
	g.tab[272383]->color = -1;
	
	// line 19 15 11
	g.tab[279551]->e = setMinMax(g.tab[279551]->e,2,2);
	g.tab[279551]->color = -1;
		
	return g; // 14 6 5 4 = 2
}

// Dandelin Gallucci - 19 pts
graph dg_part1 (graph g) {
	
	g.effectiveAllocPow = 9;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	// line a 9 6 3
	g.tab[291]->e = setMinMax(g.tab[291]->e,2,2);
	g.tab[291]->color = -1;

	// line b 8 5 2
	g.tab[145]->e = setMinMax(g.tab[145]->e,2,2);
	g.tab[145]->color = -1;

	// line c 7 4 1
	g.tab[72]->e = setMinMax(g.tab[72]->e,2,2);
	g.tab[72]->color = -1;
	
	// line a' 3 2 1
	g.tab[6]->e = setMinMax(g.tab[6]->e,2,2);
	g.tab[6]->color = -1;
	
	// line b' 6 5 4
	g.tab[55]->e = setMinMax(g.tab[55]->e,2,2);
	g.tab[55]->color = -1;
	
	// line c' 9 8 7
	g.tab[447]->e = setMinMax(g.tab[447]->e,2,2);
	g.tab[447]->color = -1;
	
	// line a & b
	g.tab[437]->e = setMinMax(g.tab[437]->e,4,4);
	g.tab[437]->color = -1;
	
	// line a & c
	g.tab[364]->e = setMinMax(g.tab[364]->e,4,4);
	g.tab[364]->color = -1;
	
	// line b & c
	g.tab[218]->e = setMinMax(g.tab[218]->e,4,4);
	g.tab[218]->color = -1;
	
	// line a' & b'
	g.tab[62]->e = setMinMax(g.tab[62]->e,4,4);
	g.tab[62]->color = -1;
	
	// line a' & c'
	g.tab[454]->e = setMinMax(g.tab[454]->e,4,4);
	g.tab[454]->color = -1;
	
	// line b' & c'
	g.tab[503]->e = setMinMax(g.tab[503]->e,4,4);
	g.tab[503]->color = -1;
	
	return g; // first convergence
}
		
// Dandelin Gallucci - 19 pts
graph dg_part2 (graph g) {
	
	g.effectiveAllocPow = 16;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	//~ // line a & b
	//~ g.tab[437]->e = setMinMax(g.tab[437]->e,4,4);
	//~ g.tab[437]->color = -1;
	//~ 
	//~ // line a & c
	//~ g.tab[364]->e = setMinMax(g.tab[364]->e,4,4);
	//~ g.tab[364]->color = -1;
	//~ 
	//~ // line b & c
	//~ g.tab[218]->e = setMinMax(g.tab[218]->e,4,4);
	//~ g.tab[218]->color = -1;
	//~ 
	//~ // line a' & b'
	//~ g.tab[62]->e = setMinMax(g.tab[62]->e,4,4);
	//~ g.tab[62]->color = -1;
	//~ 
	//~ // line a' & c'
	//~ g.tab[454]->e = setMinMax(g.tab[454]->e,4,4);
	//~ g.tab[454]->color = -1;
	//~ 
	//~ // line b' & c'
	//~ g.tab[503]->e = setMinMax(g.tab[503]->e,4,4);
	//~ g.tab[503]->color = -1;
	
	// line c 12 7 4 1
	g.tab[2120]->e = setMinMax(g.tab[2120]->e,2,2);
	g.tab[2120]->color = -1;
	
	// line b 11 8 5 2
	g.tab[1169]->e = setMinMax(g.tab[1169]->e,2,2);
	g.tab[1169]->color = -1;
	
	// line a 10 9 6 3
	g.tab[803]->e = setMinMax(g.tab[803]->e,2,2);
	g.tab[803]->color = -1;
	
	// line c' 15 9 8 7
	g.tab[16831]->e = setMinMax(g.tab[16831]->e,2,2);
	g.tab[16831]->color = -1;
	
	//~ // line b' 6 5 4
	//~ g.tab[55]->e = setMinMax(g.tab[55]->e,2,2);
	//~ g.tab[55]->color = -1;
	
	// line a' 13 3 2 1
	g.tab[4102]->e = setMinMax(g.tab[4102]->e,2,2);
	g.tab[4102]->color = -1;
	
	// line e 16 15 14 13
	g.tab[61439]->e = setMinMax(g.tab[61439]->e,2,2);
	g.tab[61439]->color = -1;
	
	// line e' 16 12 11 10
	g.tab[36351]->e = setMinMax(g.tab[36351]->e,2,2);
	g.tab[36351]->color = -1;
	
	// plane 14 9 6 5 4 3
	g.tab[8507]->e = setMinMax(g.tab[8507]->e,3,3);
	g.tab[8507]->color = -1;
	
	// line a & e
	g.tab[28963]->e = setMinMax(g.tab[28963]->e,4,4);
	g.tab[28963]->color = -1;
	
	// line b & e
	g.tab[28817]->e = setMinMax(g.tab[28817]->e,4,4);
	g.tab[28817]->color = -1;
	
	// line c & e
	g.tab[28744]->e = setMinMax(g.tab[28744]->e,4,4);
	g.tab[28744]->color = -1;
	
	// line a' & e'
	g.tab[3590]->e = setMinMax(g.tab[3590]->e,4,4);
	g.tab[3590]->color = -1;
	
	// line b' & e'
	g.tab[3639]->e = setMinMax(g.tab[3639]->e,4,4);
	g.tab[3639]->color = -1;
	
	// line c' & e'
	g.tab[4031]->e = setMinMax(g.tab[4031]->e,4,4);
	g.tab[4031]->color = -1;
		
	return g; // second convergence
}

// Dandelin Gallucci - 19 pts
graph dg_part3 (graph g) {
	
	g.effectiveAllocPow = 19;
	g.effectiveSize = spow(g.effectiveAllocPow);
	
	// line 17 13 11
	g.tab[70655]->e = setMinMax(g.tab[70655]->e,2,2);
	g.tab[70655]->color = -1;
	
	// line 17 14 10
	g.tab[74239]->e = setMinMax(g.tab[74239]->e,2,2);
	g.tab[74239]->color = -1;
	
	// line 18 13 12
	g.tab[137215]->e = setMinMax(g.tab[137215]->e,2,2);
	g.tab[137215]->color = -1;
	
	// line 18 15 10
	g.tab[147967]->e = setMinMax(g.tab[147967]->e,2,2);
	g.tab[147967]->color = -1;
	
	// line 19 14 12
	g.tab[272383]->e = setMinMax(g.tab[272383]->e,2,2);
	g.tab[272383]->color = -1;
	
	// line 19 15 11
	g.tab[279551]->e = setMinMax(g.tab[279551]->e,2,2);
	g.tab[279551]->color = -1;
		
	return g; // 14 6 5 4 = 2
}

// ------------------------------------------------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------------------------------------------------
// example0 -> 6
// example01 -> 6
// example02 -> 13
// example03 -> 5
// example04 -> 10

// example1 -> 27
// example2 -> 22
// example5 -> 198

// pasch_extended -> 111
// pappus -> 447
// example6 -> 931
// desargues3D -> 895
// desargues2D -> 28671
// harmonic -> 6143
// dg -> 8247



int main(int argc, char * argv[]) {
	
	allocSize sizeTab;
	graph g1,g2,g3;
	int res = 111;
	
	int i, nbp;

	FILE* file = NULL;
	file = fopen(filename,"w");
	
	fprintf(stderr,"-------------- initialisation\n\n");
	
	sizeTab = allocSizeTab(1,2);
	nbp = 7;
	g1 = allocGraph(nbp);
	
	//~ sizeTab = allocSizeTab(3,2);
	//~ nbp = 9;
	//~ g1 = allocGraph(nbp);
	//~ nbp = 16;
	//~ g2 = allocGraph(nbp);
	//~ nbp = 19;
	//~ g3 = allocGraph(nbp);
	
	fprintf(stderr,"-------------- convergence\n\n");

	//~ printGraphWithoutProof(g1);

	g1 = pasch_extended(g1);
	sizeTab.tab[0][0] = g1.effectiveAllocPow;
	sizeTab.tab[0][1] = g1.effectiveSize;
	g1 = convergenceParties(g1,res);

	printGraphWithoutProof(g1);

	//~ preMark(g1.tab[res]);
	//~ constructLemma(file, g1, g1.tab[res]);
	//~ constructIntro(file, g1);
	//~ constructProof(file, g1.tab[res], sizeTab, 1);
	
	/////////////////////////////////////////////////////////////////
	
	//~ fprintf(stderr,"-------- convergence 1\n");
	//~ g1 = dg_part1(g1);
	//~ sizeTab.tab[0][0] = g1.effectiveAllocPow;
	//~ sizeTab.tab[0][1] = g1.effectiveSize;
	//~ g1 = convergenceParties(g1,res);
	//~ 
	//~ copyGraph(g1,g2,res);
	//~ fprintf(stderr,"-------- convergence 2\n");
	//~ 
	//~ g2 = dg_part2(g2);
	//~ sizeTab.tab[1][0] = g2.effectiveAllocPow;
	//~ sizeTab.tab[1][1] = g2.effectiveSize;
	//~ g2 = convergenceParties(g2,res);
//~ 
	//~ copyGraph(g2,g3,res);
	//~ fprintf(stderr,"-------- convergence 3\n");
//~ 
	//~ g3 = dg_part3(g3);
	//~ sizeTab.tab[2][0] = g3.effectiveAllocPow;
	//~ sizeTab.tab[2][1] = g3.effectiveSize;
	//~ g3 = convergenceParties(g3,res);
	//~ 
	//~ fprintf(stderr,"--------------- reconstruction\n\n");
	//~ 
	//~ preMark(g3.tab[res]);
//~ 
	//~ for(i = 0; i < g2.effectiveSize; i++)
	//~ {
		//~ if(g3.tab[i]->mark == 1 && i != res)
		//~ {
			//~ preMark(g2.tab[i]);
		//~ }
	//~ }
	//~ 
	//~ for(i = 0; i < g1.effectiveSize; i++)
	//~ {
		//~ if(g2.tab[i]->mark == 1 && i != res)
		//~ {
			//~ preMark(g1.tab[i]);
			//~ constructLemma(file, g1, g1.tab[i]);
			//~ constructIntro(file, g1);
			//~ constructProof(file,g1.tab[i], sizeTab, 1);
			//~ g1.tab[i]->mark = 4;
			//~ unMark(g1.tab[i]);
		//~ }
	//~ }
	//~ 
	//~ for(i = g1.effectiveSize; i < g2.effectiveSize; i++)
	//~ {
		//~ if(g3.tab[i]->mark == 1 && i != res)
		//~ {
			//~ preMark(g2.tab[i]);
			//~ constructLemma(file, g2, g2.tab[i]);
			//~ constructIntro(file, g2);
			//~ constructProof(file,g2.tab[i], sizeTab, 1);
			//~ g2.tab[i]->mark = 4;
			//~ unMark(g2.tab[i]);
		//~ }
	//~ }
	//~ 
	//~ constructLemma(file, g3, g3.tab[res]);
	//~ constructIntro(file, g3);
	//~ constructProof(file, g3.tab[res], sizeTab, 1);
	
	fclose(file);
	
	return 0;
}
