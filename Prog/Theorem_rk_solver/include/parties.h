#ifndef __PARTIES_H_
#define __PARTIES_H_

#include "graph.h"
#include "maths_addon.h"

#define filename "proof.txt"

typedef struct allocSize {
	int ** tab;
	int size;
}allocSize;

typedef struct graph {
	node * tab;
	int effectiveSize;
	int size;
	int effectiveAllocPow;
	int allocPow;
}graph;

allocSize allocSizeTab (int n, int m);
graph allocGraph (int n);
graph copyGraph(graph g1, graph g2, int res);

graph convergenceParties (graph g, int res);
graph applyPappus (graph g, int * convergence, int loopnumber);
graph applyPappusParties (graph g, int i, int j, int * convergence, int loopNumber);
myType existPappusConfiguration(graph g, myType e1, myType e2, myType e3, myType e4, myType e5, myType e6);
myType existIntersectPoint(graph g, myType e1, myType e2);

void preMark(node n);
void unMark(node n);
void constructLemma(FILE* file, graph g, node n);
void constructIntro(FILE* file, graph g);
void constructProofaux (FILE* file, node n, allocSize tab, int previousConstruct);
void constructProof (FILE* file, node n, allocSize tab, int previousConstruct);
void printSetFile (FILE* file, myType e);
void printHypSetFile (FILE* file, myType e);

void printLineGraph (graph g, int i);
void printLineGraphWithoutProof (graph g, int i);
void printGraph (graph g);
void printGraphWithoutProof(graph g);



#endif //__PARTIES_H_


