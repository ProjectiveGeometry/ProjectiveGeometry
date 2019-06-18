#ifndef __GRAPH_H_
#define __GRAPH_H_

#include "set.h"
#include "maths_addon.h"

typedef struct s_node s_node,*node;

typedef struct s_list {
	s_node * n;
	struct s_list * prev;
	struct s_list * next;
}s_list,*list;

struct s_node {
	myType e;
	int color;
	int mark;
	int rule;
	s_list * ante;
	s_list * succ;
};

node createNode (myType e);
node addNode (list l, myType e, int rule);
list createList (node n);
list addList (list l, node n);
int checkSuccList (list l);

void printNode(node n);
void printNodes(node n, int space);

#endif //__GRAPH_H_


