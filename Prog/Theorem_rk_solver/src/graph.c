#include "graph.h"

node createNode (myType e) {
	
	//create new node
	node new = (s_node *)malloc(sizeof(s_node));
	new->e = e;
	new->color = 0;
	new->mark = 0;
	new->rule = 0;
	new->ante = NULL;
	new->succ = NULL;
	
	return new;
}

node addNode (list l, myType e, int rule) {
	
	//create new node
	node new = (s_node *)malloc(sizeof(s_node));
	new->e = e;
	new->color = 0;
	new->mark = 0;
	new->rule = rule;
	new->ante = l;
	new->succ = NULL;

	list tmp = l;
	while(tmp != NULL)
	{
		if(tmp->n->succ == NULL)
		{
			tmp->n->succ = createList(new);
		}
		else
		{
			tmp->n->succ = addList(tmp->n->succ,new);
		}
		tmp = tmp->next;
	}
	return new;
}

list createList (node n) {
	
	//create new list
	list new = (s_list *)malloc(sizeof(s_list));
	new->n = n;
	new->next = NULL;
	new->prev = NULL;
	
	return new;
}

list addList (list l, node n) {

	//add element
	list new = (s_list *)malloc(sizeof(s_list));
	new->n = n;
	
	list tmp = l;
	while(tmp->next != NULL)
	{
		tmp = tmp->next;
	}
	
	tmp->next = new;
	new->prev = tmp;
	new->next = NULL;
	
	return l;
}

int checkSuccList (list l){
	int mark = 1;
	
	list tmp = l;
	while(tmp != NULL && mark == 1)
	{
		if(tmp->n->mark == 1 || tmp->n->mark == 2)
		{
			mark = 0;
		}
		tmp = tmp->next;
	}
	
	return mark;
}

void printNode(node n) {
	if(n != NULL)
	{
		printSet(n->e);
	}
}

void printNodes(node n, int space) {
	if(n != NULL)
	{
		printSet(n->e);

		list tmp = n->ante;
		
		while(tmp != NULL)
		{
			int i = space;
			while(i > 0)
			{
				printf("     ");
				i--;
			}
			printf("%d -----> ", n->rule);
			printNodes(tmp->n, space+1);
			tmp=tmp->next;
		}
	}
}


