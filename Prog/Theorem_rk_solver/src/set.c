#include "set.h"

myType setIByte(myType e, int i) {
	myType mask = 1u << (i-1);
	myType result = e | mask;
	return result;
}

myType unsetIByte(myType e, int i) {
	myType mask = ~(1u << (i-1));
	myType result = e & mask;
	return result;
}

int getBytes(myType e, int i) {
	int result = e >> (i-1) & 0x1;
	return result;
}

myType getIBytes(myType e, int i) {
	myType mask,res;
	int j = 0;
	while(i != 0 && j <= sizemyType -1)
	{
		mask = 1u << j;
		res = e & mask;
		if(res)
		{
			i--;
		}
		j++;
	}
	return res;
}

int countBytes(myType e) {
	return __builtin_popcount(e);
}

myType initSet() {
	myType e;
	e = 0x0;
	return e;
}

myType DecToBin(int i) {
	int j;
	int cpt=1;
	myType res = 0x0;
	
	while(i > 0)
	{
		j = i%2;
		
		if(j == 1)
		{
			res = setIByte(res,cpt);
		}
		i=i/2;
		cpt++;
	}
	
	return res;
}

myType initRanks(myType e) {
	int bits = countBytes(e);
	
	if(bits >= 4)
	{
		e = setIByte(e,sizemyType);
		e = setIByte(e,sizemyType-1);
	}
	else if(bits == 3)
	{
		e = setIByte(e,sizemyType);
	}
	else if(bits == 2)
	{
		e = setIByte(e,sizemyType-1);
	}
	
	return e;
}

int rankMax(myType e) {
	int i;
	int k,l;
	
	i = sizemyType-1;
	k = (e >> i & 0x1) == 1;
	l = (e >> (i-1) & 0x1) == 1;
	
	if(k == 1)
	{
		if(l == 1)
		{
			return 4;
		}
		else
		{
			return 3;
		}
	}
	else
	{
		if(l == 1)
		{
			return 2;
		}
		else
		{
			return 1;
		}
	}
}

myType setMax(myType e, int i) {
	
	if(i == 4)
	{
		e = (e & 0x3FFFFFFF) | 0xC0000000;
	}
	else if(i == 3)
	{
		e = (e & 0x3FFFFFFF) | 0x80000000;
	}
	else if(i == 2)
	{
		e = (e & 0x3FFFFFFF) | 0x40000000;
	}
	else if(i == 1)
	{
		e = (e & 0x3FFFFFFF);
	}
	
	return e;	
}

int rankMin(myType e) {
	int i;
	int o,p;
	
	i = sizemyType-3;
	o = (e >> i & 0x1) == 1;
	p = (e >> (i-1) & 0x1) == 1;
	
	if(o == 1)
	{
		if(p == 1)
		{
			return 4;
		}
		else
		{
			return 3;
		}
	}
	else
	{
		if(p == 1)
		{
			return 2;
		}
		else
		{
			return 1;
		}
	}
}

myType setMin(myType e, int i) {
	
	if(i == 4)
	{
		e = (e & 0xCFFFFFFF) | 0x30000000;
	}
	else if(i == 3)
	{
		e = (e & 0xCFFFFFFF) | 0x20000000;
	}
	else if(i == 2)
	{
		e = (e & 0xCFFFFFFF) | 0x10000000;
	}
	else if(i == 1)
	{
		e = (e & 0xCFFFFFFF);
	}
	
	return e;	
}

myType setMinMax(myType e, int i, int j) {
	e = setMax(e,i);
	e = setMin(e,j);
	return e;
}

int rankMinMaxEqual(myType e, int value) {
	int min = rankMin(e);
	int max = rankMax(e);
	
	if(min == value && max == value)
	{
		return 1;
	}
	else
	{
		return 0;
	}
}

int incl(myType e1, myType e2) {
	if(((e1 & 0x0FFFFFFF) & (e2 & 0x0FFFFFFF)) == (e1 & 0x0FFFFFFF))
	{
		return 1;
	}
	else
	{
		return 0;
	}
}

void printSet(myType e) {
	printBytesAsRank(e);printBytes(e);printBytesAsNumber(e);
}

void printBytes(myType e) {
	int i;
	myType mask;
	for(i = sizemyType-1; i >= 0; i--)
	{
		mask = 1u << i;
		if(e & mask)
		{
			printf("%d",1);
		}
		else
		{
			printf("%d",0);
		}
	}
}

void printBytesAsNumber(myType e) {
	int i,j;
	int first = 1;
	j = realSizemyType;
	printf("  "); // blank for printSet
	printf("{");
	for(i = realSizemyType-1; i >= 0; i--)
	{
		if(first)
		{
			if(((e >> i) & 0x1) == 1)
			{
				printf("%d",j);
				first = 0;
			}
		}
		else
		{
			if(((e >> i) & 0x1) == 1)
			{
				printf(",%d",j);
			}
		}
		j--;
	}
	printf("}");
	printf("\n");
}

void printBytesAsRank(myType e) {
	int i;
	int k,l,o,p;
	
	i = sizemyType-1;
	k = (e >> i & 0x1) == 1;
	l = (e >> (i-1) & 0x1) == 1;
	
	i = sizemyType-3;
	o = (e >> i & 0x1) == 1;
	p = (e >> (i-1) & 0x1) == 1;
	
	if(k == 1)
	{
		if(l == 1)
		{
			printf("Rank max : 4, ");
		}
		else
		{
			printf("Rank max : 3, ");
		}
	}
	else
	{
		if(l == 1)
		{
			printf("Rank max : 2, ");
		}
		else
		{
			printf("Rank max : 1, ");
		}
	}
	
	if(o == 1)
	{
		if(p == 1)
		{
			printf("Rank min : 4 | ");
		}
		else
		{
			printf("Rank min : 3 | ");
		}
	}
	else
	{
		if(p == 1)
		{
			printf("Rank min : 2 | ");
		}
		else
		{
			printf("Rank min : 1 | ");
		}
	}
}
	
	
