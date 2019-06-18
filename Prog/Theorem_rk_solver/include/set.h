#ifndef __SET_H_
#define __SET_H_

#include <stdio.h>
#include <stdlib.h>

// 28 bytes for set & 4 bits for rank min|max
#define myType unsigned int
#define sizemyType 32
#define realSizemyType 28

myType setIByte(myType e, int i);
myType unsetIByte(myType e, int i);
int getBytes(myType e, int i);
myType getIBytes(myType e, int i);
int countBytes(myType e);
myType initSet();
myType DecToBin(int i);
myType initRanks(myType e);

int rankMax(myType e);
myType setMax(myType e, int i);
int rankMin(myType e);
myType setMin(myType e, int i);
myType setMinMax(myType e, int i, int j);
int rankMinMaxEqual(myType e, int value);
int incl(myType e1, myType e2);

void printSet(myType e);
void printBytes(myType e);
void printBytesAsNumber(myType e);
void printBytesAsRank(myType e);

#endif //__SET_H_
