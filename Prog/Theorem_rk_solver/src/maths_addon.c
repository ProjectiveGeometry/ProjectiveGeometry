#include "maths_addon.h"

int factRec (int n) {
  if (n <= 1)
    return 1;
  else
    return n * factRec(n-1);
}

int fact (int n) {
  int f;
  for (f = 1; n > 1; n--)
    f *= n;
  return f;
}

int spow (int n) {
	return pow(2.0,n)-1;
}

// Cet algorithme nécessite 2n-1 multiplications et 1 division.
int binomial_slow (int n, int p) {
  return fact(n)/(fact(p)*fact(n-p));
}

// Cet algorithme nécessite 2(p-1) multiplications et 1 division.
int binomial_moderate (int n, int p) {
  int num; // Numérateur
  int k; // Variable d'itération

  // On se ramène au cas où p <= n-p
  if (p > n-p) 
    p = n-p;

  // Calcul du numérateur
  for (num = 1, k = n-p+1; k <= n; k++)
    num *= k;

  // Calcul du binômial
  return num/fact(p);
}

// Cet algorithme nécessite p-1 multiplications et p-1 divisions.
int binomial_fast (int n, int p) {
  int binom;			// Résultat
  int k;			// Variable d'itération

  // On se ramène au cas où p <= n-p
  if (p > n-p) 
    p = n-p;

  // k     prend les valeurs     1 ... p
  // n-p+k prend les valeurs n-p+1 ... n
  for (binom = 1, k = 1; k <= p; k++)
    // Il est important de faire la mutiplication avant la division.
    // Le résultat intermédiaire binom/k n'est pas nécessairement un 
    // entier.
    binom = (binom * (n-p+k)) / k;

  return binom;
}
