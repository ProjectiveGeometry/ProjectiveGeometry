#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

int** fill_inc_tab(int** tab_inc, int n, int p, int** tab);

//////////////////////////////////////////////////////////////
////////////////// supplement ////////////////////////

int puissance(int a, int b){
    int i;
    for(i=0;i<b;i++){
        a=a*a;
    }
    return a;
}

void print_tab_console(int n, int p, int** tab){

    int i,j;
    printf("\n");
    for(i=0;i<n;i++){

        for(j=0;j<p;j++){

            printf("%d ",tab[i][j]);
        }
        printf("\n");
    }
    printf("\n");
}

/////////////////////////////////////////////////////////////
///////////// creation de tableau ///////////////////////////

/*
*   entr�e: n:nombre de ligne
*           p:nombre de colonne
*
*   sortie: tableau cr��
*   utilit�: alloue la m�moire pour un tableau de taille indiqu�
*/

int **creer_tab(int n,int p){

    int i;
    int **tab;

    tab=malloc(n*sizeof(int*));

    for(i=0;i<n;i++){

        tab[i]=malloc(p*sizeof(int));
    }

    return tab;
}

/*
*   entr�e: n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau a traiter
*
*   sortie: tableau trait�
*   utilit�: met � -1 toutes les cases du tableau
*/

int **set_tab(int n,int p,int** tab){

    int i,j;

    for(i=0;i<n;i++){

        for(j=0;j<p;j++){

            tab[i][j]=-1;
        }
    }

    return tab;
}

/*
*   entr�e: n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau a traiter
*
*   sortie: tableau trait�
*   utilit�: met � 0 toutes les cases du tableau
*/

int **set_tab_to_0(int n,int p,int** tab){

    int i,j;

    for(i=0;i<n;i++){

        for(j=0;j<p;j++){

            tab[i][j]=0;
        }
    }

    return tab;
}

/*
*   entr�e: lin:ligne a set
*           p:nombre de colonne
*           tab:tableau a traiter
*
*   sortie: tableau trait�
*   utilit�: remet � -1 la ligne d�sign�
*/

int **set_line(int lin,int p,int** tab){

    int j;

    for(j=0;j<p;j++){

    	tab[lin][j]=-1;
    }

    return tab;
}

/*
*   entr�e: lin:ligne a set
*           p:nombre de colonne
*           tab:tableau a traiter
*
*   sortie: tableau trait�
*   utilit�: remet � 0 la ligne d�sign�
*/

int **set_line_to_0(int lin,int p,int** tab){

    int j;

    for(j=0;j<p;j++){

    	tab[lin][j]=0;
    }

    return tab;
}

/*
*   entr�e: lin: nombre de ligne
*           tab:tableau � liberer
*
*   sortie: rien
*   utilit�: lib�re la place prise par le tableau dans la m�moire
*/

void free_tab(int lin,int** tab){
    int i;

    for(i=0;i<lin;i++){

        free(tab[i]);
    }
    free(tab);
}

///////////////////////////////////////////////////////////////////////////
////////////////////////////////// DESARGUE ///////////////////////////////

/*
*   entr�e: a,b,c:points � v�rifier
*           p:taille du tableau (carr�)
*           tab_inc:tableau a traiter
*
*   sortie: booleen
*   utilit�: valide si 3 points sont colineaires
*/

int colinear(int a, int b, int c, int p, int** tab_inc){

    int i;

    for(i=0;i<p;i++){

            if(tab_inc[i][a]==1 && tab_inc[i][b]==1 && tab_inc[i][c]==1)
                return 1;
    }

    return 0;
}

/*
*   entr�e: a,b:points de la premi�re droite
*           A,B:points de la seconde droite
*           p:taille du tableau (carr�)
*           tab_inc:tableau a traiter
*
*   sortie: point d'intersection
*   utilit�: trouve le point d'intersection de deux droites
*/

int inter_line(int a, int b, int A, int B, int p, int** tab_inc){

    int i,d1,d2;

    for(i=0;i<p;i++){

        if(tab_inc[i][a]==1 && tab_inc[i][b]==1){

            d1=i;
        }
        if(tab_inc[i][A]==1 && tab_inc[i][B]==1){

            d2=i;
        }
    }

    for(i=0;i<p;i++){

        if(tab_inc[d1][i]==1 && tab_inc[d2][i]==1)
            return i;
    }
    return -1;
}

/*
*   entr�e: n:taille du tableau (carr�)
*           fichier:emplacement d'�criture
*           tab_inc:tableau a traiter
*
*   sortie: bool�en
*   utilit�: v�rifie si d�sargue est resp�ct� avec la table d'incidence
*/

int is_desargue(int n, int** inc_tab, FILE* fichier){
    int o,p,q,r,P,Q,R,a,b,g;
    int counto=0,countp=0,countq=0,countr=0,countP=0,countQ=0,countR=0,count1=0,count2=0,count3=0,count4=0,count5=0,count6=0;
    for(o=0;o<n;o++){
        counto++;
        for(p=0;p<n;p++){
            countp++;
            for(q=0;q<n;q++){
                countq++;
                if(!colinear(o,p,q,n,inc_tab)){
                    count1++;
                    for(r=0;r<n;r++){
                        countr++;
                        if(!colinear(o,p,r,n,inc_tab) && !colinear(o,q,r,n,inc_tab) && !colinear(p,q,r,n,inc_tab)){
                            count2++;
                            for(P=0;P<n;P++){
                                countP++;
                                if(colinear(o,p,P,n,inc_tab)){
                                    count3++;
                                    for(Q=0;Q<n;Q++){
                                        countQ++;
                                        if(colinear(o,q,Q,n,inc_tab)){
                                            count4++;
                                            for(R=0;R<n;R++){
                                                countR++;
                                                if(colinear(o,r,R,n,inc_tab) && !colinear(P,Q,R,n,inc_tab)){
                                                    count5++;
                                                    if((p==P && q!=Q && r!=R) || (p!=P && q==Q && r!=R) || (p!=P && q!=Q && r==R) || (p!=P && q!=Q && r!=R)){
                                                        count6++;

                                                        a=inter_line(p,q,P,Q,n,inc_tab);
                                                        b=inter_line(p,r,P,R,n,inc_tab);
                                                        g=inter_line(q,r,Q,R,n,inc_tab);

                                                        if(!colinear(a,b,g,n,inc_tab)){

                                                            return 0;
                                                       }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    fprintf(fichier,"passage o:%d\n \npassage p:%d\n \npassage q:%d\n \nif(!col(o,p,q)):%d\n \npassage r:%d\n \nif( !col(o,p,r) && !col(o,q,r) && !col(p,q,r) ):%d\n \npassage P:%d\n \nif( col(o,p,P) ):%d\n \npassage Q:%d\n \nif( col(o,q,Q) ):%d\n \npassage R:%d\n \nif( col(o,r,R) && !col(P,Q,R) ):%d\n \ndeux distinction min:%d\n",counto,countp,countq,count1,countr,count2,countP,count3,countQ,count4,countR,count5,count6);
    return 1;
}

// �quivalent avec le premier point fixe

int is_desargue_quick(int n, int** inc_tab, FILE* fichier){
    int o=0,p,q,r,P,Q,R,a,b,g;
    int countp=0,countq=0,countr=0,countP=0,countQ=0,countR=0,count1=0,count2=0,count3=0,count4=0,count5=0,count6=0;
        for(p=0;p<n;p++){
            countp++;
            for(q=0;q<n;q++){
                countq++;
                if(!colinear(o,p,q,n,inc_tab)){
                    count1++;
                    for(r=0;r<n;r++){
                        countr++;
                        if(!colinear(o,p,r,n,inc_tab) && !colinear(o,q,r,n,inc_tab) && !colinear(p,q,r,n,inc_tab)){
                            count2++;
                            for(P=0;P<n;P++){
                                countP++;
                                if(colinear(o,p,P,n,inc_tab)){
                                    count3++;
                                    for(Q=0;Q<n;Q++){
                                        countQ++;
                                        if(colinear(o,q,Q,n,inc_tab)){
                                            count4++;
                                            for(R=0;R<n;R++){
                                                countR++;
                                                if(colinear(o,r,R,n,inc_tab) && !colinear(P,Q,R,n,inc_tab)){
                                                    count5++;
                                                    if((p==P && q!=Q && r!=R) || (p!=P && q==Q && r!=R) || (p!=P && q!=Q && r==R) || (p!=P && q!=Q && r!=R)){
                                                        count6++;

                                                        a=inter_line(p,q,P,Q,n,inc_tab);
                                                        b=inter_line(p,r,P,R,n,inc_tab);
                                                        g=inter_line(q,r,Q,R,n,inc_tab);

                                                        if(!colinear(a,b,g,n,inc_tab)){
                                                            return 0;
                                                       }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    fprintf(fichier,"passage p:%d\n \npassage q:%d\n \nif(!col(o,p,q)):%d\n \npassage r:%d\n \nif( !col(o,p,r) && !col(o,q,r) && !col(p,q,r) ):%d\n \npassage P:%d\n \nif( col(o,p,P) ):%d\n \npassage Q:%d\n \nif( col(o,q,Q) ):%d\n \npassage R:%d\n \nif( col(o,r,R) && !col(P,Q,R) ):%d\n \ndeux distinction min:%d\n",countp,countq,count1,countr,count2,countP,count3,countQ,count4,countR,count5,count6);
    return 1;
}

/*
*   entr�e: type: 1 si speed 0 si complet
*           nb_tab:nombre de table � traiter
*           rang:rang pour le quel on v�rifie d�sargue
*           fic_in:fichier dans le quel on lie les tables
*           fic_out:fichier dans le quel on ressort les donn�es
*
*   sortie: rien
*   utilit�: v�rifie desargues pour toutes les tables pr�sentes dans fic_in
*/

void desargue_multiple(int type, int nb_tab, int rang, FILE* fic_in, FILE* fic_out){

    int i=0,j=0,k,l,n,p,numb=0,ch;

    n=rang+1;
    p=rang*rang+rang+1;

    int** tab_temp=creer_tab(n,p);
    tab_temp=set_tab(n,p,tab_temp);

    int** tab_temp_inc=creer_tab(p,p);
    tab_temp_inc=set_tab_to_0(p,p,tab_temp_inc);

    fseek(fic_in,50,SEEK_SET);

    for(k=0;k<nb_tab;k++){

        for(l=0;l<(rang+1)+1;l++){

            while(fgetc(fic_in) != 10);
        }

        while((i<n-1 && j<p)){

            while((ch=fgetc(fic_in)) != '\n' ){

                while((ch=fgetc(fic_in)) != 32){

                    numb = (numb*10)+(ch-48);
                }

                tab_temp[i][j]=numb;
                i++;
                numb=0;

                if(i>=n){

                    i=0;
                    j++;
                }
            }
        }

        fill_inc_tab(tab_temp_inc,n,p,tab_temp);
        fprintf(fic_out,"\nTable %d: \n",k);

        if(type==1){
            if(!is_desargue_quick(p,tab_temp_inc,fic_out)){

                fprintf(fic_out,"Ne respecte pas d�sargue\n \n");
            }
        }else{
            if(!is_desargue(p,tab_temp_inc,fic_out)){

                fprintf(fic_out,"Ne respecte pas d�sargue\n \n");
            }
        }

        while(fgetc(fic_in) != '\n');
    }

    free_tab(n,tab_temp);
    free_tab(p,tab_temp_inc);
}
//////////////////////////////////////////////////////////////////////////
////////////////// math verification /////////////////////////////////////

int line_exist(int n,int** tab){

    int i,j,k,count;

    for(j=0;j<n-1;j++){

        for(k=j+1;k<n;k++){

            for(i=0;i<n;i++){
                if(tab[i][k]==1 && tab[i][j]==1)
                    count++;
            }

            if(count==0)
                return 0;
            count=0;
        }
    }
    return 1;
}

int point_exist(int n,int** tab){

    int i,j,k,count;

    for(i=0;i<n-1;i++){

        for(k=i+1;k<n;k++){

            for(j=0;j<n;j++){

                if(tab[i][j]==1 && tab[k][j]==1)
                    count++;
            }

            if(count==0)
                return 0;
            count=0;
        }
    }
    return 1;
}

int three_points(int n,int** tab){

    int i,j,count;

    for(i=0;i<n;i++){
        count=0;
        for(j=0;j<n;j++){

            if(tab[i][j]==1)
                count++;
        }
        if(count<3)
            return 0;
    }
    return 1;
}

int uniqueness(int n,int** tab){
    int i,j,k,l;

    for(i=0;i<n;i++){

        for(k=0;k<n;k++){

            for(j=0;j<n;j++){

                for(l=0;l<n;l++){

                    if(tab[i][j]==1 && tab[i][l]==1 && tab[k][j]==1 && tab[k][l]==1){

                        if(i!=k && j!=l){
                            return 0;
                        }
                    }
                }
            }
        }
    }

    return 1;
}

int lower_dim(int n,int** tab){
    int i,j;

    for(i=0;i<n-1;i++){

        for(j=0;j<n;j++){

            if(tab[i][j]!=tab[i+1][j])
                return 1;
        }
    }
    return 0;
}

/////////////////////////////////////////////////////////////////
//////////////////// verification ///////////////////////////////
/*
int compare(int p,int** tab_ref_inc,int** tab_temp_inc){

    int i,j,k,swap;
    int* temp_col_v=malloc(p*sizeof(int));
    int* ref_col_v=malloc(p*sizeof(int));
    int* temp_lin_v=malloc(p*sizeof(int));
    int* ref_lin_v=malloc(p*sizeof(int));

    for(k=0;k<p;k++){
        temp_col_v[k]=0;
        ref_col_v[k]=0;
        temp_lin_v[k]=0;
        ref_lin_v[k]=0;
    }

    for(j=0;j<p;j++){

        for(i=0;i<p;i++){

            if(tab_temp_inc[i][j]==1){
                temp_col_v[j]+=(int)pow(2,(p-1)-i);
            }

            if(tab_ref_inc[i][j]==1){
                ref_col_v[j]+=(int)pow(2,(p-1)-i);
            }
        }
    }

    for(j=0;j<p-1;j++){

        for(k=j+1;k<p;k++){

            if(temp_col_v[j]<temp_col_v[k]){

                for(i=0;i<p;i++){

                    swap=tab_temp_inc[i][j];
                    tab_temp_inc[i][j]=tab_temp_inc[i][k];
                    tab_temp_inc[i][k]=swap;
                }

                swap=temp_col_v[j];
                temp_col_v[j]=temp_col_v[k];
                temp_col_v[k]=swap;
            }

            if(ref_col_v[j]<ref_col_v[k]){

                for(i=0;i<p;i++){

                    swap=tab_ref_inc[i][j];
                    tab_ref_inc[i][j]=tab_ref_inc[i][k];
                    tab_ref_inc[i][k]=swap;
                }

                swap=ref_col_v[j];
                ref_col_v[j]=ref_col_v[k];
                ref_col_v[k]=swap;
            }
        }
    }

    for(i=0;i<p;i++){

        for(j=0;j<p;j++){

            if(tab_temp_inc[i][j]==1){
                temp_lin_v[i]+=(int)pow(2,(p-1)-j);
            }
            if(tab_ref_inc[i][j]==1){
                ref_lin_v[i]+=(int)pow(2,(p-1)-j);
            }
        }
    }

    for(i=0;i<p-1;i++){

        for(k=i+1;k<p;k++){

            if(temp_lin_v[i]<temp_lin_v[k]){

                for(j=0;j<p;j++){

                    swap=tab_temp_inc[i][j];
                    tab_temp_inc[i][j]=tab_temp_inc[k][j];
                    tab_temp_inc[k][j]=swap;
                }

                swap=temp_lin_v[i];
                temp_lin_v[i]=temp_lin_v[k];
                temp_lin_v[k]=swap;
            }

            if(ref_lin_v[i]<ref_lin_v[k]){

                for(j=0;j<p;j++){

                    swap=tab_ref_inc[i][j];
                    tab_ref_inc[i][j]=tab_ref_inc[k][j];
                    tab_ref_inc[k][j]=swap;
                }

                swap=ref_lin_v[i];
                ref_lin_v[i]=ref_lin_v[k];
                ref_lin_v[k]=swap;
            }
        }
    }

    for(i=0;i<p;i++){

        for(j=0;j<p;j++){

            if(tab_ref_inc[i][j]!=tab_temp_inc[i][j]){

                return 0;
            }
        }
    }
    return 1;
}

void are_same_plane(int nb_tab,int rang,FILE* fic_in){

    int i=0,j=0,k,l,n,p,numb=0,ch;

    n=rang+1;
    p=rang*rang+rang+1;

    int** tab_ref=creer_tab(n,p);
    tab_ref=set_tab(n,p,tab_ref);
    int** tab_temp=creer_tab(n,p);
    tab_temp=set_tab(n,p,tab_temp);

    int** tab_ref_inc=creer_tab(p,p);
    tab_ref_inc=set_tab_to_0(p,p,tab_ref_inc);
    int** tab_temp_inc=creer_tab(p,p);
    tab_temp_inc=set_tab_to_0(p,p,tab_temp_inc);

    fseek(fic_in,50,SEEK_SET);

    for(l=0;l<(rang+1)+1;l++){

        while(fgetc(fic_in) != 10);
    }

    while((i<n-1 && j<p)){

        while((ch=fgetc(fic_in)) != '\n' ){

            while((ch=fgetc(fic_in)) != 32){

                numb = (numb*10)+(ch-48);
            }

            tab_ref[i][j]=numb;
            i++;
            numb=0;

            if(i>=n){

                i=0;
                j++;
            }
        }
    }
    tab_ref_inc=fill_inc_tab(tab_ref_inc,n,p,tab_ref);

    for(k=1;k<nb_tab;k++){
        i=0;
        j=0;
        for(l=0;l<(rang+1)+1;l++){

            while(fgetc(fic_in) != 10);
        }

        while((i<n-1 && j<p)){

            while((ch=fgetc(fic_in)) != '\n' ){

                while((ch=fgetc(fic_in)) != 32){

                    numb = (numb*10)+(ch-48);
                }

                tab_temp[i][j]=numb;
                i++;
                numb=0;

                if(i>=n){

                    i=0;
                    j++;
                }
            }
        }
        tab_temp_inc=fill_inc_tab(tab_temp_inc,n,p,tab_temp);
        tab_temp=set_tab(n,p,tab_temp);

        if(!compare(p,tab_ref_inc,tab_temp_inc)){
            printf("table %d\n",k);
        }else{
            printf("%d est identique\n",k);
        }
        tab_temp_inc=set_tab_to_0(p,p,tab_temp_inc);
    }
}
*/

/*
*   entr�e: p:taille du tableau (carr�)
*           tab:tableau a traiter
*
*   sortie: rien
*   utilit�: affiche si la table d'incidence respecte les regles
*/

void verify_inc_tab(int p,int **tab, FILE* fichier){

    int i,j,count=0;

    for(i=0;i<p;i++){

        for(j=0;j<p;j++){

            if(tab[i][j]==1 && tab[i][(j+1)%p]==1){

                count++;
            }
        }

        if(count!=1){

                fprintf(fichier,"/!\\ erreur de table /!\\");
        }

        count=0;
    }

    for(i=0;i<p;i++){

        for(j=0;j<p;j++){

            if(tab[i][j]==1 && tab[(i+1)%p][j]==1){

                count++;
            }
        }

        if(count!=1){

                fprintf(fichier,"/!\\ erreur de table /!\\");
        }

        count=0;
    }
}

/*
*   entr�e: c:valeur a verifier
*           lin:ligne pour placer la valeur
*           col:colonne pour placer la valeur
*           n:nombre de lignes
*           p:nombre de colonnes
*           tab:tableau d'acceuil de la valeur
*
*   sortie: booleen vrai ou faux
*   utilit�: v�rifie la validit� de la valeur l� o� on veut la rentrer
*/

int check_c(int c,int lin, int col,int n,int p,int **tab){

    int i,j,k,test,count=0;

    /* couples */
    for(k=0;k<lin;k++){

        test=tab[k][col];

        if(test==c)
            return 0;

        for(j=0;j<p&&j!=col;j++){

            for(i=0;i<n;i++){

                if((tab[i][j]==test) || tab[i][j]==c)
                    count++;
            }

            if(count>1)
                return 0;

            count=0;
        }
    }

    return 1;
}

////////////////////////////////////////////////////////////////////////
///////////////////////// affichage ////////////////////////////////////

/*
*   entr�e: n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau a afficher
*           fichier:fichier dans le quel effectuer l'affichage
*
*   sortie: rien
*/

void print_tab_inc(int n, int p, int** tab_inc,FILE* fichier){

    int i, j;

    for(i=0;i<n;i++){

        for(j=0;j<p;j++){

            fprintf(fichier," %d ",tab_inc[i][j]);
        }

        fprintf(fichier,"\n");
    }
    fprintf(fichier,"\n");
}

/*
*   entr�e: n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau a afficher
*
*   sortie: tableau modifi�
*   utilit�: range chaque colonne puis chaque colonnes entre elles
*/

int** format_table_change(int n,int p,int** tab){

    int i,j,k,tmp;

    for(j=0;j<p;j++){

        for(i=0;i<n-1;i++){

            for(k=i+1;k<n;k++){

                if(tab[i][j]>tab[k][j]){

                    tmp=tab[i][j];
                    tab[i][j]=tab[k][j];
                    tab[k][j]=tmp;
                }
            }
        }
    }

    for(j=0;j<p-1;j++){

        for(k=j+1;k<p;k++){

            if(tab[0][j]>tab[0][k]){

                for(i=0;i<n;i++){

                    tmp=tab[i][j];
                    tab[i][j]=tab[i][k];
                    tab[i][k]=tmp;
                }
            }

            if(tab[0][j]==tab[0][k]){

                if(tab[1][j]>tab[1][k]){

                    for(i=0;i<n;i++){

                        tmp=tab[i][j];
                        tab[i][j]=tab[i][k];
                        tab[i][k]=tmp;
                    }
                }
            }
        }
    }
    return tab;
}

/*
*   entr�e: n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau a afficher
*           fichier:fichier dans le quel effectuer l'affichage
*
*   sortie: rien
*/
void print_tab(int n,int p,int** tab,FILE* fichier){
    int i,j,tmp;

    for(i=0;i<n;i++){

        for(j=0;j<p;j++){

            if(tab[i][j]==0)
                tmp=p-j;

            fprintf(fichier," %d ",tab[i][j]);
        }

        fprintf(fichier," col:%d",tmp);
        fprintf(fichier,"\n");
    }

    fprintf(fichier,"\n");

    tab=format_table_change(n,p,tab);

    for(j=0;j<p;j++){

        for(i=0;i<n;i++){

            fprintf(fichier," %d ",tab[i][j]);
        }
        fprintf(fichier,"\n");
    }
    fprintf(fichier,"\n");
}

///////////////////////////////////////////////////////////////////////////////
//////////////////////// TRAITEMENT ///////////////////////////////////////////

/*
*   entr�e: tab_inc: tableau a remplir
*           n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau support
*
*   sortie: tableau trait�
*   utilit�: fait correspondre un tableau d'incidence � un tableau contenant toutes les droites.
*/

int** fill_inc_tab(int** tab_inc,int n,int p,int** tab){

    int i,j;

    for(i=0;i<n;i++){

        for(j=0;j<p;j++){

            tab_inc[j][(tab[i][j])]=1;
        }
    }

    return tab_inc;
}

/*
*   entr�e: lin:derniere ligne fixe pour la recherche
*           n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau a traiter
*
*   sortie: entier donnant le nombre de tableau trouv�
*   utilit�: trouve les combinaison de droite correspondant � la taille du tableau et les affiches dans un fichier
*/

int fill_tab_multiple(int ind, int n, int p, int** tab,FILE* fichier){

    int i,j,c,nb_tab=0;
    int col[n];

    for(i=0;i<n;i++){

        col[i]=-1;
    }

    while(col[ind]<p){

        for(i=0;i<n;i++){

            for(j=0;j<p;j++){

                c=(p+(j-col[i]))%p;
                tab[i][j]=c;
            }
            if(!check_c(c,i,j-1,n,p,tab)){

                col[i]--;
                set_line(i,p,tab);

                if(abs(col[i])>p){

                    col[i]=-1;
                    col[i-1]--;
                    i--;

                    if(i==ind-1){

                        return nb_tab;
                    }

                    set_line(i,p,tab);
                }

                i--;
            }
        }

        print_tab(n,p,tab,fichier);
        set_tab(n,p,tab);
        nb_tab++;
        col[i-1]--;
    }

    return nb_tab;
}

/*
*   entr�e: ind:ligne fixe lors de la recherche
*           n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau a traiter
*
*   sortie: tableau trait�
*   utilit�: trouve une combinaison de droite correspondant � la taille du tableau
*/

int **fill_tab_unique(int ind, int n, int p, int** tab){

    int i,j,c;
    int col[n];

    for(i=0;i<n;i++){

        col[i]=-1;
    }

    for(i=0;i<n;i++){

        for(j=0;j<p;j++){

            c=(p+(j-col[i]))%p;
            tab[i][j]=c;
        }
        if(!check_c(c,i,j-1,n,p,tab)){

            col[i]--;
            set_line(i,p,tab);

            if(abs(col[i])>p){

                col[i]=-1;
                col[i-1]--;
                i--;

                if(i==ind-1){

                    return -1;
                }

                set_line(i,p,tab);
            }
            i--;
        }
    }
    return tab;
}

///////////////////////////////////////////////////////////////////////
////////////////////////// RECUPERATION COQ  //////////////////////////

/*
*   entr�e: n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau a traiter
*           fic_induc_coq: fichier permettant l'affichage
*
*   sortie: rien
*   utilit�:rend le code coq format inductif dans le fichier sp�cifi�
*/

void get_in_coq_inductive(int p,int** tab_inc,FILE* fichier_coq_inductive){

    int i,j;

    fprintf(fichier_coq_inductive,"Inductive ind_Point : Set := ");

    for(i=0;i<p;i++){
        if(i==p-1)
            fprintf(fichier_coq_inductive,"p%d.",i);
        else
            fprintf(fichier_coq_inductive,"p%d | ",i);
    }

    fprintf(fichier_coq_inductive,"\n \n");
    fprintf(fichier_coq_inductive,"Inductive ind_line : Set := ");

    for(i=0;i<p;i++){

        fprintf(fichier_coq_inductive,"l%d",i);

        if(i==p-1)
            fprintf(fichier_coq_inductive,".");
        else
            fprintf(fichier_coq_inductive," | ");
    }

    fprintf(fichier_coq_inductive,"\n \n");
    fprintf(fichier_coq_inductive,"Definition Point : Set := ind_Point.\nDefinition Line : Set := ind_line.\n \nDefinition Incid_bool : Point -> Line -> bool := fun P l =>\n match P with\n");

    for(i=0;i<p;i++){

        fprintf(fichier_coq_inductive,"| p%d =>\n\tmatch l with\n\t",i);
        for(j=0;j<p;j++){

            if(tab_inc[j][i]==1){
                    fprintf(fichier_coq_inductive,"| l%d",j);
            }
        }
        fprintf(fichier_coq_inductive,"=> true\n\t");
        fprintf(fichier_coq_inductive,"| _ => false\n\t");
        fprintf(fichier_coq_inductive,"end\n");
    }
    fprintf(fichier_coq_inductive,"end.\n");

    fprintf(fichier_coq_inductive,"Ltac solve_ex_p := first [\n");

    for(i=0;i<p;i++){
        if(i==0)
            fprintf(fichier_coq_inductive,"\t\tsolve_ex p%d\n",i);
        else
            fprintf(fichier_coq_inductive,"\t|\tsolve_ex p%d\n",i);
    }

    fprintf(fichier_coq_inductive,"].\n");

    fprintf(fichier_coq_inductive,"Ltac solve_ex_l := first [\n");

    for(i=0;i<p;i++){
        if(i==0)
            fprintf(fichier_coq_inductive,"\t\tsolve_ex l%d\n",i);
        else
            fprintf(fichier_coq_inductive,"\t|\tsolve_ex l%d\n",i);
    }

    fprintf(fichier_coq_inductive,"].\n");
}

/*
*   entr�e: n:nombre de ligne
*           p:nombre de colonne
*           tab:tableau a traiter
*           fic_incid_coq: fichier permettant l'affichage
*
*   sortie: rien
*   utilit�:rend le code coq format incidence dans le fichier sp�cifi�
*/

void get_in_coq_incidence(int p,int** tab_inc,FILE* fic_incid_coq){

    int i,j;

    fprintf(fic_incid_coq,"Parameter Point: Set.\nParameter");

    for(i=0;i<p;i++){

        fprintf(fic_incid_coq," p%d",i);
    }

    fprintf(fic_incid_coq,": Point.\n \n");
    fprintf(fic_incid_coq,"Parameter Line: Set.\nParameter");

    for(i=0;i<p;i++){

        fprintf(fic_incid_coq," ");
        fprintf(fic_incid_coq,"l%d",i);
    }
    fprintf(fic_incid_coq," : Line.\n \n");

    fprintf(fic_incid_coq,"Parameter Incid : Point -> Line -> Prop.\n \n");

    fprintf(fic_incid_coq,"Axiom is_only_%d_pts : forall P:Point, ",p);

    for(i=0;i<p;i++){

        if(i==p-1)
            fprintf(fic_incid_coq,"{P=p%d}",i);
        else
            fprintf(fic_incid_coq,"{P=p%d}+",i);
    }

    fprintf(fic_incid_coq,".\n \nAxiom is_only_%d_lines : forall P:Line, ",p);

    for(i=0;i<p;i++){

        fprintf(fic_incid_coq,"{P=");
        fprintf(fic_incid_coq,"l%d",i);
        if(i==p-1)
            fprintf(fic_incid_coq,"}.");
        else
            fprintf(fic_incid_coq,"}+");
    }

    fprintf(fic_incid_coq,"\n \nDefinition is_fano_plane ");

    for(i=0;i<p;i++){

        fprintf(fic_incid_coq,"p%d ",i);
    }

    for(i=0;i<p;i++){

        fprintf(fic_incid_coq,"l%d",i);
        fprintf(fic_incid_coq," ");
    }

    fprintf(fic_incid_coq,":=\n");
    fprintf(fic_incid_coq,"(");

    for(i=0;i<p-1;i++){

        for(j=i+1;j<p;j++){
            if(i==p-2)
                fprintf(fic_incid_coq,"~p%d=p%d) /\\ ",i,j);
            else
                fprintf(fic_incid_coq,"~p%d=p%d /\\ ",i,j);
        }
        fprintf(fic_incid_coq,"\n");
    }

    fprintf(fic_incid_coq,"(");
    for(i=0;i<p-1;i++){

        for(j=i+1;j<p;j++){
                    fprintf(fic_incid_coq,"l%d",i);

            fprintf(fic_incid_coq,"<>");
                    fprintf(fic_incid_coq,"l%d",j);

            if(i==p-2)
                fprintf(fic_incid_coq,")");

            fprintf(fic_incid_coq," /\\ ");
        }

        fprintf(fic_incid_coq,"\n");
    }
    fprintf(fic_incid_coq,"(");
    for(i=0;i<p;i++){

        for(j=0;j<p;j++){

            if(tab_inc[j][i]==0)
                fprintf(fic_incid_coq,"~");

            fprintf(fic_incid_coq,"Incid p%d ",i);

            fprintf(fic_incid_coq,"l%d",j);
            if(i==p-1 && j==p-1)
                fprintf(fic_incid_coq,").");
            else
                fprintf(fic_incid_coq," /\\ ");
        }
        fprintf(fic_incid_coq,"\n");
    }

    fprintf(fic_incid_coq," \n");
    fprintf(fic_incid_coq,"Axiom is_fano_plane_inst :  is_fano_plane");

    for(i=0;i<p;i++){

        fprintf(fic_incid_coq," p%d",i);
    }

    for(i=0;i<p;i++){

        fprintf(fic_incid_coq," ");
        fprintf(fic_incid_coq,"l%d",i);
    }

    fprintf(fic_incid_coq,".");
}
///////////////////////////////////////////////////////////////////////
////////////////////////// MAIN ///////////////////////////////////////

int main(int argc, char* argv[])
{
    if(argc==0){

        printf("utilisation: ./main [rang] [o/m] [0-2] <c/d/n>\n");
        exit(-1);
    }
    if(argv[2][0]=='o'){

        if(argc!=5){

            printf("Merci de tout renseigner: ./main pour les conseils.");
            exit(-1);
        }
        if(argv[3][0]<'0' || argv[3][0]>'2'){

            printf("Valeur incorrect");
            exit(-1);
        }
    }
    else if(argv[2][0]=='m'){

        if(argc!=5){

            printf("Merci de tout renseigner: ./main pour les conseils.");
            exit(-1);
        }
        if(argv[3][0]<'0' || argv[3][0]>'2'){

            printf("Valeur incorrect");
            exit(-1);
        }
    }

    double process_time;
    clock_t begin;
    clock_t end;
    int rang=atoi(argv[1]),p,n;
    int** tab;

    p=rang*rang+rang+1;
    n=rang+1;

    tab=creer_tab(n,p);
    tab=set_tab(n,p,tab);

    if(argv[2][0]=='o'){

        int** tab_inc;

        begin = clock();

        char file_name[50];
        FILE* fichier = NULL;
        sprintf(file_name, "pg(2,%d).txt", rang);

        if(argv[3][0]=='0'){

            if((tab=fill_tab_unique(0,n,p,tab))==-1){
                printf("table introuvable!\n");
                exit(-1);
            }
        }
        else if(argv[3][0]=='2'){

            if((tab=fill_tab_unique(2,n,p,tab))==-1){
                printf("table introuvable!\n");
                exit(-1);
            }
        }

        tab_inc=creer_tab(p,p);
        tab_inc=set_tab_to_0(p,p,tab_inc);
        tab_inc=fill_inc_tab(tab_inc,n,p,tab);

        end = clock();
        process_time = (double)(end - begin) / CLOCKS_PER_SEC;

        if(fichier==NULL){
            fichier=fopen(file_name,"w");
        }
        if(fichier==NULL){
            exit(-1);
        }
        else{

                if(!(line_exist(p,tab_inc) && point_exist(p,tab_inc) && three_points(p,tab_inc) && uniqueness(p,tab_inc) && lower_dim(p,tab_inc))){
                    fprintf(fichier,"! TABLE INVALIDE !");
                    exit(-1);
                }
                else{
                    fprintf(fichier," TABLE VALIDE ");
                    fprintf(fichier,"processing time: %f \n \n",process_time);
                    print_tab(n,p,tab,fichier);
                    print_tab_inc(p,p,tab_inc,fichier);
                }
                if(argv[4][0]=='c'){

                    FILE* fic_incid_coq = NULL;
                    FILE* fic_induc_coq = NULL;

                    char file_inductive_coq[50];
                    char file_incidence_coq[50];

                    sprintf(file_inductive_coq,"coq_pg(2,%d)_induc.txt",rang);
                    sprintf(file_incidence_coq,"coq_pg(2,%d)_incid.txt",rang);

                    if(fic_induc_coq==NULL && fic_incid_coq==NULL){

                        fic_induc_coq=fopen(file_inductive_coq,"w");
                        fic_incid_coq=fopen(file_incidence_coq,"w");
                    }

                    if(fic_induc_coq==NULL || fic_incid_coq==NULL){
                        exit(-1);
                    }
                    else{

                        get_in_coq_incidence(p,tab_inc,fic_incid_coq);
                        get_in_coq_inductive(p,tab_inc,fic_induc_coq);

                        fclose(fic_incid_coq);
                        fclose(fic_induc_coq);

                        fic_incid_coq=NULL;
                        fic_induc_coq=NULL;
                    }
                }
            if(argv[4][0]=='d'){

                FILE* fic_desargue=NULL;
                char file_desargue[50];
                sprintf(file_desargue,"desargue_data_pg(2,%d).txt",rang);

                if(fic_desargue==NULL){

                    fic_desargue=fopen(file_desargue,"w");
                }
                if(fic_desargue==NULL){

                    exit(-1);
                }
                else{

                    begin=clock();
                    if(argv[4][1]=='s'){
                        if(is_desargue_quick(p,tab_inc,fic_desargue)){
                            fprintf(fichier,"Desargue valide\n");
                        }
                    }else{
                        if(is_desargue(p,tab_inc,fic_desargue)){
                            fprintf(fichier,"Desargue valide\n");
                        }
                    }
                    end=clock();
                    process_time = (double)(end - begin) / CLOCKS_PER_SEC;

                    fprintf(fic_desargue,"process-time: %f",process_time);

                    fclose(fic_desargue);
                    fic_desargue=NULL;
                }
            }

            fclose(fichier);
            fichier=NULL;
        }
        free_tab(p,tab_inc);
    }

    else{

        int nb_tab;

        begin = clock();
        if(argv[3][0]=='0'){

            FILE* fic_mult_0 = NULL;
            char file_multiple_0[50];
            sprintf(file_multiple_0,"all_pg(2,%d)_fixe_0.txt",rang);

            if(fic_mult_0==NULL){
                fic_mult_0=fopen(file_multiple_0,"w+");
            }

            if(fic_mult_0==NULL){
                exit(-1);
            }
            else{
                fseek(fic_mult_0,50,SEEK_SET);
                nb_tab=fill_tab_multiple(0,n,p,tab,fic_mult_0);

                //are_same_plane(nb_tab, rang, fic_mult_0);

                if(argv[4][0]=='d'){

                    FILE* fic_out=NULL;
                    char file_out[50];
                    sprintf(file_out,"desargue_for_all_pg(2,%d).txt",rang);

                    if(fic_out==NULL){

                        fic_out=fopen(file_out, "w");
                    }
                    if(fic_out==NULL){

                        exit(-1);
                    }
                    else{
                        if(argv[4][1]=='s'){
                            desargue_multiple(1,nb_tab , rang, fic_mult_0, fic_out);
                        }else{
                            desargue_multiple(0,nb_tab , rang, fic_mult_0, fic_out);
                        }
                        fclose(fic_out);
                        fic_out=NULL;
                    }
                }

                end = clock();
                process_time = (double)(end - begin) / CLOCKS_PER_SEC;

                fseek(fic_mult_0,0,SEEK_SET);
                fprintf(fic_mult_0,"nombre de table: %d\n",nb_tab);
                fprintf(fic_mult_0,"process time: %f s\n \n",process_time);

                fclose(fic_mult_0);
                fic_mult_0=NULL;
            }
        }
        else if(argv[3][0]=='1'){

            FILE* fic_mult_1 = NULL;
            char file_multiple_1[50];
            sprintf(file_multiple_1,"all_pg(2,%d)_fixe_1.txt",rang);

            if(fic_mult_1==NULL){
                fic_mult_1=fopen(file_multiple_1,"w+");
            }

            if(fic_mult_1==NULL){
                exit(-1);
            }
            else{

                fseek(fic_mult_1,50,SEEK_SET);
                nb_tab=fill_tab_multiple(1,n,p,tab,fic_mult_1);

                //are_same_plane(nb_tab, rang, fic_mult_1);

                if(argv[4][0]=='d'){

                    FILE* fic_out=NULL;
                    char file_out[50];
                    sprintf(file_out,"desargue_for_all_pg(2,%d).txt",rang);

                    if(fic_out==NULL){

                        fic_out=fopen(file_out, "w");
                    }
                    if(fic_out==NULL){

                        exit(-1);
                    }
                    else{

                        if(argv[4][1]=='s'){
                            desargue_multiple(1,nb_tab , rang, fic_mult_1, fic_out);
                        }else{
                            desargue_multiple(0,nb_tab , rang, fic_mult_1, fic_out);
                        }

                        fclose(fic_out);
                        fic_out=NULL;
                    }
                }

                end = clock();
                process_time = (double)(end - begin) / CLOCKS_PER_SEC;

                fseek(fic_mult_1,0,SEEK_SET);
                fprintf(fic_mult_1,"nombre de table: %d\n",nb_tab);
                fprintf(fic_mult_1,"process time: %f s\n \n",process_time);

                fclose(fic_mult_1);
                fic_mult_1=NULL;
            }
        }
        else{

            FILE* fic_mult_2 = NULL;
            char file_multiple_2[50];
            sprintf(file_multiple_2,"all_pg(2,%d)_fixe_2.txt",rang);

            if(fic_mult_2==NULL){
                fic_mult_2=fopen(file_multiple_2,"w+");
            }

            if(fic_mult_2==NULL){
                exit(-1);
            }
            else{

                fseek(fic_mult_2,50,SEEK_SET);
                nb_tab=fill_tab_multiple(2,n,p,tab,fic_mult_2);

                //are_same_plane(nb_tab, rang, fic_mult_2);

                if(argv[4][0]=='d'){

                    FILE* fic_out=NULL;
                    char file_out[50];
                    sprintf(file_out,"desargue_for_all_pg(2,%d).txt",rang);

                    if(fic_out==NULL){

                        fic_out=fopen(file_out, "w");
                    }
                    if(fic_out==NULL){

                        exit(-1);
                    }
                    else{

                        if(argv[4][1]=='s'){
                            desargue_multiple(1,nb_tab , rang, fic_mult_2, fic_out);
                        }else{
                            desargue_multiple(0,nb_tab , rang, fic_mult_2, fic_out);
                        }

                        fclose(fic_out);
                        fic_out=NULL;
                    }
                }

                end = clock();
                process_time = (double)(end - begin) / CLOCKS_PER_SEC;

                fseek(fic_mult_2,0,SEEK_SET);
                fprintf(fic_mult_2,"nombre de table: %d\n",nb_tab);
                fprintf(fic_mult_2,"process time: %f s\n \n",process_time);

                fclose(fic_mult_2);
                fic_mult_2=NULL;
            }
        }
    }

    free_tab(n,tab);

    return 0;
}
