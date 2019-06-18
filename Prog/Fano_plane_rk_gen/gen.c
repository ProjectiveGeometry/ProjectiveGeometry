// program
// ./g xxx.v 40 130

#include<stdio.h>
#include<stdlib.h>

int belongs(int tab[][6], int k, int points_per_line, int v) // checks whether point v belongs to line k
{
  int i,t=1;
  for(i=0;i<points_per_line&&t; i++)
    if (tab[k][i]==v) {t=0;}
  if (t==0) return 1; else return 0;
}

int on_same_line(int tab[][6], int points_per_line, int l, int v, int w, int x)
{
  int i, t=-1;
  for (i=0;i<l&&(t==-1);i++)
    if(belongs(tab,i,points_per_line, v)&&
       belongs(tab,i,points_per_line, w)&&
       belongs(tab,i,points_per_line, x))
      {t=i;}
  if (t==-1) return 0; else return t;
}
  
int* find_line(int i, int tab[][6], int points_per_line, int l) 
{
  int j,k,cpt=0;
  int *line= malloc(sizeof(int[6]));
  for(j=0;j<l;j++)
    for(k=0;k<points_per_line;k++)
      if (tab[j][k]==i)
	{ 
	  line[cpt]=j;
	  cpt++;
	}
  return line;
}

int create_and_write_file(char *in, char *s, int p, int l)
{
  FILE*f=fopen(s,"w");
  int i,j;
  fprintf(f,"Require Export ProjectiveGeometry.Dev.fano_matroid_tactics.\n");
  fprintf(f,"\n");
  fprintf(f,"(** Pg(2,5). **)\n");
  fprintf(f,"\n");
  fprintf(f,"(** To show that our axiom system is consistent we build a finite model. **)\n");


  fprintf(f,"(*****************************************************************************)\n");
  fprintf(f,"\n");

  fprintf(f,"Section s_fanoPlaneModelRkPG25.\n");
  
  fprintf(f, "(* %s: #points = %d, #lines = %d *)\n\n", s, p, l);
  fprintf(f, "Parameter \n");
  for(i=0;i<p;i++)
    fprintf(f," P%d ", i);
  fprintf(f, ": Point.\n\n");

   fprintf(f, "Parameter rk_points : \n");
  for(i=0;i<p;i++)
    {
      fprintf(f,"rk (P%d :: nil) = 1 ",i);
      if(i<p-1)
	fprintf (f," /\\ ");
      else fprintf(f, ".\n\n");
}

  fprintf(f, "Parameter rk_distinct_points : \n");
  for(i=0;i<p;i++)
    for(j=i;j<p;j++)
      {
	if (i!=j)
	  {
	    fprintf(f,"rk (P%d :: P%d :: nil) = 2 ",i,j);
	  }

	if((i==p-2)&&(j==p-1))
	  fprintf(f, ".\n\n");
	else if (i!=j) fprintf (f," /\\ ");

      }
  FILE *f_in =fopen(in,"r");
  int (*tab)[6] = malloc(sizeof(int[p][6]));
  i=-1;
  int nb_points=0;
  int compt=0;
  char ch[4];
  while(fgets(ch,4,f_in))
    {
      if(nb_points!=6)
        {
	  //printf("calcul : %d %d |%s| {%d}\n", compt, nb_points, ch, atoi(ch));
          tab[compt][nb_points]=atoi(ch);
          nb_points++;
        }
      else {nb_points=0;compt++;}
      i++;
    }

  fclose(f_in);
  //for(i=0;i<p;i++)
  //  fprintf(f, "point %d belongs to lines %d %d %d %d %d %d\n",i,tab[i][0], tab[i][1], tab[i][2], tab[i][3], tab[i][4], tab[i][5]);
  int *line;
  fprintf(f, "Parameter rk_lines : ");
  for(i=0;i<l;i++)
    {
      line=find_line(i, tab, 6, l);
      fprintf(f,"rk (P%d :: P%d :: P%d :: P%d :: P%d :: P%d :: nil) = 2 ",line[0],line[1],line[2],line[3],line[4],line[5]);
   
      if(i==l-1)
	fprintf(f, ".\n\n");
      else fprintf (f," /\\ ");

    }

  fprintf(f, "Parameter rk_planes : \n");
  int k;
  int yes=0;
  for(i=0;i<p;i++)
    for(j=i+1;j<p;j++)
	  for(k=j+1;k<p;k++)
	    {
	      if (on_same_line(tab, 6, l, i,j,k))
		{//printf("%d %d and %d are all 3 on line %d\n",i,j,k,on_same_line(tab, 6, l, i,j,k));
		  if(yes==1)
		    {
		      fprintf(f, " /\\ ");
		      yes=0;
		    }
		  fprintf(f, "rk ( P%d :: P%d :: P%d ::nil )= 3",i,j,k); yes=1;}

	      //if((i==p-1)&&(j==p-1)&&(k==p-1)) fprintf(f, ".\n\n");
	    }
  fprintf(f, ".\n\n");

  
  fprintf(f, "Parameter is_only_%d_pts : forall P,\n", p);
  for(i=0;i<p;i++)
    {
      fprintf(f, "{P=P%d}",i);
      if(i==p-1)
	fprintf(f, ".\n\n");
      else
	fprintf(f, "+");
    }

  fprintf(f, " Ltac case_clear_2 P :=\n");
  for(i=0;i<p;i++)
    fprintf(f,"let HP%d:=fresh in ",i);
  fprintf(f, "destruct  (is_only_%d_pts P) as \n", 31);
    for (i=1;i<p;i++)
      {
	fprintf(f,"[");
      }
  fprintf(f,"P%d ", 0);
      for (i=1;i<p;i++)
      {
	fprintf(f,"| HP%d ]",i);
      }
      fprintf(f, "; subst P.\n\n");

  fprintf(f, "Ltac solve_ex_p tac := first [\n");
  for(i=0;i<p;i++)
    {
      if (i!=0) fprintf (f,"| ");
      fprintf(f," tac P%d ",i);
    }
  fprintf(f,"].\n\n");

  fprintf(f, "(* Local Variables: *)\n");
  fprintf(f, "(* coq-prog-name: \"/Users/magaud/.opam/4.06.0/bin/coqtop\" *)\n");
  fprintf(f, "(* coq-load-path: ((\"/Users/magaud/containers/theories\" \"Containers\") (\"/Users/magaud/galapagos/dev/trunk/ProjectiveGeometry/Dev\" \"ProjectiveGeometry.Dev\")) *)\n");
  fprintf(f, "(* suffixes: .v *)\n");
  fprintf(f, "(* End: *)\n");


  fclose(f);
  return 0; 
}


int main(int argc, char *argv[])
{
  if (argc!=5) {printf("usage: %s #points #lines output\n", argv[0]); exit(1);}

  int p = atoi(argv[3]);
  int l = atoi(argv[4]);

  printf("Generating all the required specifications...\n");

  create_and_write_file(argv[1],argv[2], p,l);
  printf("end !\n");
  return 0;
}
