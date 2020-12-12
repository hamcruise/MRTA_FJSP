int nTask = ...;
int nAgent= ...;
int nSubtask= ...;
	
range Locs = 1..nTask;
range Agents = 1..nAgent;
int StkIdx=1;
int Dist[1..100][1..100]=...;

tuple t_task {
key int t;    
key int s;
key int l; //location
    int delay;} {t_task} Tasks   = ...;
int sLast[j in 1..nTask] = max(t in Tasks: j==t.t) t.s;

tuple t_mode {
key int t;    
key int s;
key int a; 
    int pt;} {t_mode} Modes =...;

tuple t_prec {
key int t1;    
key int s1;
key int t2;    
key int s2;
key int a;
} 
{t_prec} Prec = { <m1.t, m1.s, m2.t, m2.s, m1.a> |m1, m2 in Modes: m1.a==m2.a && m1!=m2};

tuple t_wait {
key int t1;    
key int s1;
key int t2;    
key int s2;
    int w;} {t_wait} Waits =...;

tuple t_deadline {
key int t1;    
key int s1;
key int t2;    
key int s2;
    int d;} {t_deadline} Deadlines =...;
    
int L= sum(md in Modes) md.pt*3;
   
dvar boolean X[Modes];
dvar boolean Z[Prec];
dvar int+ F[Modes];
dvar int+ S[Modes];
dvar int+ Ft[Tasks];
dvar int+ St[Tasks];//start of task
dvar boolean Y[Tasks][Tasks];
dexpr int Cmax = max(md in Modes:md.s==sLast[md.t]) F[md]; 
//MIP results always are larger than true optimal.
execute  { cplex.tilim = 30*60; cplex.epagap=0;}
minimize  Cmax; 
subject to {
/*
forall (md in Modes: md.t==1 && md.s==1 && md.a==1) X[md]==1;
*/
   forall (T in Tasks)
     sum(md in Modes: T.t==md.t && T.s==md.s) X[md] ==1;
   forall (md in Modes)
     S[md] + F[md] <= L * X[md]; 
   forall (md in Modes)
     F[md] >= S[md] + md.pt + L * (X[md]-1);     
   forall (T1,T2 in Tasks, md1, md2 in Modes, pr in Prec : pr.t1 < pr.t2 && md1.a == pr.a && md1.a==md2.a && 
           md1.t==pr.t1 && md1.s==pr.s1 && md2.t==pr.t2 && md2.s==pr.s2 &&
           T1.t==md1.t && T1.s==md1.s && T2.t==md2.t && T2.s==md2.s) {
     S[md1] >= F[md2] - L * (3-Z[pr]-X[md1]-X[md2]) + Dist[T2.l][T1.l];   //Z[pr] X[md1] X[md2] all 1 then activate
     S[md2] >= F[md1] - L * Z[pr]  + Dist[T1.l][T2.l];
     }    

   forall (T in Tasks) St[T]>= Dist[1][T.l];
    
   forall (T in Tasks) {
		Ft[T]==sum(md in Modes: T.t==md.t && T.s==md.s) F[md];
		St[T]==sum(md in Modes: T.t==md.t && T.s==md.s) S[md];
	}		
 
   //precedence relationships between the operations of a job     
   forall (t1,t2 in Tasks: t2.s>=2 && t1.t==t2.t && t1.s==t2.s-1)
        sum(md2 in Modes: t2.t==md2.t && t2.s==md2.s)   S[md2] >= 
        sum(md1 in Modes: t2.t==md1.t && t2.s-1==md1.s) F[md1] + t1.delay; //Self-suspension constraints  
 
   //Wait constraint: t2 starts at least W time units after t1 ends 
   forall (w in Waits)
        sum(md2 in Modes: w.t2==md2.t && w.s2==md2.s)  S[md2] >= 
        sum(md1 in Modes: w.t1==md1.t && w.s1==md1.s)  F[md1] + w.w; 
           	
  //Deadline constraint: maximum time between the start time of t1 and the finish time of t2
  //cannot confirm 
  forall (d in Deadlines)
        sum(md2 in Modes: d.t2==md2.t && d.s2==md2.s)   F[md2] <= 
        sum(md1 in Modes: d.t1==md1.t && d.s1==md1.s)   S[md1] + d.d;  
 
  //Spatial proximity   
  forall (t1, t2 in Tasks: t1!=t2 && (t1.l+1==t2.l || t1.l==t2.l || t1.l-1==t2.l )) 
        Ft[t1] <= St[t2] + L * (1-Y[t1][t2]);
  forall (t1, t2 in Tasks: t1!=t2 && (t1.l+1==t2.l || t1.l==t2.l || t1.l-1==t2.l )) 
        Ft[t2] <= St[t1] + L * (Y[t1][t2]);
        
}

execute {
  writeln("task"+"\t"+"sub"+"\t"+"agent"+"\t"+ "s"+"\t"+ "e"+"\t"+ "pt");
  for (var md in Modes) 
	if(X[md]==1)  
      writeln(md.t + "\t" + md.s +"\t"+ md.a +"\t"+ S[md]  +"\t"+ F[md]+"\t" + 
             md.pt);
}