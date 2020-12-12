int nTask = ...;
int nAgent= ...;
int nSubtask= ...;
	
//range Locs = 1..nTask;
//range Agents = 1..nAgent;
//int StkIdx=1;
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
} 
{t_prec} Prec = { <m1.t, m1.s, m2.t, m2.s> |m1, m2 in Tasks: m1!=m2};

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
dvar int+ F[Tasks];
dvar int+ S[Tasks];
//dvar int+ Ft[Tasks];
//dvar int+ St[Tasks];//start of task
//dvar boolean Y[Tasks][Tasks];
dexpr int Cmax = max(T in Tasks:T.s==sLast[T.t]) F[T]; // (1)
//MIP results always are larger than true optimal.
execute  { cplex.tilim = 30*60; cplex.epagap=0;}
minimize  Cmax; 
subject to {

  // (2)
  forall (T in Tasks)
    sum(md in Modes: T.t==md.t && T.s==md.s) X[md] ==1;

  // (3)-1: precedence relationships within same task     
  forall (pr in Prec: pr.s2>=2 && pr.t1==pr.t2 && pr.s1==pr.s2-1)
    Z[pr] == 1;
  // (3)-2: precedence relationships between two jobs    
  forall (w in Waits, pr in Prec: w.t1==pr.t1 && w.s1==pr.s1 && w.t2==pr.t2 && w.s2==pr.s2) 
    Z[pr] == 1;

  // (4)-1: Wait constraint between the operations of a job     
  forall (T1,T2 in Tasks: T2.s>=2 && T1.t==T2.t && T1.s==T2.s-1)
    S[T2] >= F[T1] + T1.delay; //Self-suspension constraints  
  // (4)-2: Wait constraint: t2 starts at least W time units after t1 ends 
  forall (w in Waits, T1, T2 in Tasks: w.t1==T1.t && w.s1==T1.s && w.t2==T2.t && w.s2==T2.s)
    S[T2] >= F[T1] + w.w; 
 
  // (5): Deadline constraint: maximum time between the start time of t1 and the finish time of t2
  // cannot confirm 
  forall (d in Deadlines, T1, T2 in Tasks: d.t1==T1.t && d.s1==T1.s && d.t2==T2.t && d.s2==T2.s)
    F[T2] <= S[T1] + d.d;  
 
  // (7): no (6) and (8)
  forall (T in Tasks, md in Modes: T.t==md.t && T.s==md.s)
      F[T] >= S[T] + md.pt + L * (X[md]-1);

  // (9) Spatial proximity   
  forall (t1, t2 in Tasks, pr in Prec: pr.t1==t1.t && pr.s1==t1.s && pr.t2==t2.t && pr.s2==t2.s && 
          (t1.l+1==t2.l || t1.l==t2.l || t1.l-1==t2.l )) {
      F[t1] <= S[t2] + L * (1-Z[pr]);
      F[t2] <= S[t1] + L * Z[pr];
    }      

  // transportation time        
  forall (T1,T2 in Tasks, md1, md2 in Modes, pr in Prec : pr.t1 < pr.t2 && md1.a==md2.a && 
          md1.t==pr.t1 && md1.s==pr.s1 && md2.t==pr.t2 && md2.s==pr.s2 &&
          T1.t==md1.t && T1.s==md1.s && T2.t==md2.t && T2.s==md2.s) {
    S[T2] >= F[T1] + L * (X[md1]+X[md2]+Z[pr]-3) + Dist[T1.l][T2.l];
    S[T1] >= F[T2] + L * (X[md1]+X[md2]-Z[pr]-2) + Dist[T2.l][T1.l];
    }    

  // default transportation time   
  forall (T in Tasks) S[T]>= Dist[1][T.l];
}
    
execute {
  writeln("task"+"\t"+"sub"+"\t"+"agent"+"\t"+ "s"+"\t"+ "e"+"\t"+ "pt");
  for (var md in Modes) for(var T in Tasks) 
	if(X[md]==1) 
	  if(md.t == T.t) 
	    if(md.s == T.s)  
          writeln(md.t + "\t" + md.s +"\t"+ md.a +"\t"+ S[T]  +"\t"+ F[T]+"\t" + 
             md.pt);
}
