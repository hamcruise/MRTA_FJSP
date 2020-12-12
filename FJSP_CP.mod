using CP;
int nTask = ...;
int nAgent= ...;
int nSubtask= ...;
	
range Locs = 1..nTask;
range Agents = 1..nAgent;
int StkIdx=1;

tuple t_task {
key int task;    
key int sub;
key int loc;
    int delay;} {t_task} Tasks   = ...;
int sLast[j in 1..nTask] = max(t in Tasks: j==t.task) t.sub;

tuple t_mode {
key int task;    
key int sub;
key int agent; 
    int pt;} {t_mode} Modes =...;

int L= sum(md in Modes) md.pt*3;

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
tuple t_D {
	key int l1;
	key int l2;
	int dist;
};
{t_D} D;

int Dist[1..100][1..100]=...;
execute {
for(var l1 in Locs) 
for(var l2 in Locs) 
  if (l1!=l2) D.add(l1, l2, Dist[l1][l2]);
}	   



dvar interval itvTask[Tasks] in 0..L; 
dvar interval itvMode[md in Modes] optional size md.pt;
dvar interval agentInitLoc[Agents] in -1..0 size 1;
dvar sequence seqAgent[a in Agents]
  in append(
	 all(t in Tasks, md in Modes: t.task==md.task && t.sub==md.sub && md.agent == a) itvMode[md],
	 all(d in 1..1) agentInitLoc[a])
  types append(
     all(t in Tasks, md in Modes: t.task==md.task && t.sub==md.sub && md.agent == a) t.loc,
     all(d in 1..1) StkIdx);   
		                           
execute {
  cp.param.NoOverlapInferenceLevel     = "Extended"; //Low Extended
 // cp.param.TemporalRelaxation = "On"; 
  cp.param.Workers = 4;
//  var f = cp.factory;
 // cp.setSearchPhases(f.searchPhase(seqAgent));
 // cp.param.TimeLimit = 600;
  cp.param.LogVerbosity=21;  
}

minimize max(t in Tasks: sLast[t.task]==t.sub) endOf(itvTask[t]);
subject to {
  forall (t in Tasks)
    alternative(itvTask[t],all(md in Modes: t.task==md.task && t.sub==md.sub) itvMode[md]);

  forall (a in Agents) noOverlap(seqAgent[a],D); 
      
  //Self-suspension constraints   
  forall (t1,t2 in Tasks: t1.task==t2.task && t2.sub==1+t1.sub)
   	endBeforeStart(itvTask[t1],itvTask[t2],t1.delay); //
 
  //Wait constraint: t2 starts at least W time units after t1 ends 	
  forall (t1,t2 in Tasks, w in Waits: t1.task!=t2.task && t1.task==w.t1 && t2.task==w.t2 && t1.sub==w.s1 && t2.sub==w.s2)
   	endBeforeStart(itvTask[t1],itvTask[t2],w.w);

  //Deadline constraint: maximum time between the start time of t1 and the finish time of t2
  forall (t1,t2 in Tasks, d in Deadlines: t1.task!=t2.task && t1.task==d.t1 && t2.task==d.t2 && t1.sub==d.s1 && t2.sub==d.s2)
   	endOf(itvTask[t2]) - startOf(itvTask[t1]) <= d.d;   
	
  //Spatial proximity 
  //forall (t1, t2 in Tasks: t1!=t2 && (t1.loc+1==t2.loc || t1.loc==t2.loc || t1.loc-1==t2.loc)) 
  //	overlapLength(itvTask[t1],itvTask[t2])==0;

}


execute {
  writeln("agent"+"\t"+"task"+"\t"+"sub" +"\t"+ "loc" +"\t"+ "pt"+"\t"+ "s"+"\t"+ "e");
  for (var md in Modes) for(t in Tasks) 
	if(itvMode[md].present && t.task==md.task && t.sub==md.sub)  
      writeln(md.agent + "\t" + md.task +"\t"+ md.sub +"\t"+ t.loc +"\t" + md.pt  
        +"\t"+ itvMode[md].start  +"\t"+ itvMode[md].end);
/*
  //Check self-suspension constraints   
  writeln("end"+"\t"+"start"+"\t"+"delta" +"\t"+ "delay");  
  for (t1 in Tasks) for(t2 in Tasks)
    if(t1.task==t2.task && t2.sub==1+t1.sub)
   	   writeln(itvTask[t1].end+ "\t" +itvTask[t2].start+ "\t" + (itvTask[t2].start-itvTask[t1].end)+ "\t"  + t1.delay); //

  //Check Wait constraint: t2 starts at least W time units after t1 ends 	
  writeln("end"+"\t"+"start"+"\t"+"delta" +"\t"+ "wait");  
  for (t1 in Tasks) for(t2 in Tasks) for(w in Waits)
    if(t1.task!=t2.task && t1.task==w.t1 && t2.task==w.t2 && t1.sub==w.s1 && t2.sub==w.s2)
     writeln(itvTask[t1].end+ "\t" +itvTask[t2].start+ "\t" + (itvTask[t2].start-itvTask[t1].end)+ "\t"  + w.w); //

  //Check Deadline constraint: maximum time between the start time of t1 and the finish time of t2
  writeln("end"+"\t"+"start"+"\t"+"delta" +"\t"+ "deadline");  
  for (t1 in Tasks) for(t2 in Tasks) for(d in Deadlines)
    if(t1.task!=t2.task && t1.task==d.t1 && t2.task==d.t2 && t1.sub==d.s1 && t2.sub==d.s2)
     writeln(itvTask[t1].start+ "\t" +itvTask[t2].end+ "\t" + (itvTask[t2].end-itvTask[t1].start)+ "\t"  +d.d); //
*/
}
