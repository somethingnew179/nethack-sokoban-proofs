import sys,itertools
from collections import deque
sys.path.insert(0,'research/owner1007')
from diagnose import Model
m=Model('soko1_1')
local={137,139,187,188,189,190,191,138,164,216,215,214,213,112,111}
zero={137:['east'],139:['west'],187:['east'],188:['east'],189:['east'],191:['west'],138:['north','south'],164:['north','south'],190:['north','south'],216:['west'],215:['west'],214:['west'],213:['north','south'],112:['west'],111:['north']}
opp=dict(north='south',south='north',east='west',west='east')
def locked(cells):
 cells=set(cells)
 for src in cells:
  for d in opp:
   hero=m.adjacent(src,opp[d]);dest=m.adjacent(src,d)
   if hero in m.floor and hero not in cells and dest in m.floor and dest not in m.doors and dest not in cells:return False
 return True
def dead(boxes):
 return next((list(c) for n in [1,2,3] for c in itertools.combinations(sorted(boxes),n) if locked(c)),None)
def key(state):return (tuple(sorted(state[1])),min(m.walks(state)))
start=(190,frozenset([137,139,187,189]),frozenset([9999]));q=deque([(start,[])]);seen={key(start)};edges=0;limit=64;deadlocks={};states=[]
while q:
 state,path=q.popleft();states.append((state,path))
 for source in state[1]:
  for direction in zero.get(source,[]):
   result=m.macros(state,[(source,direction)])
   if result is None:continue
   dest=m.adjacent(source,direction);nextstate,_=result;newpath=path+[(source,direction,dest)];edges+=1
   frozen=dead(nextstate[1])
   if frozen:deadlocks[tuple(frozen)]=deadlocks.get(tuple(frozen),0)+1;continue
   if dest not in local:
    print('LOCAL EXIT',len(seen),'nodes',edges,'edges','path=',newpath,'boxes=',sorted(nextstate[1]));raise SystemExit
   k=key(nextstate)
   if k not in seen:
    if len(seen)>=limit:print('CAPPED',limit,'nodes',edges,'edges','frontier=',newpath,'prunedLocked=',deadlocks);raise SystemExit
    seen.add(k);q.append((nextstate,newpath))
print('LOCAL CLOSURE',len(seen),'nodes',edges,'edges','prunedLocked=',deadlocks)
print('STATICCUTS=',sorted(seen))
print('Diagnostic only:4ghosttokens,15manualwordcells,cap64,allotherboulderserased,uppermustconsume assumption;notoriginalproof')
