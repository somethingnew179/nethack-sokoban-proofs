import Owner1007.RightParkedReady11
namespace Owner1007.RightParkedReady11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.RightParkedSix11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Next (i j : Fin 4) (source target : Cell) : Prop :=
 (i.val=0∧j.val=1∧source=187∧target=186)∨
 (i.val=2∧j.val=0∧source=214∧target=213)∨
 (i.val=3∧j.val=1∧source=214∧target=213)
instance (i j : Fin 4) (source target : Cell) : Decidable (Next i j source target):=by unfold Next;infer_instance

theorem after_ready {beforeDirs state beforePushes beforeMoves before dir t outcome dirs final pushes moves outcomes i j source target}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i)
 (west : dir=.west) (headEq : outcome=.push source (.stay target)) (next : Next i j source target) :
 Ready (first.append (Logged.cons head effect (Logged.nil _))) last j:=by
 have ordinary : Matches state t (.push source (.stay target)):=by simpa only [headEq] using effect
 have nextFacts : (update (locks i) outcome).Perm (locks j)∧
  update [184] outcome=[184]∧update [u i] outcome=[u j]∧
  update [189] outcome=[189]∧update [marker i] outcome=[marker j]∧
  update [137] outcome=[137]∧update [139] outcome=[139]∧
  source≠137∧source≠139∧source∈region j:=by
  rw [headEq]
  rcases next with ⟨a,b,rfl,rfl⟩|⟨a,b,rfl,rfl⟩|⟨a,b,rfl,rfl⟩
  ·have sameI : i=0:=Fin.ext a
   have sameJ : j=1:=Fin.ext b
   subst i;subst j;decide +kernel
  ·have sameI : i=2:=Fin.ext a
   have sameJ : j=0:=Fin.ext b
   subst i;subst j;decide +kernel
  ·have sameI : i=3:=Fin.ext a
   have sameJ : j=1:=Fin.ext b
   subst i;subst j;decide +kernel
 have actual:=step_boulders_nodup _ _ _ _ (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1 head
 have physical:=GhostSubset.update_subset _ _ _ effect (locks i) (unique i) ready.physical
 let one : Logged soko1_1.board state [dir] t.state t.pushCost 1 [outcome]:=.cons head effect (.nil _)
 have wholeEq : (before++[outcome])++outcomes=before++outcome::outcomes:=by simp only [List.append_assoc,List.singleton_append]
 have nextTags (cell : Cell) (a b : Cell) (tag : endGroup [cell] before=[a]) (shift : update [a] outcome=[b]) :
  endGroup [cell] (before++[outcome])=[b]:=by rw [endGroup_append,tag];exact shift
 have nextZero (cell : Cell) (z : ownPushes [cell] before=0) (different : source≠cell) :
  ownPushes [cell] (before++[outcome])=0:=by
  rw [ownPushes_append,no_push_unchanged _ _ z,z,headEq]
  have notOwner : source∉[cell]:=by simpa using different
  simp [ownPushes,ownPush,notOwner]
 have nextGone : endGroup (locks j) outcomes=[]:=by
  have gone:=ready.gone
  change endGroup (update (locks i) outcome) outcomes=[] at gone
  have perm:=endGroup_perm nextFacts.1 outcomes
  rw [gone] at perm
  exact List.perm_nil.mp perm.symm
 have prefixPair:=prefix_energy_le first one TightSplit11.A (by decide) (by decide)
 have prefixUpper:=prefix_energy_le first one UpperBudget11.U6 (by decide) (by decide)
 refine ⟨ready.completed,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,nextGone⟩
 ·have cap:=ready.cheap;change beforePushes+t.pushCost+pushes≤327;change beforePushes+(t.pushCost+pushes)≤327 at cap;omega
 ·change energy soko1_1.initial final UpperBudget11.U6 ((before++[outcome])++outcomes)≤6
  rw [wholeEq];exact ready.upper
 ·change energy soko1_1.initial final [186] ((before++[outcome])++outcomes)≤4
  rw [wholeEq];exact ready.left186
 ·change energy soko1_1.initial final [212] ((before++[outcome])++outcomes)≤2
  rw [wholeEq];exact ready.left212
 ·change energy soko1_1.initial final UpperBudget11.Rest ((before++[outcome])++outcomes)<2
  rw [wholeEq];exact ready.rest
 ·change PaidCount11.count FirstRest18711.paid UpperBudget11.Rest (beforeDirs++[dir]) (before++[outcome])=0
  rw [PaidCount11.append first]
  have noPaid : ¬PaidCount11.owned FirstRest18711.paid (endGroup UpperBudget11.Rest before) dir outcome:=by
   rw [headEq,west];simp [PaidCount11.owned,FirstRest18711.paid]
  simp only [PaidCount11.count,if_neg noPaid,Nat.add_zero,ready.noRest]
 ·exact nextZero 137 ready.zero137 nextFacts.2.2.2.2.2.2.2.1
 ·exact nextZero 139 ready.zero139 nextFacts.2.2.2.2.2.2.2.2.1
 ·exact nextTags 186 184 184 ready.tag186 nextFacts.2.1
 ·exact nextTags 188 (u i) (u j) ready.tag188 nextFacts.2.2.1
 ·exact nextTags 191 189 189 ready.tag191 nextFacts.2.2.2.1
 ·exact nextTags 212 (marker i) (marker j) ready.tag212 nextFacts.2.2.2.2.1
 ·change 2≤energy soko1_1.initial t.state TightSplit11.A (before++[outcome]);have cap:=ready.pairTwo;omega
 ·change 4≤energy soko1_1.initial t.state UpperBudget11.U6 (before++[outcome]);have cap:=ready.upperFour;omega
 ·exact fun c h=>physical (nextFacts.1.mem_iff.mpr h)
 ·rw [ordinary.2];exact nextFacts.2.2.2.2.2.2.2.2.2
#print axioms after_ready
end Owner1007.RightParkedReady11
