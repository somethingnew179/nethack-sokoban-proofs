import Owner1007.FirstAnyFive11Canonical
import Owner1007.Left184Parked21211
import Owner1007.BlockRestNorth11
import Owner1007.ForwardLeftWest11
import Owner1007.Left186TagPrice11
namespace Owner1007.Forward185187Excluded11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem impossible
 {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : beforePushes+pushes<335)
 (upper : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤6)
 (left186 : energy soko1_1.initial final [186] (before++outcomes)≤4)
 (left212 : energy soko1_1.initial final [212] (before++outcomes)≤2)
 (rest : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)<2)
 (noRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest beforeDirs before=0)
 (zero137 : ownPushes [137] before=0) (zero139 : ownPushes [139] before=0)
 (prefixFour : 4≤energy soko1_1.initial state UpperBudget11.U6 before)
 (tag186 : endGroup [186] before=[185]) (tag188 : endGroup [188] before=[187]) (tag191 : endGroup [191] before=[189]) : False := by
 obtain ⟨cut,quietZero,metadata,west,effect⟩:=FirstAnyFive11.canonical_first_west first logged completed upper (by omega) rest
   zero137 zero139 prefixFour tag186 tag188 tag191
 have headEq:=NetHack.Sokoban.GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome (.push 185 (.stay 184)) cut.headEffect effect
 have localZero (cell : Cell) (member : cell∈FirstAnyFive11.K) : ownPushes [cell] cut.beforeOutcomes=0:=by
  apply LeftQuietIdentity11.subset_zero [cell] FirstAnyFive11.K cut.beforeOutcomes
  ·intro c found
   have same:=List.mem_singleton.mp found
   subst c;exact member
  ·exact quietZero
 have localTag (cell : Cell) (member : cell∈FirstAnyFive11.K) :
     endGroup [cell] cut.beforeOutcomes=[cell]:=no_push_unchanged [cell] cut.beforeOutcomes (localZero cell member)
 let current:=first.append cut.before.logged
 have before186 : endGroup [186] (before++cut.beforeOutcomes)=[185]:=by rw [endGroup_append,tag186,localTag 185 (by decide)]
 have two:=Left186TagPrice11.at185_two current before186
 have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
 have four:=ForwardLeftWest11.four current checked cut.headEffect (Logged.nil cut.actor.state) before186 metadata (by decide) two
 let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome]:=
   .cons cut.headChecked cut.headEffect (.nil _)
 let next:=current.append one
 have after186 : endGroup [186] ((before++cut.beforeOutcomes)++[cut.headOutcome])=[184]:=by
  rw [endGroup_append,before186]
  change update [185] cut.headOutcome=[184]
  rw [headEq];decide
 have after188 : endGroup [188] ((before++cut.beforeOutcomes)++[cut.headOutcome])=[187]:=by
  rw [endGroup_append,endGroup_append,tag188,localTag 187 (by decide)]
  change update [187] cut.headOutcome=[187]
  rw [headEq];decide
 have after191 : endGroup [191] ((before++cut.beforeOutcomes)++[cut.headOutcome])=[189]:=by
  rw [endGroup_append,endGroup_append,tag191,localTag 189 (by decide)]
  change update [189] cut.headOutcome=[189]
  rw [headEq];decide
 have before187 : 187∈state.boulders:=
  (first.end_subset (by decide) [188] (by decide) (by decide)).2 (by rw [tag188];simp)
 have localNoRest:=BlockRestNorth11.count_zero cut.before.logged 187 (Or.inl rfl) before187 (localZero 187 (by decide))
   (endGroup UpperBudget11.Rest before)
 have beforeNoRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest
     (beforeDirs++cut.beforeDirs) (before++cut.beforeOutcomes)=0:=by
  rw [PaidCount11.append first,noRest,localNoRest]
 have afterNoRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest
     ((beforeDirs++cut.beforeDirs)++[cut.direction]) ((before++cut.beforeOutcomes)++[cut.headOutcome])=0:=by
  rw [PaidCount11.append current]
  simp [PaidCount11.count,PaidCount11.owned,FirstRest18711.paid,headEq,beforeNoRest]
 have totalEq : (((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)=before++outcomes:=by
  calc
   _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes):=by simp only [List.append_assoc,List.singleton_append]
   _=before++outcomes:=congrArg (fun rest=>before++rest) cut.outcomesEq.symm
 have nextUpper : energy soko1_1.initial final UpperBudget11.U6
     (((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)≤6:=by rw [totalEq];exact upper
 have next186 : energy soko1_1.initial final [186]
     (((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)≤4:=by rw [totalEq];exact left186
 have next212 : energy soko1_1.initial final [212]
     (((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)≤2:=by rw [totalEq];exact left212
 have nextRest : energy soko1_1.initial final UpperBudget11.Rest
     (((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)<2:=by rw [totalEq];exact rest
 have nextCheap : beforePushes+cut.beforePushes+cut.actor.pushCost+cut.afterPushes<335:=by
  have counts:=cut.pushesEq
  omega
 have prefixLeft : 4≤energy soko1_1.initial cut.actor.state [186] ((before++cut.beforeOutcomes)++[cut.headOutcome]):=four
 have hero : cut.actor.state.player=185:=by rw [effect.2]
 exact Left184Parked21211.from_left next cut.after completed nextCheap nextUpper next186 next212 nextRest
   afterNoRest prefixLeft after186 after188 after191 hero
#print axioms impossible
end Owner1007.Forward185187Excluded11
