import Owner1007.Spare315Word11
namespace Owner1007.Spare315Rest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem survives {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (restCap : energy soko1_1.initial final UpperBudget11.Rest outcomes<2) : endGroup [315] outcomes≠[] := by
 have compare := energy_subset (Trace.nil soko1_1.initial) logged [315] UpperBudget11.Rest
   (by decide) (by decide) (by decide) (by decide) (by decide)
 have nn := energy_nonnegative logged [315] (by decide) (by decide)
 intro gone
 have even := ConsumedParity11.consumed_even logged completed [315] (by decide) (by decide) gone
 have zero : energy soko1_1.initial final [315] outcomes=0 := by omega
 have moved : ownPushes [315] outcomes≠0 := by
   intro fixed
   have tag := no_push_unchanged [315] outcomes fixed
   rw [gone] at tag
   contradiction
 have positive := Spare31511.moved_positive logged moved
 omega

theorem at_most_one {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (restCap : energy soko1_1.initial final UpperBudget11.Rest outcomes<2) : ownPushes [315] outcomes≤1 := by
 have survives := survives logged completed restCap
 have ledger := survivor_energy logged completed 315 survives
 have initial : value soko1_1.initial [315]=0 := by decide +kernel
 have compare := energy_subset (Trace.nil soko1_1.initial) logged [315] UpperBudget11.Rest
   (by decide) (by decide) (by decide) (by decide) (by decide)
 rw [initial] at ledger
 simp only [Int.ofNat_eq_natCast] at ledger
 omega
theorem final_tag {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (restCap : energy soko1_1.initial final UpperBudget11.Rest outcomes<2) :
 ∃cell,cell∈([314,315,316] : List Cell) ∧endGroup [315] outcomes=[cell] := by
 by_cases zero : ownPushes [315] outcomes=0
 ·exact ⟨315,by decide,no_push_unchanged [315] outcomes zero⟩
 ·rcases first_cut_or_quiet (paid:=Gate265Markers11.firstPaid 315) logged [315] with found|quiet
  ·obtain ⟨cut⟩ := found
   have fixed := cut.before.fixed (by decide :315∈([315] : List Cell)) (by intro dir;rfl)
   have tag := no_push_unchanged [315] cut.beforeOutcomes fixed
   obtain ⟨source,owner,metadata,same⟩ := cut.headPaid
   change source=315 at same
   subst source
   obtain ⟨dest,member,targets⟩ : ∃dest,dest∈([314,316] : List Cell)∧pushTargets soko1_1.board 315 cut.direction=[dest] := by
    rcases Spare31511.head_ew cut.headChecked metadata with east|west
    ·exact ⟨316,by decide,by rw [east];decide +kernel⟩
    ·exact ⟨314,by decide,by rw [west];decide +kernel⟩
   have noHole : dest∉soko1_1.initial.holes := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> decide
   have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata targets noHole cut.before.logged.trace.holes_sublist.subset
   have bounded := at_most_one logged completed restCap
   rw [cut.outcomesEq,ownPushes_append,tag,fixed] at bounded
   simp only [ownPushes,headEq,ownPush,if_pos (by decide :315∈([315] : List Cell)),update,move,post,List.erase_cons_head,Nat.zero_add] at bounded
   have tailZero : ownPushes [dest] cut.afterOutcomes=0 := by omega
   have tailTag := no_push_unchanged [dest] cut.afterOutcomes tailZero
   have finalTag : endGroup [315] outcomes=[dest] := by
    rw [cut.outcomesEq,endGroup_append,tag]
    change endGroup (update [315] cut.headOutcome) cut.afterOutcomes=[dest]
    rw [headEq]
    simpa only [update,move,if_pos (by decide :315∈([315] : List Cell)),post,List.erase_cons_head] using tailTag
   have memberLarge : dest∈([314,315,316] : List Cell) := (show ([314,316] : List Cell)⊆[314,315,316] from by decide) member
   exact ⟨dest,memberLarge,finalTag⟩
  ·exact False.elim (zero (quiet.fixed (by decide :315∈([315] : List Cell)) (by intro dir;rfl)))
theorem other_capacity {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (restCap : energy soko1_1.initial final UpperBudget11.Rest outcomes<2)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆final.boulders)
 (away : ∀c,c∈group→c∉([314,315,316] : List Cell)) : group.length≤1 := by
 obtain ⟨cell,member,tag⟩ := final_tag logged completed restCap
 have selected := (logged.end_subset (by decide) [315] (by decide) (by decide)).2
 have present : cell∈final.boulders := selected (by rw [tag];simp)
 have absent : cell∉group := fun h=>away cell h member
 have distinct : (cell::group).Nodup := List.nodup_cons.mpr ⟨absent,unique⟩
 have all : cell::group⊆final.boulders := List.cons_subset.mpr ⟨present,inside⟩
 have count := List.Nodup.length_le_of_subset distinct all
 have conservation := logged.trace.conservation
 have empty : final.holes=[] := completed
 rw [empty] at conservation
 change 18+0=final.boulders.length+16 at conservation
 simp only [List.length_cons] at count
 omega


theorem frozen_pair {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)<2)
 (frozen : List Cell) (locked : Locked soko1_1.board frozen)
 (unique : frozen.Nodup) (two : frozen.length=2) (physical : frozen⊆state.boulders)
 (away : ∀c,c∈frozen→c∉([314,315,316]:List Cell)) : False:=by
 have retained:=locked_trace locked last.trace physical
 have cap:=other_capacity (first.append last) completed restCap frozen unique retained away
 omega
#print axioms survives
#print axioms at_most_one
#print axioms final_tag
#print axioms other_capacity
#print axioms frozen_pair
end Owner1007.Spare315Rest11
