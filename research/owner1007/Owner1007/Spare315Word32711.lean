import Owner1007.Spare315Cap32711
namespace Owner1007.Spare315Word32711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem at_most_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) : ownPushes [315] outcomes≤2 := by
 have ledger := survivor_energy logged completed 315 (Spare315Cap32711.survives logged completed cheap)
 have initial : value soko1_1.initial [315]=0 := by decide +kernel
 have modes := (Budget32711.modes logged completed cheap).2
 have restCap : energy soko1_1.initial final UpperBudget11.Rest outcomes≤2 := by rcases modes with mode|mode|mode <;> omega
 have compare := energy_subset (Trace.nil soko1_1.initial) logged [315] UpperBudget11.Rest
   (by decide) (by decide) (by decide) (by decide) (by decide)
 rw [initial] at ledger
 simp only [Int.ofNat_eq_natCast] at ledger
 omega

theorem one_from_neighbor {state dirs final pushes moves outcomes cell}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (member : cell∈([314,316] : List Cell))
 (holesInside : state.holes⊆soko1_1.initial.holes)
 (bound : ownPushes [cell] outcomes≤1) :
 ∃dest,dest∈([314,315,316,317] : List Cell) ∧endGroup [cell] outcomes=[dest] := by
 rcases first_cut_or_quiet (paid:=Gate265Markers11.firstPaid cell) logged [cell] with found|quiet
 ·obtain ⟨cut⟩ := found
  have fixed := cut.before.fixed (by simp :cell∈[cell]) (by intro dir;rfl)
  have tag := no_push_unchanged [cell] cut.beforeOutcomes fixed
  obtain ⟨source,owner,metadata,same⟩ := cut.headPaid
  change source=cell at same
  subst source
  obtain ⟨dest,landed,target⟩ := LeftEnergy11.push_landing cut.headChecked metadata
  have checked : ([314,316] : List Cell).all (fun c=>allDirs.all (fun dir=>
      (pushTargets soko1_1.board c dir).all (fun dest=>decide (pushTargets soko1_1.board c dir=[dest] ∧dest∈([315,317] : List Cell)))))=true := by decide +kernel
  have row := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked cell member) cut.direction (Geometry.all_directions cut.direction)) dest target)
  have noHole : dest∉soko1_1.initial.holes := by
   rcases List.mem_cons.mp row.2 with rfl|later
   ·decide
   ·have eq := List.mem_singleton.mp later
    subst dest
    decide
  have currentHoles := List.Subset.trans cut.before.logged.trace.holes_sublist.subset holesInside
  have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata row.1 noHole currentHoles
  rw [cut.outcomesEq,ownPushes_append,tag,fixed] at bound
  simp only [ownPushes,headEq,ownPush,if_pos (by simp :cell∈[cell]),update,move,post,List.erase_cons_head,Nat.zero_add] at bound
  have tailZero : ownPushes [dest] cut.afterOutcomes=0 := by omega
  have tailTag := no_push_unchanged [dest] cut.afterOutcomes tailZero
  have finalTag : endGroup [cell] outcomes=[dest] := by
   rw [cut.outcomesEq,endGroup_append,tag]
   change endGroup (update [cell] cut.headOutcome) cut.afterOutcomes=[dest]
   rw [headEq]
   simpa only [update,move,if_pos (by simp :cell∈[cell]),post,List.erase_cons_head] using tailTag
  have inside : dest∈([314,315,316,317] : List Cell) := (show ([315,317] : List Cell)⊆[314,315,316,317] from by decide) row.2
  exact ⟨dest,inside,finalTag⟩
 ·have fixed := quiet.fixed (by simp :cell∈[cell]) (by intro dir;rfl)
  exact ⟨cell,(show ([314,316] : List Cell)⊆[314,315,316,317] from by decide) member,no_push_unchanged _ _ fixed⟩

theorem final_tag {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) :
 ∃cell,cell∈([314,315,316,317] : List Cell) ∧endGroup [315] outcomes=[cell] := by
 rcases first_cut_or_quiet (paid:=Gate265Markers11.firstPaid 315) logged [315] with found|quiet
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
  have bound := at_most_two logged completed cheap
  rw [cut.outcomesEq,ownPushes_append,tag,fixed] at bound
  simp only [ownPushes,headEq,ownPush,if_pos (by decide :315∈([315] : List Cell)),update,move,post,List.erase_cons_head,Nat.zero_add] at bound
  have tailBound : ownPushes [dest] cut.afterOutcomes≤1 := by omega
  have headLog := Logged.cons cut.headChecked cut.headEffect cut.after
  have currentHoles := headLog.trace.holes_sublist.subset
  have holesAfter := (step_holes_sublist _ _ _ _ cut.headChecked).subset
  have allHoles := List.Subset.trans holesAfter cut.before.logged.trace.holes_sublist.subset
  obtain ⟨last,lastMember,lastTag⟩ := one_from_neighbor cut.after member allHoles tailBound
  have finalTag : endGroup [315] outcomes=[last] := by
   rw [cut.outcomesEq,endGroup_append,tag]
   change endGroup (update [315] cut.headOutcome) cut.afterOutcomes=[last]
   rw [headEq]
   simpa only [update,move,if_pos (by decide :315∈([315] : List Cell)),post,List.erase_cons_head] using lastTag
  exact ⟨last,lastMember,finalTag⟩
 ·have fixed := quiet.fixed (by decide :315∈([315] : List Cell)) (by intro dir;rfl)
  exact ⟨315,by decide,no_push_unchanged _ _ fixed⟩
#print axioms at_most_two
#print axioms one_from_neighbor
#print axioms final_tag
end Owner1007.Spare315Word32711
