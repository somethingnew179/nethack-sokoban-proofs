import Owner1007.Spare31511
namespace Owner1007.Spare315Word11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem final_tag {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤326) :
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
   have bounded := Spare31511.at_most_one logged completed cheap
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
#print axioms final_tag
end Owner1007.Spare315Word11
