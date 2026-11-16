import Owner1007.LeftSix317Canonical11
import Owner1007.HeroEndSubset11
namespace Owner1007.TightSurvivors11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def discarded : List Cell := [133,135,137,139,141,186,188,191,193,212,264,266,268,293,317,367]
def negativeRest : List Cell := [133,135,264,266,268,293,367]
theorem singleton_nil {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆soko1_1.initial.boulders) (bounded : group.length≤18)
 (cap : Int) (budget : energy soko1_1.initial final group outcomes≤cap)
 (cell : Cell) (member : cell∈group) (debt : value soko1_1.initial [cell]< -cap) :
 endGroup [cell] outcomes=[] := by
 by_cases gone : endGroup [cell] outcomes=[]
 · exact gone
 · have ledger := survivor_energy logged completed cell gone
   have subset : [cell]⊆group := by simpa using member
   have bound := energy_subset (Trace.nil soko1_1.initial) logged [cell] group
     (by simp) groupUnique subset inside bounded
   have nn : (0:Int)≤Int.ofNat (ownPushes [cell] outcomes) := Int.ofNat_nonneg _
   omega

theorem all_nil {board initial dirs final pushes moves outcomes}
 (logged : Logged board initial dirs final pushes moves outcomes) (actualUnique : initial.boulders.Nodup)
 (cells : List Cell) (unique : cells.Nodup) (inside : cells⊆initial.boulders)
 (gone : ∀cell∈cells,endGroup [cell] outcomes=[]) : endGroup cells outcomes=[] := by
 induction cells with
 |nil=>exact endGroup_empty outcomes
 |cons c rest ih=>
   have headGone := gone c (by simp)
   have tailGone := ih (List.nodup_cons.mp unique).2 (List.Subset.trans (by simp) inside)
     (fun cell member=>gone cell (List.mem_cons_of_mem _ member))
   have split := HeroLedger.Logged.end_append_perm logged actualUnique [c] rest unique inside
   rw [headGone,tailGone] at split
   exact List.eq_nil_iff_forall_not_mem.mpr (by intro cell member;simpa using split.mem_iff.mp member)

theorem stationary_zero_survivors {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325) :
 ownPushes [315] outcomes=0 ∧ownPushes [321] outcomes=0 := by
 obtain ⟨_,upper,left,rest⟩ := Tight32511.budgets logged completed cheap
 have moved317 := LeftSix317Canonical11.moves317_at325 logged completed cheap
 have gone317 : endGroup [317] outcomes=[] := by
   by_cases gone : endGroup [317] outcomes=[]
   · exact gone
   · have ledger := survivor_energy logged completed 317 gone
     have zero : value soko1_1.initial [317]=0 := by decide +kernel
     have bound := energy_subset (Trace.nil soko1_1.initial) logged [317] UpperBudget11.Rest
       (by decide) (by decide) (by decide) (by decide) (by decide)
     have stationary : ownPushes [317] outcomes=0 := by rw [zero] at ledger;simp only [Int.ofNat_eq_natCast] at ledger;omega
     exact False.elim (moved317 stationary)
 have upperDebts : UpperBudget11.U6.all (fun c=>decide (value soko1_1.initial [c]< -6))=true := by decide +kernel
 have leftDebts : TightSplit11.B.all (fun c=>decide (value soko1_1.initial [c]< -4))=true := by decide +kernel
 have restDebts : negativeRest.all (fun c=>decide (value soko1_1.initial [c]<0))=true := by decide +kernel
 have cases : discarded.all (fun c=>decide (c=317∨c∈UpperBudget11.U6∨c∈TightSplit11.B∨c∈negativeRest))=true := by decide +kernel
 have gone : ∀cell∈discarded,endGroup [cell] outcomes=[] := by
   intro cell member
   have known := of_decide_eq_true (List.all_eq_true.mp cases cell member)
   rcases known with rfl|upperMember|leftMember|restMember
   · exact gone317
   · exact singleton_nil logged completed UpperBudget11.U6 (by decide) (by decide) (by decide) 6 (by omega)
       cell upperMember (of_decide_eq_true (List.all_eq_true.mp upperDebts cell upperMember))
   · exact singleton_nil logged completed TightSplit11.B (by decide) (by decide) (by decide) 4 (by omega)
       cell leftMember (of_decide_eq_true (List.all_eq_true.mp leftDebts cell leftMember))
   · have memberRest : cell∈UpperBudget11.Rest := (show negativeRest⊆UpperBudget11.Rest from by decide) restMember
     exact singleton_nil logged completed UpperBudget11.Rest (by decide) (by decide) (by decide) 0 (by omega)
       cell memberRest (of_decide_eq_true (List.all_eq_true.mp restDebts cell restMember))
 have discardedGone := all_nil logged (by decide) discarded (by decide) (by decide) gone
 have initialPerm : ([315,321]++discarded).Perm soko1_1.initial.boulders := by decide +kernel
 have full := HeroLedger.Logged.end_append_perm logged (by decide) [315,321] discarded (by decide) (by decide)
 rw [discardedGone,List.append_nil] at full
 have transported := endGroup_perm initialPerm outcomes
 rw [HeroLedger.Logged.end_all logged] at transported
 have survivors : (endGroup [315,321] outcomes).Perm final.boulders := full.symm.trans transported
 have conservation := logged.trace.conservation
 have empty : final.holes=[] := completed
 rw [empty] at conservation
 change 18+0=final.boulders.length+16 at conservation
 have totalLength : (endGroup [315,321] outcomes).length=2 := by have h:=survivors.length_eq;omega
 have split := HeroLedger.Logged.end_append_perm logged (by decide) [315] [321] (by decide) (by decide)
 have sumLength := split.length_eq
 rw [List.length_append] at sumLength
 change (endGroup [315,321] outcomes).length=(endGroup [315] outcomes).length+(endGroup [321] outcomes).length at sumLength
 rw [totalLength] at sumLength
 have firstBound := endGroup_length_le [315] outcomes
 have secondBound := endGroup_length_le [321] outcomes
 change (endGroup [315] outcomes).length≤1 at firstBound
 change (endGroup [321] outcomes).length≤1 at secondBound
 have firstSurvives : endGroup [315] outcomes≠[] := by intro h;rw [h] at sumLength;simp only [List.length_nil] at sumLength;omega
 have secondSurvives : endGroup [321] outcomes≠[] := by intro h;rw [h] at sumLength;simp only [List.length_nil] at sumLength;omega
 constructor
 · have ledger := survivor_energy logged completed 315 firstSurvives
   have zero : value soko1_1.initial [315]=0 := by decide +kernel
   have bound := energy_subset (Trace.nil soko1_1.initial) logged [315] UpperBudget11.Rest
     (by decide) (by decide) (by decide) (by decide) (by decide)
   rw [zero] at ledger
   simp only [Int.ofNat_eq_natCast] at ledger
   omega
 · have ledger := survivor_energy logged completed 321 secondSurvives
   have zero : value soko1_1.initial [321]=0 := by decide +kernel
   have bound := energy_subset (Trace.nil soko1_1.initial) logged [321] UpperBudget11.Rest
     (by decide) (by decide) (by decide) (by decide) (by decide)
   rw [zero] at ledger
   simp only [Int.ofNat_eq_natCast] at ledger
   omega
#print axioms stationary_zero_survivors
end Owner1007.TightSurvivors11