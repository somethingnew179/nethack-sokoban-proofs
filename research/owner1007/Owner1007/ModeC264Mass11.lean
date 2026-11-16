import Owner1007.Spare315Cap32711
namespace Owner1007.ModeC264Mass11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- All Rest identities except the original264. -/
def Other : List Cell := [133,135,266,268,293,315,317,321,367]

theorem other_zero {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (rest : energy soko1_1.initial final Rest outcomes≤2)
 (price : 2≤energy soko1_1.initial final [264] outcomes) :
 energy soko1_1.initial final Other outcomes=0 ∧
 energy soko1_1.initial final [264] outcomes=2 := by
 have split := Hero315Frame11.energy_split logged [264] Other (by decide) (by decide)
 have perm : ([264]++Other).Perm Rest := by decide +kernel
 have same := Hero315Frame11.energy_perm perm soko1_1.initial final outcomes
 have nn := energy_nonnegative logged Other (by decide) (by decide)
 omega

theorem gone317 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (left : energy soko1_1.initial final TightSplit11.B outcomes≤4)
 (other : energy soko1_1.initial final Other outcomes=0) :
 endGroup [317] outcomes=[] := by
 by_cases gone : endGroup [317] outcomes=[]
 ·exact gone
 ·have ledger := survivor_energy logged completed 317 gone
  have initial : value soko1_1.initial [317]=0 := by decide +kernel
  rw [initial] at ledger
  have subset := energy_subset (Trace.nil soko1_1.initial) logged [317] Other
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have stationary : ownPushes [317] outcomes=0 := by
    simp only [Int.ofNat_eq_natCast] at ledger
    omega
  have six := LeftSix317Canonical11.pair_six logged completed stationary
  change 6≤energy soko1_1.initial final TightSplit11.B outcomes at six
  omega

/-- With the two Rest units spent by264, a cheap Left4 completion cannot
consume321: all other possible zero-debt survivors have already been ruled out.
Its zero singleton energy therefore forces321 to be stationary throughout. -/
theorem stationary321 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (left : energy soko1_1.initial final TightSplit11.B outcomes≤4)
 (rest : energy soko1_1.initial final Rest outcomes≤2)
 (price : 2≤energy soko1_1.initial final [264] outcomes) :
 ownPushes [321] outcomes=0 := by
 have other := (other_zero logged rest price).1
 have consumed317 := gone317 logged completed left other
 have consumedNegative := Spare315Cap32711.negatives_gone logged completed cheap
 have removed := HeroLedger.Logged.end_append_perm logged (by decide)
   Spare315Cap32711.negative [317] (by decide) (by decide)
 rw [consumedNegative,consumed317] at removed
 have removedNil : endGroup (Spare315Cap32711.negative++[317]) outcomes=[] := by
   exact List.eq_nil_iff_forall_not_mem.mpr (by
     intro c member
     simpa using removed.mem_iff.mp member)
 have discardedPerm : (Spare315Cap32711.negative++[317]).Perm TightSurvivors11.discarded := by decide +kernel
 have discardedGone : endGroup TightSurvivors11.discarded outcomes=[] := by
   have eq := endGroup_perm discardedPerm outcomes
   rw [removedNil] at eq
   exact List.eq_nil_iff_forall_not_mem.mpr (by intro c member;simpa using eq.mem_iff.mpr member)
 have initialPerm : ([315,321]++TightSurvivors11.discarded).Perm soko1_1.initial.boulders := by decide +kernel
 have full := HeroLedger.Logged.end_append_perm logged (by decide) [315,321]
   TightSurvivors11.discarded (by decide) (by decide)
 rw [discardedGone,List.append_nil] at full
 have transported := endGroup_perm initialPerm outcomes
 rw [HeroLedger.Logged.end_all logged] at transported
 have survivors := full.symm.trans transported
 have conservation := logged.trace.conservation
 have empty : final.holes=[] := completed
 rw [empty] at conservation
 change 18+0=final.boulders.length+16 at conservation
 have lengthTwo : (endGroup [315,321] outcomes).length=2 := by have eq:=survivors.length_eq;omega
 have split := HeroLedger.Logged.end_append_perm logged (by decide) [315] [321] (by decide) (by decide)
 have lengths := split.length_eq
 rw [List.length_append] at lengths
 have bound := endGroup_length_le [315] outcomes
 change (endGroup [315] outcomes).length≤1 at bound
 have alive : endGroup [321] outcomes≠[] := by
   intro gone
   rw [gone] at lengths
   change (endGroup [315,321] outcomes).length=(endGroup [315] outcomes).length+0 at lengths
   omega
 have ledger := survivor_energy logged completed 321 alive
 have initial : value soko1_1.initial [321]=0 := by decide +kernel
 rw [initial] at ledger
 have subset := energy_subset (Trace.nil soko1_1.initial) logged [321] Other
   (by decide) (by decide) (by decide) (by decide) (by decide)
 simp only [Int.ofNat_eq_natCast] at ledger
 omega
#print axioms other_zero
#print axioms gone317
#print axioms stationary321
end Owner1007.ModeC264Mass11
