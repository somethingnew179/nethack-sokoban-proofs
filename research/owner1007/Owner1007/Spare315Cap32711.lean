import Owner1007.Budget32711
import Owner1007.Spare31511
namespace Owner1007.Spare315Cap32711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
def negative : List Cell := [133,135,137,139,141,186,188,191,193,212,264,266,268,293,367]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem negatives_gone {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) : endGroup negative outcomes=[] := by
 have modes := (Budget32711.modes logged completed cheap).2
 have caps : energy soko1_1.initial final U6 outcomes≤8 ∧
   energy soko1_1.initial final TightSplit11.B outcomes≤6 ∧energy soko1_1.initial final Rest outcomes≤2 := by
  rcases modes with mode|mode|mode <;> omega
 have goneUpper := Budget32711.upper_gone logged completed caps.1
 have goneLeft := Budget32711.left_gone logged completed caps.2.1
 have goneRest := Budget32711.rest_negative_gone logged completed caps.2.2
 have gone (cell : Cell) (group : List Cell) (member : cell∈group) (groupUnique : group.Nodup)
     (inside : group⊆soko1_1.initial.boulders) (nil : endGroup group outcomes=[]) : endGroup [cell] outcomes=[] := by
  have subset : [cell]⊆group := by simpa using member
  have transported := end_subset_selected logged (by decide) [cell] group (by simp) groupUnique subset inside
  rw [nil] at transported
  exact List.eq_nil_iff_forall_not_mem.mpr (by intro c h;simpa using transported h)
 have cases : negative.all (fun c=>decide (c∈U6∨c∈TightSplit11.B∨c∈TightSurvivors11.negativeRest))=true := by decide +kernel
 apply TightSurvivors11.all_nil logged (by decide) negative (by decide) (by decide)
 intro cell member
 rcases of_decide_eq_true (List.all_eq_true.mp cases cell member) with upper|left|rest
 ·exact gone cell U6 upper (by decide) (by decide) goneUpper
 ·exact gone cell TightSplit11.B left (by decide) (by decide) goneLeft
 ·exact gone cell TightSurvivors11.negativeRest rest (by decide) (by decide) goneRest

theorem survives317_if315_gone {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) (gone315 : endGroup [315] outcomes=[]) :
 endGroup [317] outcomes≠[] := by
 have goneNegative := negatives_gone logged completed cheap
 have others := HeroLedger.Logged.end_append_perm logged (by decide) [315] negative (by decide) (by decide)
 rw [gone315,goneNegative] at others
 have othersNil : endGroup ([315]++negative) outcomes=[] := List.eq_nil_iff_forall_not_mem.mpr (by
  intro c member
  have retained:=others.mem_iff.mp member
  simpa using retained)
 have partition : ([317,321]++([315]++negative)).Perm soko1_1.initial.boulders := by decide +kernel
 have split := HeroLedger.Logged.end_append_perm logged (by decide) [317,321] ([315]++negative) (by decide) (by decide)
 rw [othersNil,List.append_nil] at split
 have transported := endGroup_perm partition outcomes
 rw [HeroLedger.Logged.end_all logged] at transported
 have survivors := split.symm.trans transported
 have conservation := logged.trace.conservation
 have empty : final.holes=[] := completed
 rw [empty] at conservation
 change 18+0=final.boulders.length+16 at conservation
 have lengthTwo : (endGroup [317,321] outcomes).length=2 := by have eq:=survivors.length_eq;omega
 have pair := HeroLedger.Logged.end_append_perm logged (by decide) [317] [321] (by decide) (by decide)
 have lengths := pair.length_eq
 rw [List.length_append] at lengths
 have bound := endGroup_length_le [321] outcomes
 change (endGroup [321] outcomes).length≤1 at bound
 intro gone
 rw [gone] at lengths
 change (endGroup [317,321] outcomes).length=0+(endGroup [321] outcomes).length at lengths
 omega

theorem survives {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) : endGroup [315] outcomes≠[] := by
 intro gone315
 have modes := (Budget32711.modes logged completed cheap).2
 have restCap : energy soko1_1.initial final Rest outcomes≤2 := by rcases modes with mode|mode|mode <;> omega
 have even315 := ConsumedParity11.consumed_even logged completed [315] (by decide) (by decide) gone315
 have moved315 : ownPushes [315] outcomes≠0 := by
  intro fixed
  have tag:=no_push_unchanged [315] outcomes fixed
  rw [gone315] at tag
  contradiction
 have price315 := Spare31511.moved_positive logged moved315
 have two315 : 2≤energy soko1_1.initial final [315] outcomes := by omega
 have compare315 := energy_subset (Trace.nil soko1_1.initial) logged [315] Rest
   (by decide) (by decide) (by decide) (by decide) (by decide)
 have restTwo : energy soko1_1.initial final Rest outcomes=2 := by omega
 have leftFour : energy soko1_1.initial final TightSplit11.B outcomes=4 := by
  rcases modes with mode|mode|mode <;> omega
 have survives317 := survives317_if315_gone logged completed cheap gone315
 have ledger317 := survivor_energy logged completed 317 survives317
 have initial : value soko1_1.initial [317]=0 := by decide +kernel
 rw [initial] at ledger317
 have moved317 : ownPushes [317] outcomes≠0 := by
  intro fixed
  have six := LeftSix317Canonical11.pair_six logged completed fixed
  change 6≤energy soko1_1.initial final TightSplit11.B outcomes at six
  omega
 have pair := Hero315Frame11.energy_split logged [315] [317] (by decide) (by decide)
 change energy soko1_1.initial final [315,317] outcomes=
   energy soko1_1.initial final [315] outcomes+energy soko1_1.initial final [317] outcomes at pair
 have compare := energy_subset (Trace.nil soko1_1.initial) logged [315,317] Rest
   (by decide) (by decide) (by decide) (by decide) (by decide)
 simp only [Int.ofNat_eq_natCast] at ledger317
 omega
#print axioms negatives_gone
#print axioms survives317_if315_gone
#print axioms survives
end Owner1007.Spare315Cap32711
