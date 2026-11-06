/- Bitwise sufficient conditions for the exact existing packed cubes.
This changes certificate checking, never the Sokoban Model or proof profile.
The list-subset result is proved in the ordinary kernel, for arbitrary masks
and cell lists; no external evaluator or native reflection is used. -/
import NetHack.Sokoban.PackedMasks

namespace NetHack.Sokoban.PackedMasksChecks
open PackedMasks DecisionDAGTransform

def subsetCheck (yes no parentYes parentNo : Nat) : Bool :=
  decide ((yes &&& parentYes) = yes ∧ (no &&& parentNo) = no ∧
    (parentYes &&& parentNo) = 0)

theorem bit_subset (mask parent : Nat) (checked : (mask &&& parent) = mask)
    (i : Nat) (selected : mask.testBit i = true) : parent.testBit i = true := by
  have bits := congrArg (fun n => n.testBit i) checked
  simpa [Nat.testBit_and,selected] using bits

theorem disjoint_bit (yes no : Nat) (checked : (yes &&& no) = 0)
    (i : Nat) (negative : no.testBit i = true) : yes.testBit i = false := by
  have bits := congrArg (fun n => n.testBit i) checked
  simpa [Nat.testBit_and,negative] using bits

theorem indexed_subset (cells : List Cell) (i yes no parentYes parentNo : Nat)
    (positive : ∀ j, yes.testBit j = true → parentYes.testBit j = true)
    (negative : ∀ j, no.testBit j = true → parentNo.testBit j = true)
    (disjoint : ∀ j, parentNo.testBit j = true → parentYes.testBit j = false) :
    indexed cells i yes no ⊆ indexed cells i parentYes parentNo := by
  induction cells generalizing i with
  | nil => simp [indexed]
  | cons cell tail ih =>
    have rest := ih (i+1)
    by_cases selected : yes.testBit i = true
    · have parent := positive i selected
      simp only [indexed,selected,parent,↓reduceIte]
      exact List.cons_subset_cons _ rest
    · by_cases rejected : no.testBit i = true
      · have parent := negative i rejected
        have clear := disjoint i parent
        simp only [indexed,selected,rejected,parent,clear,Bool.false_eq_true,↓reduceIte]
        exact List.cons_subset_cons _ rest
      · simp only [indexed,selected,rejected,↓reduceIte]
        cases parent : parentYes.testBit i <;> cases negativeParent : parentNo.testBit i <;>
          simp only [parent,negativeParent,Bool.false_eq_true,↓reduceIte]
        · exact rest
        · exact List.subset_cons_of_subset _ rest
        · exact List.subset_cons_of_subset _ rest
        · exact List.subset_cons_of_subset _ rest

/-- Fast mask checks imply exactly the old list-inclusion premise. The
extra disjointness is a certificate condition, not a restriction on states. -/
theorem subset_sound (cells : List Cell) (yes no parentYes parentNo : Nat)
    (checked : subsetCheck yes no parentYes parentNo = true) :
    cube cells yes no ⊆ cube cells parentYes parentNo := by
  have data : (yes &&& parentYes) = yes ∧ (no &&& parentNo) = no ∧
      (parentYes &&& parentNo) = 0 := of_decide_eq_true checked
  rw [cube_eq_indexed,cube_eq_indexed]
  exact indexed_subset cells 0 yes no parentYes parentNo
    (bit_subset yes parentYes data.1) (bit_subset no parentNo data.2.1)
    (disjoint_bit parentYes parentNo data.2.2)

end NetHack.Sokoban.PackedMasksChecks
