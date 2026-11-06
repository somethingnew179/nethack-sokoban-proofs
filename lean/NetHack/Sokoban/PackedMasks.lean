/- Linear mask decoding for certificate data, with an ordinary-kernel proof
that it agrees with indexed testBit decoding for every mask and cell list. -/
import NetHack.Sokoban.DecisionDAGTransform
namespace NetHack.Sokoban.PackedMasks
open DecisionDAGTransform

def indexed : List Cell → Nat → Nat → Nat → Bindings
  | [], _, _, _ => []
  | cell :: tail, i, yes, no =>
    if yes.testBit i then (cell, true) :: indexed tail (i+1) yes no
    else if no.testBit i then (cell, false) :: indexed tail (i+1) yes no
    else indexed tail (i+1) yes no

def cube : List Cell → Nat → Nat → Bindings
  | [], _, _ => []
  | cell :: tail, yes, no =>
    if yes % 2 = 1 then (cell, true) :: cube tail (yes/2) (no/2)
    else if no % 2 = 1 then (cell, false) :: cube tail (yes/2) (no/2)
    else cube tail (yes/2) (no/2)

theorem cube_eq_indexed_of_bits (cells : List Cell) (yes no i originalYes originalNo : Nat)
    (yesBits : ∀ j, yes.testBit j = originalYes.testBit (i+j))
    (noBits : ∀ j, no.testBit j = originalNo.testBit (i+j)) :
    cube cells yes no = indexed cells i originalYes originalNo := by
  induction cells generalizing yes no i with
  | nil => rfl
  | cons cell tail ih =>
    have yesHead : decide (yes % 2 = 1) = originalYes.testBit i := by
      simpa only [Nat.testBit_zero, Nat.add_zero] using yesBits 0
    have noHead : decide (no % 2 = 1) = originalNo.testBit i := by
      simpa only [Nat.testBit_zero, Nat.add_zero] using noBits 0
    have nextYes : ∀ j, (yes/2).testBit j = originalYes.testBit (i+1+j) := by
      intro j
      rw [Nat.testBit_div_two, yesBits]
      congr 1
      omega
    have nextNo : ∀ j, (no/2).testBit j = originalNo.testBit (i+1+j) := by
      intro j
      rw [Nat.testBit_div_two, noBits]
      congr 1
      omega
    have next := ih (yes/2) (no/2) (i+1) nextYes nextNo
    simp only [cube, indexed, ← yesHead, ← noHead, decide_eq_true_eq, next]

theorem cube_eq_indexed (cells : List Cell) (yes no : Nat) :
    cube cells yes no = indexed cells 0 yes no :=
  cube_eq_indexed_of_bits cells yes no 0 yes no (by intro j; simp) (by intro j; simp)

def select : List Cell → Nat → List Cell
  | [], _ => []
  | cell :: tail, mask =>
    if mask % 2 = 1 then cell :: select tail (mask/2) else select tail (mask/2)

end NetHack.Sokoban.PackedMasks
