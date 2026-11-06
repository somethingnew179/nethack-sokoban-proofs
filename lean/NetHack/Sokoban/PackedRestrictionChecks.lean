/- A bitwise checker for the existing restriction certificate rows. Its
soundness theorem returns the ORIGINAL restrictionCheck, so all existing
semantic System/Model theorems and proof boundaries remain applicable. -/
import NetHack.Sokoban.PackedMasksChecks

namespace NetHack.Sokoban.PackedRestrictionChecks
open DecisionDAG DecisionDAGTransform PackedMasks

structure RawRow where
  original : Nat
  yes : Nat
  no : Nat
  output : Nat
  rule : RestrictionRule

def materialize (cells : List Cell) (row : RawRow) : RestrictionRow :=
  ⟨⟨cube cells row.yes row.no,row.original,row.output⟩,row.rule⟩

def check (read : Nat → Node) (cells : List Cell) (rows : Nat → RawRow) (index : Nat) : Bool :=
  let row := rows index
  match row.rule with
  | .same => decide (row.output = row.original)
  | .selected bit child =>
    match read row.original with
    | .literal _ => false
    | .branch cell low high =>
      decide (low < row.original ∧ high < row.original ∧ child < index ∧
        (cell,bit) ∈ cube cells row.yes row.no ∧
        (rows child).original = (if bit then high else low) ∧ (rows child).output = row.output) &&
      PackedMasksChecks.subsetCheck (rows child).yes (rows child).no row.yes row.no
  | .branch left right =>
    match read row.original with
    | .literal _ => false
    | .branch cell low high =>
      decide (low < row.original ∧ high < row.original ∧ left < index ∧ right < index ∧
        (rows left).original = low ∧ (rows right).original = high) &&
      PackedMasksChecks.subsetCheck (rows left).yes (rows left).no row.yes row.no &&
      PackedMasksChecks.subsetCheck (rows right).yes (rows right).no row.yes row.no &&
      joinCheck read row.output cell (rows left).output (rows right).output

/-- Every successful packed check proves exactly the old checker result.
Mask disjointness/inclusion are discharged by kernel-checked bit operations,
and their list meaning follows from PackedMasksChecks.subset_sound. -/
theorem checked_sound (read : Nat → Node) (cells : List Cell) (rows : Nat → RawRow) (index : Nat)
    (checked : check read cells rows index = true) :
    restrictionCheck read (fun i => materialize cells (rows i)) index = true := by
  cases rule : (rows index).rule with
  | same => simpa only [check,rule,restrictionCheck,materialize] using checked
  | selected bit child =>
    cases code : read (rows index).original with
    | literal value => simp only [check,rule,code,Bool.false_eq_true] at checked
    | branch cell low high =>
      have data := checked
      simp only [check,rule,code,Bool.and_eq_true_iff,decide_eq_true_eq] at data
      have subset := PackedMasksChecks.subset_sound cells (rows child).yes (rows child).no
        (rows index).yes (rows index).no data.2
      simp only [restrictionCheck,materialize,rule,code,decide_eq_true_eq]
      exact ⟨data.1.1,data.1.2.1,data.1.2.2.1,data.1.2.2.2.1,subset,
        data.1.2.2.2.2.1,data.1.2.2.2.2.2⟩
  | branch left right =>
    cases code : read (rows index).original with
    | literal value => simp only [check,rule,code,Bool.false_eq_true] at checked
    | branch cell low high =>
      have data := checked
      simp only [check,rule,code,Bool.and_eq_true_iff,decide_eq_true_eq] at data
      have subsetLeft := PackedMasksChecks.subset_sound cells (rows left).yes (rows left).no
        (rows index).yes (rows index).no data.1.1.2
      have subsetRight := PackedMasksChecks.subset_sound cells (rows right).yes (rows right).no
        (rows index).yes (rows index).no data.1.2
      have facts := data.1.1.1
      simp only [restrictionCheck,materialize,rule,code,Bool.and_eq_true_iff,decide_eq_true_eq]
      exact ⟨⟨facts.1,facts.2.1,facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2.1,
        facts.2.2.2.2.2,subsetLeft,subsetRight⟩,data.2⟩

end NetHack.Sokoban.PackedRestrictionChecks
