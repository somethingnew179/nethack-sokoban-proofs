/- Small, kernel-checked certificates for the explicit Sokoban model.
External matching/search code proposes tables only. The checker verifies all
static source-to-landing edges; no solver result is an axiom. -/
import NetHack.Sokoban.LowerBounds

namespace NetHack.Sokoban.Certificates

open LowerBounds

/-- Total natural table lookup; the default outside a finite table is zero. -/
def tableAt : List Nat → Cell → Nat
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: tail, index + 1 => tableAt tail index

def tablePotential (debt credit : List Nat) : Potential := {
  boulder := fun cell => -(Int.ofNat (tableAt debt cell))
  hole := fun cell => Int.ofNat (tableAt credit cell) }

theorem tablePotential_nonpositive (debt credit : List Nat) (cell : Cell) :
    (tablePotential debt credit).boulder cell ≤ 0 := by
  simp only [tablePotential, Int.ofNat_eq_natCast]
  omega

/-- Pointwise credit ≤ debt, including the zero default after either list. -/
def dominates : List Nat → List Nat → Bool
  | [], _ => true
  | credit :: credits, [] => (credit == 0) && dominates credits []
  | credit :: credits, debt :: debts => decide (credit ≤ debt) && dominates credits debts

theorem dominates_sound (credits debts : List Nat) (checked : dominates credits debts = true)
    (cell : Cell) : tableAt credits cell ≤ tableAt debts cell := by
  induction credits generalizing debts cell with
  | nil => simp [tableAt]
  | cons credit credits ih =>
    cases debts with
    | nil =>
      simp only [dominates, Bool.and_eq_true, beq_iff_eq] at checked
      cases cell with
      | zero => simp [tableAt, checked.1]
      | succ cell => simpa [tableAt] using ih [] checked.2 cell
    | cons debt debts =>
      simp only [dominates, Bool.and_eq_true, decide_eq_true_eq] at checked
      cases cell with
      | zero => exact checked.1
      | succ cell => exact ih debts checked.2 cell

theorem tablePotential_absorption (debt credit : List Nat)
    (checked : dominates credit debt = true) (cell : Cell) :
    (tablePotential debt credit).boulder cell + (tablePotential debt credit).hole cell ≤ 0 := by
  have bound := dominates_sound credit debt checked cell
  simp only [tablePotential, Int.ofNat_eq_natCast]
  omega

/-- Finite checking covers every board floor source, all eight direction
constructors, and every possible relaxed landing from the source algorithm.
Including impossible diagonal pushes only strengthens the checked condition. -/
def edgesCheck (board : Board) (potential : Potential) : Bool :=
  board.floor.all fun source => allDirs.all fun direction =>
    (pushTargets board source direction).all fun destination =>
      decide (potential.boulder source ≤ 1 + potential.boulder destination)

theorem allDirs_complete (direction : Dir) : direction ∈ allDirs := by
  cases direction <;> simp [allDirs, cardinalDirs]

theorem edgesCheck_sound (board : Board) (potential : Potential)
    (checked : edgesCheck board potential = true)
    (source : Cell) (member : source ∈ board.floor) (direction : Dir)
    (destination : Cell) (landing : destination ∈ pushTargets board source direction) :
    potential.boulder source ≤ 1 + potential.boulder destination := by
  have sources := List.all_eq_true.mp checked
  have directions := List.all_eq_true.mp (sources source member)
  have destinations := List.all_eq_true.mp (directions direction (allDirs_complete direction))
  exact of_decide_eq_true (destinations destination landing)

/-- Soundness of the entire finite certificate, independent of its proposer. -/
theorem valid_of_tables (board : Board) (debt credit : List Nat)
    (absorption : dominates credit debt = true)
    (edges : edgesCheck board (tablePotential debt credit) = true) :
    LowerBounds.Valid board (tablePotential debt credit) := {
  nonpositive := tablePotential_nonpositive debt credit
  absorption := tablePotential_absorption debt credit absorption
  edge := edgesCheck_sound board (tablePotential debt credit) edges }

end NetHack.Sokoban.Certificates
