import Owner1007.Locks
import NetHack.Sokoban.Generated.Soko32Potential
import NetHack.Sokoban.NonlinearFacts

namespace Owner1007
open NetHack.Sokoban NetHack.Sokoban.LowerBounds

def debtOf (potential : Potential) (boxes : List Cell) : Int :=
  weightSum (fun cell => -potential.boulder cell) boxes

theorem debtOf_neg (potential : Potential) (boxes : List Cell) :
    debtOf potential boxes = -weightSum potential.boulder boxes := by
  induction boxes with
  | nil => rfl
  | cons c rest ih =>
    change -potential.boulder c + debtOf potential rest =
      -(potential.boulder c + weightSum potential.boulder rest)
    rw [ih]
    omega

/-- A frozen set appearing in the middle of an ORIGINAL trace contributes
its terminal debt in addition to the initial scalar transport bound. -/
theorem frozen_debt_bound {board : Board} {potential : Potential}
    (valid : Valid board potential) {initial state final : State}
    {history dirs : List Dir} {past pastMoves future futureMoves : Nat}
    (reached : Trace board initial history state past pastMoves)
    (tail : Trace board state dirs final future futureMoves) (completed : Goal final)
    (locks : List Cell) (locked : Locked board locks) (unique : locks.Nodup)
    (inside : locks ⊆ state.boulders) :
    potential.value initial + debtOf potential locks ≤ Int.ofNat (past + future) := by
  have stays := locked_trace locked tail inside
  have debts := NonlinearFacts.weightSum_le_of_nodup_subset
    (fun cell => -potential.boulder cell) locks final.boulders
    (fun cell => by have h := valid.nonpositive cell; omega) unique stays
  change debtOf potential locks ≤ debtOf potential final.boulders at debts
  have empty : final.holes = [] := completed
  have endpoint : potential.value final = -debtOf potential final.boulders := by
    rw [debtOf_neg]
    simp [Potential.value, empty, weightSum]
  have prefixBound := LowerBounds.trace_bound valid.stepBound reached
  have suffixBound := LowerBounds.trace_bound valid.stepBound tail
  rw [endpoint] at suffixBound
  simp only [Int.ofNat_eq_natCast, Int.natCast_add] at prefixBound suffixBound ⊢
  omega

abbrev potential32 := Generated.soko3_2Potential

def locks32 : Fin 5 → List Cell
  | 0 => [160,161]
  | 1 => [158,159]
  | 2 => [241,267]
  | 3 => [289,290]
  | 4 => [288,289]

def lockBound32 : Fin 5 → Nat
  | 0 => 141
  | 1 => 137
  | 2 => 153
  | 3 => 149
  | 4 => 147

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem locks32_checked : ∀ i : Fin 5, lockedCheck soko3_2.board (locks32 i) = true := by
  decide +kernel

theorem locks32_unique : ∀ i : Fin 5, (locks32 i).Nodup := by
  decide +kernel

theorem locks32_values : ∀ i : Fin 5,
    134 + debtOf potential32 (locks32 i) = Int.ofNat (lockBound32 i) := by
  decide +kernel

/-- Five compact irreversible-order cuts, with no restriction on trace length,
hole phase, the other stones, or the player's component. -/
theorem lock32_price {state final : State} {history dirs : List Dir}
    {past pastMoves future futureMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    (tail : Trace soko3_2.board state dirs final future futureMoves) (completed : Goal final)
    (i : Fin 5) (inside : locks32 i ⊆ state.boulders) :
    lockBound32 i ≤ past + future := by
  have bound := frozen_debt_bound Generated.soko3_2_potential_valid reached tail completed
    (locks32 i) (locked_of_check _ _ (locks32_checked i)) (locks32_unique i) inside
  rw [Generated.soko3_2_initial_potential, locks32_values i] at bound
  simp only [Int.ofNat_eq_natCast, Int.natCast_add] at bound
  omega

#print axioms lock32_price
end Owner1007
