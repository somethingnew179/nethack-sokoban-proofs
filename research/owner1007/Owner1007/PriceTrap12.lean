import Owner1007.PricedCorral

namespace Owner1007.PriceTrap12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds

def pocket : List Cell := [105,106,131,132,157]
def locks (i : Fin 3) : List Cell :=
  if i.val = 0 then [133,158,184] else if i.val = 1 then [132,158,184] else []
def region (i : Fin 3) : List Cell :=
  if i.val < 2 then soko1_2.board.floor.filter
    (fun c => !pocket.contains c && !(locks i).contains c) else soko1_2.board.floor
def credit (i : Fin 3) : Int := if i.val = 0 then 11 else if i.val = 1 then 11 else 0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked : PricedCorral.check soko1_2.board soko1_2.initial.holes
    Generated.soko1_2Potential locks region credit = true := by decide +kernel

theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes
    Generated.soko1_2Potential locks region credit :=
  PricedCorral.closed_of_check _ _ _ _ _ _ checked

theorem unique (i : Fin 3) : (locks i).Nodup := by
  have all : (List.finRange 3).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))

/-- Arbitrary completing suffixes must pay11 to escape this three-stone cut. -/
theorem priceTrap {state final : State} {history dirs : List Dir}
    {past pastMoves future futureMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (tail : Trace soko1_2.board state dirs final future futureMoves) (completed : Goal final)
    (outside : state.player ∉ pocket) (inside : [133,158,184] ⊆ state.boulders) :
    11 ≤ Int.ofNat future + Generated.soko1_2Potential.value final -
      Generated.soko1_2Potential.value state := by
  have prefixConserved := reached.conservation
  have suffixConserved := tail.conservation
  have empty : final.holes = [] := completed
  have finalCount : final.boulders.length = 2 := by
    change 20 + state.holes.length = state.boulders.length + 18 at prefixConserved
    rw [empty] at suffixConserved
    simp only [List.length_nil] at suffixConserved
    omega
  have standing : state.player ∉ state.boulders := by
    cases tail with
    | nil =>
      have count := List.Nodup.length_le_of_subset (show ([133,158,184] : List Cell).Nodup by decide +kernel) inside
      simp only [List.length_cons, List.length_nil] at count
      omega
    | cons head rest => exact (step_player_clear _ _ _ _ head).2.2.1
  have playerFloor := reached.player_floor (by decide +kernel)
  have good : PricedCorral.Good locks region 0 state := by
    constructor
    · have noPocket : pocket.contains state.player = false := by simp [outside]
      have noLocks : (locks 0).contains state.player = false := by
        have notMem : state.player ∉ locks 0 := fun h => standing (inside h)
        simp [notMem]
      change state.player ∈ soko1_2.board.floor.filter
        (fun c => !pocket.contains c && !(locks 0).contains c)
      apply List.mem_filter.mpr
      exact ⟨playerFloor, by
        simpa using And.intro outside
          (show state.player ∉ locks 0 from fun h => standing (inside h))⟩
    · exact inside
  obtain ⟨j, finalGood, bound⟩ := PricedCorral.trace_price closed unique
    Generated.soko1_2_potential_valid tail good reached.holes_sublist.subset
  have terminalCount := List.Nodup.length_le_of_subset (unique j) finalGood.2
  rw [finalCount] at terminalCount
  have zero : credit j = 0 := by
    by_cases hz : j.val = 0
    · simp [locks, hz] at terminalCount
    · by_cases ho : j.val = 1
      · simp [locks, hz, ho] at terminalCount
      · simp [credit, hz, ho]
  rw [zero] at bound
  simpa only [credit, Fin.val_zero, ↓reduceIte, Int.add_zero] using bound

/-- This is conditional on encountering the cut; it is not a global lower223. -/
theorem original_conditional_223 {state final : State} {history dirs : List Dir}
    {past pastMoves future futureMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (tail : Trace soko1_2.board state dirs final future futureMoves) (completed : Goal final)
    (outside : state.player ∉ pocket) (inside : [133,158,184] ⊆ state.boulders) :
    223 ≤ past + future := by
  have extra := priceTrap reached tail completed outside inside
  have prefixBound := trace_bound Generated.soko1_2_potential_valid.stepBound reached
  have goalBound := Generated.soko1_2_potential_valid.goalBound final completed
  rw [Generated.soko1_2_initial_potential] at prefixBound
  simp only [Int.ofNat_eq_natCast] at extra prefixBound
  omega

#print axioms checked
#print axioms priceTrap
#print axioms original_conditional_223
end Owner1007.PriceTrap12
