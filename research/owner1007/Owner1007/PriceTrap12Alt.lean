import Owner1007.PriceTrap12

namespace Owner1007.PriceTrap12Alt
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
def locks (i : Fin 5) : List Cell :=
  if i.val = 0 then [133,158,184] else
  if i.val = 1 then [132,158,184] else
  if i.val = 2 then [133,158,159,185,210] else
  if i.val = 3 then [132,158,159,185,210] else []
def pocket (i : Fin 5) : List Cell :=
  if i.val = 2 ∨ i.val = 3 then [105,106,131,132,157,184] else [105,106,131,132,157]
def region (i : Fin 5) : List Cell :=
  if i.val < 4 then soko1_2.board.floor.filter
    (fun c => !(pocket i).contains c && !(locks i).contains c) else soko1_2.board.floor
def credit (i : Fin 5) : Int := if i.val < 4 then 11 else 0
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked : PricedCorral.check soko1_2.board soko1_2.initial.holes
    Generated.soko1_2Potential locks region credit = true := by decide +kernel
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes
    Generated.soko1_2Potential locks region credit :=
  PricedCorral.closed_of_check _ _ _ _ _ _ checked
theorem unique (i : Fin 5) : (locks i).Nodup := by
  have all : (List.finRange 5).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
theorem terminal_zero (i : Fin 5) (small : (locks i).length ≤ 2) : credit i = 0 := by
  have all : ∀ i : Fin 5, (locks i).length ≤ 2 → credit i = 0 := by decide +kernel
  exact all i small

theorem family_price {state final : State} {history dirs : List Dir}
    {past pastMoves future futureMoves : Nat} {i : Fin 5}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (tail : Trace soko1_2.board state dirs final future futureMoves) (completed : Goal final)
    (good : PricedCorral.Good locks region i state) (active : credit i = 11) :
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
  obtain ⟨j, finalGood, bound⟩ := PricedCorral.trace_price closed unique
    Generated.soko1_2_potential_valid tail good reached.holes_sublist.subset
  have terminalCount := List.Nodup.length_le_of_subset (unique j) finalGood.2
  rw [finalCount] at terminalCount
  rw [active, terminal_zero j terminalCount] at bound
  simpa only [Int.add_zero] using bound

theorem alt_price {state final : State} {history dirs : List Dir}
    {past pastMoves future futureMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (tail : Trace soko1_2.board state dirs final future futureMoves) (completed : Goal final)
    (outside : state.player ∉ ([105,106,131,132,157,184] : List Cell))
    (inside : [133,158,159,185,210] ⊆ state.boulders) :
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
      have count := List.Nodup.length_le_of_subset
        (show ([133,158,159,185,210] : List Cell).Nodup by decide +kernel) inside
      simp only [List.length_cons, List.length_nil] at count
      omega
    | cons head rest => exact (step_player_clear _ _ _ _ head).2.2.1
  have playerFloor := reached.player_floor (by decide +kernel)
  have good : PricedCorral.Good locks region 2 state := by
    constructor
    · change state.player ∈ soko1_2.board.floor.filter
        (fun c => !(pocket 2).contains c && !(locks 2).contains c)
      apply List.mem_filter.mpr
      exact ⟨playerFloor, by
        have other : state.player ∉ locks 2 := fun h => standing (inside h)
        have outsidePocket : state.player ∉ pocket 2 := by simpa [pocket] using outside
        simpa using And.intro outsidePocket other⟩
    · exact inside
  exact family_price reached tail completed good (by decide +kernel)

theorem original_conditional_223 {state final : State} {history dirs : List Dir}
    {past pastMoves future futureMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (tail : Trace soko1_2.board state dirs final future futureMoves) (completed : Goal final)
    (outside : state.player ∉ ([105,106,131,132,157,184] : List Cell))
    (inside : [133,158,159,185,210] ⊆ state.boulders) : 223 ≤ past + future := by
  have extra := alt_price reached tail completed outside inside
  have prefixBound := trace_bound Generated.soko1_2_potential_valid.stepBound reached
  have goalBound := Generated.soko1_2_potential_valid.goalBound final completed
  rw [Generated.soko1_2_initial_potential] at prefixBound
  simp only [Int.ofNat_eq_natCast] at extra prefixBound
  omega

#print axioms checked
#print axioms alt_price
#print axioms original_conditional_223
end Owner1007.PriceTrap12Alt
