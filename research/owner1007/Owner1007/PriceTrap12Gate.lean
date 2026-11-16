import Owner1007.PriceTrap12

namespace Owner1007.PriceTrap12Gate
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
def locks (i : Fin 3) : List Cell :=
  if i.val = 0 then [158,159,185,210] else
  if i.val = 1 then [184,210] else [158,159,184,185]
def region (i : Fin 3) : List Cell :=
  soko1_2.board.floor.filter (fun c =>
    !(locks i).contains c && (if i.val = 0 then decide (c ≠ 184) else true))
def credit (i : Fin 3) : Int := if i.val = 0 then 19 else if i.val = 1 then 17 else 19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked : PricedCorral.check soko1_2.board soko1_2.initial.holes
    Generated.soko1_2Potential locks region credit = true := by decide +kernel
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes
    Generated.soko1_2Potential locks region credit :=
  PricedCorral.closed_of_check _ _ _ _ _ _ checked
theorem unique (i : Fin 3) : (locks i).Nodup := by
  have all : ∀ i : Fin 3, (locks i).Nodup := by decide +kernel
  exact all i

theorem terminal {final : State} (completed : Goal final)
    (count : final.boulders.length = 2) (i : Fin 3)
    (good : PricedCorral.Good locks region i final) :
    Generated.soko1_2Potential.value final + credit i ≤ 0 := by
  by_cases hz : i.val = 0
  · have size := List.Nodup.length_le_of_subset (unique i) good.2
    simp [locks, hz, count] at size
  · by_cases ho : i.val = 1
    · have subset : [184,210] ⊆ final.boulders := by simpa [locks, hz, ho] using good.2
      have debt := NonlinearFacts.weightSum_le_of_nodup_subset
        (fun c => -Generated.soko1_2Potential.boulder c) [184,210] final.boulders
        (fun c => by have h := Generated.soko1_2_potential_valid.nonpositive c; omega)
        (by decide +kernel) subset
      change Owner1007.debtOf Generated.soko1_2Potential [184,210] ≤
        Owner1007.debtOf Generated.soko1_2Potential final.boulders at debt
      have amount : Owner1007.debtOf Generated.soko1_2Potential [184,210] = 17 := by decide +kernel
      have empty : final.holes = [] := completed
      have endpoint : Generated.soko1_2Potential.value final =
          -Owner1007.debtOf Generated.soko1_2Potential final.boulders := by
        rw [Owner1007.debtOf_neg]
        simp [Potential.value, empty, weightSum]
      simp only [credit, hz, ho, ↓reduceIte] at *
      omega
    · have size := List.Nodup.length_le_of_subset (unique i) good.2
      simp [locks, hz, ho, count] at size

/-- The tempting upper-access shortcut traps debt17 or a four-stone square. -/
theorem original_conditional_231 {state final : State} {history dirs : List Dir}
    {past pastMoves future futureMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (tail : Trace soko1_2.board state dirs final future futureMoves) (completed : Goal final)
    (outside : state.player ≠ 184) (inside : [158,159,185,210] ⊆ state.boulders) :
    231 ≤ past + future := by
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
        (show ([158,159,185,210] : List Cell).Nodup by decide +kernel) inside
      simp only [List.length_cons, List.length_nil] at count
      omega
    | cons head rest => exact (step_player_clear _ _ _ _ head).2.2.1
  have playerFloor := reached.player_floor (by decide +kernel)
  have good : PricedCorral.Good locks region 0 state := by
    constructor
    · change state.player ∈ soko1_2.board.floor.filter (fun c =>
        !(locks 0).contains c && decide (c ≠ 184))
      apply List.mem_filter.mpr
      have other : state.player ∉ locks 0 := fun h => standing (inside h)
      exact ⟨playerFloor, by simpa using And.intro other outside⟩
    · exact inside
  obtain ⟨j, finalGood, bound⟩ := PricedCorral.trace_price closed unique
    Generated.soko1_2_potential_valid tail good reached.holes_sublist.subset
  have endpoint := terminal completed finalCount j finalGood
  have prefixBound := trace_bound Generated.soko1_2_potential_valid.stepBound reached
  rw [Generated.soko1_2_initial_potential] at prefixBound
  change 19 ≤ _ at bound
  simp only [Int.ofNat_eq_natCast] at bound prefixBound
  omega

#print axioms checked
#print axioms original_conditional_231
end Owner1007.PriceTrap12Gate
