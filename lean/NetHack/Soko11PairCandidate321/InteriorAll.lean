import NetHack.Soko11PairCandidate321.InteriorEquality01
import NetHack.Soko11PairCandidate321.InteriorEquality02
import NetHack.Soko11PairCandidate321.InteriorEquality03
import NetHack.Soko11PairCandidate321.InteriorEquality04
import NetHack.Soko11PairCandidate321.InteriorEquality05
import NetHack.Soko11PairCandidate321.InteriorEquality06
import NetHack.Soko11PairCandidate321.InteriorEquality07
import NetHack.Soko11PairCandidate321.InteriorEquality08
import NetHack.Soko11PairCandidate321.InteriorEquality09
import NetHack.Soko11PairCandidate321.InteriorEquality10
import NetHack.Soko11PairCandidate321.InteriorEquality11
import NetHack.Soko11PairCandidate321.InteriorEquality12
import NetHack.Soko11PairCandidate321.InteriorEquality13
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Data equality on all permitted inputs of phases1..14. This does not
by itself identify their different first open holes or transfer oracle rows. -/
theorem interior_pair_bonus_equal (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14)
    (hero a b : Cell) (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes phase)
    (aInside : a ∈ NetHack.Soko11Hero315.phases.crates phase)
    (bInside : b ∈ NetHack.Soko11Hero315.phases.crates phase) :
    bonus phase hero [a,b] = bonus 14 hero [a,b] := by
  have choices : phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 ∨ phase = 5 ∨ phase = 6 ∨ phase = 7 ∨ phase = 8 ∨ phase = 9 ∨ phase = 10 ∨ phase = 11 ∨ phase = 12 ∨ phase = 13 ∨ phase = 14 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_bonus_eq01 hero a b heroInside aInside bInside
  · exact pair_bonus_eq02 hero a b heroInside aInside bInside
  · exact pair_bonus_eq03 hero a b heroInside aInside bInside
  · exact pair_bonus_eq04 hero a b heroInside aInside bInside
  · exact pair_bonus_eq05 hero a b heroInside aInside bInside
  · exact pair_bonus_eq06 hero a b heroInside aInside bInside
  · exact pair_bonus_eq07 hero a b heroInside aInside bInside
  · exact pair_bonus_eq08 hero a b heroInside aInside bInside
  · exact pair_bonus_eq09 hero a b heroInside aInside bInside
  · exact pair_bonus_eq10 hero a b heroInside aInside bInside
  · exact pair_bonus_eq11 hero a b heroInside aInside bInside
  · exact pair_bonus_eq12 hero a b heroInside aInside bInside
  · exact pair_bonus_eq13 hero a b heroInside aInside bInside
  · rfl
theorem interior_scalar_weight_equal (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14)
    (hero box : Cell) (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes phase)
    (boxInside : box ∈ NetHack.Soko11Hero315.phases.crates phase) :
    NetHack.Soko11Hero315.weight phase hero box = NetHack.Soko11Hero315.weight 14 hero box := by
  have choices : phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 ∨ phase = 5 ∨ phase = 6 ∨ phase = 7 ∨ phase = 8 ∨ phase = 9 ∨ phase = 10 ∨ phase = 11 ∨ phase = 12 ∨ phase = 13 ∨ phase = 14 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact scalar_weight_eq01 hero box heroInside boxInside
  · exact scalar_weight_eq02 hero box heroInside boxInside
  · exact scalar_weight_eq03 hero box heroInside boxInside
  · exact scalar_weight_eq04 hero box heroInside boxInside
  · exact scalar_weight_eq05 hero box heroInside boxInside
  · exact scalar_weight_eq06 hero box heroInside boxInside
  · exact scalar_weight_eq07 hero box heroInside boxInside
  · exact scalar_weight_eq08 hero box heroInside boxInside
  · exact scalar_weight_eq09 hero box heroInside boxInside
  · exact scalar_weight_eq10 hero box heroInside boxInside
  · exact scalar_weight_eq11 hero box heroInside boxInside
  · exact scalar_weight_eq12 hero box heroInside boxInside
  · exact scalar_weight_eq13 hero box heroInside boxInside
  · rfl
theorem interior_bonus_equal (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14)
    (hero : Cell) (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes phase)
    (group : List Cell) (inside : group ⊆ NetHack.Soko11Hero315.phases.crates phase) :
    bonus phase hero group = bonus 14 hero group := by
  by_cases two : group.length = 2
  · cases group with
    | nil => simp at two
    | cons a rest =>
      cases rest with
      | nil => simp at two
      | cons b tail =>
        cases tail with
        | nil => exact interior_pair_bonus_equal phase lower upper hero a b heroInside (inside (by simp)) (inside (by simp))
        | cons c rest => simp only [List.length_cons] at two; omega
  · simp only [bonus,if_neg two]

theorem sum_congr_on (left right : Cell → Int) (cells : List Cell)
    (same : ∀ cell ∈ cells, left cell = right cell) :
    LowerBounds.weightSum left cells = LowerBounds.weightSum right cells := by
  induction cells with
  | nil => rfl
  | cons first rest ih =>
    simp only [LowerBounds.weightSum_cons]
    rw [same first List.mem_cons_self,ih (fun c member => same c (List.mem_cons_of_mem _ member))]

theorem interior_value_equal (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14)
    (hero : Cell) (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes phase)
    (group : List Cell) (inside : group ⊆ NetHack.Soko11Hero315.phases.crates phase) :
    valueAt phase hero group = valueAt 14 hero group := by
  have weights := sum_congr_on (NetHack.Soko11Hero315.weight phase hero)
    (NetHack.Soko11Hero315.weight 14 hero) group (fun c member =>
      interior_scalar_weight_equal phase lower upper hero c heroInside (inside member))
  have bits := interior_bonus_equal phase lower upper hero heroInside group inside
  simp only [valueAt,weights,bits]
end NetHack.Soko11PairCandidate321
