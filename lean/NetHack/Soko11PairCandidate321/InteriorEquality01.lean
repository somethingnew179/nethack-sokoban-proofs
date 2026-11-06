/- Equality of pair/scalar data on every valid phase1 hero/crate input.
This alone does not transfer oracle transitions or prove lower321. -/
import NetHack.Soko11PairCandidate321.Conditional
import NetHack.Sokoban.PackedHeroEquality
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.PackedHeroEquality
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def heroMask01 : Nat := 0xff80000000000001fffffe00000000000007fffff80000000000000380000000000000001ffffffc000000000003fffffff000000000000fffffffc0000000000000000e00000000000007ffffffff80000000001ffffffffe000000000000070000000000000001ffffffff000000000007fffffffc0000000000000038000000000000000000fffff80000000000001fffffe00000000000000000000
def heroMaskCheck01 : Bool := (NetHack.Soko11Hero315.phases.heroes 1).all fun hero => decide (read3 heroMask01 hero = 7)
def wordEqualityCheck01 : Bool :=
  (NetHack.Soko11Hero315.phases.crates 1).all fun a =>
    (NetHack.Soko11Hero315.phases.crates 1).all fun b =>
      decide ((lookup (tables 1) (code [a,b]) &&& heroMask01) =
        (lookup (tables 14) (code [a,b]) &&& heroMask01))
def weightEqualityCheck01 : Bool :=
  (NetHack.Soko11Hero315.phases.heroes 1).all fun hero =>
    (NetHack.Soko11Hero315.phases.crates 1).all fun box =>
      decide (NetHack.Soko11Hero315.weight 1 hero box = NetHack.Soko11Hero315.weight 14 hero box)
theorem heroMask_checked01 : heroMaskCheck01 = true := by decide +kernel
theorem words_checked01 : wordEqualityCheck01 = true := by decide +kernel
theorem weights_checked01 : weightEqualityCheck01 = true := by decide +kernel

theorem pair_bonus_eq01 (hero a b : Cell)
    (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes 1)
    (aInside : a ∈ NetHack.Soko11Hero315.phases.crates 1)
    (bInside : b ∈ NetHack.Soko11Hero315.phases.crates 1) : bonus 1 hero [a,b] = bonus 14 hero [a,b] := by
  have full := of_decide_eq_true (List.all_eq_true.mp heroMask_checked01 hero heroInside)
  have same := of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked01 a aInside) b bInside)
  exact read3_eq_of_masked _ _ heroMask01 hero full same

theorem scalar_weight_eq01 (hero box : Cell)
    (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes 1)
    (boxInside : box ∈ NetHack.Soko11Hero315.phases.crates 1) :
    NetHack.Soko11Hero315.weight 1 hero box = NetHack.Soko11Hero315.weight 14 hero box :=
  of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp weights_checked01 hero heroInside) box boxInside)
end NetHack.Soko11PairCandidate321
