/- Equality of pair/scalar data on every valid phase10 hero/crate input.
This alone does not transfer oracle transitions or prove lower321. -/
import NetHack.Soko11PairCandidate321.Conditional
import NetHack.Sokoban.PackedHeroEquality
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.PackedHeroEquality
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def heroMask10 : Nat := 0xff80000000000001fffffe00000000000007fffff80000000000000380000000000000001ffffffc000000000003fffffff000000000000fffffffc0000000000000000e00000000000007ffffffff80000000001ffffffffe000000000000070000000000000001ffffffff000000000007fffffffc0000000000000038000000000000000000fffff8000000ffffffffffffe00000000000000000000
def heroMaskCheck10 : Bool := (NetHack.Soko11Hero315.phases.heroes 10).all fun hero => decide (read3 heroMask10 hero = 7)
def wordEqualityCheck10 : Bool :=
  (NetHack.Soko11Hero315.phases.crates 10).all fun a =>
    (NetHack.Soko11Hero315.phases.crates 10).all fun b =>
      decide ((lookup (tables 10) (code [a,b]) &&& heroMask10) =
        (lookup (tables 14) (code [a,b]) &&& heroMask10))
def weightEqualityCheck10 : Bool :=
  (NetHack.Soko11Hero315.phases.heroes 10).all fun hero =>
    (NetHack.Soko11Hero315.phases.crates 10).all fun box =>
      decide (NetHack.Soko11Hero315.weight 10 hero box = NetHack.Soko11Hero315.weight 14 hero box)
theorem heroMask_checked10 : heroMaskCheck10 = true := by decide +kernel
theorem words_checked10 : wordEqualityCheck10 = true := by decide +kernel
theorem weights_checked10 : weightEqualityCheck10 = true := by decide +kernel

theorem pair_bonus_eq10 (hero a b : Cell)
    (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes 10)
    (aInside : a ∈ NetHack.Soko11Hero315.phases.crates 10)
    (bInside : b ∈ NetHack.Soko11Hero315.phases.crates 10) : bonus 10 hero [a,b] = bonus 14 hero [a,b] := by
  have full := of_decide_eq_true (List.all_eq_true.mp heroMask_checked10 hero heroInside)
  have same := of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked10 a aInside) b bInside)
  exact read3_eq_of_masked _ _ heroMask10 hero full same

theorem scalar_weight_eq10 (hero box : Cell)
    (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes 10)
    (boxInside : box ∈ NetHack.Soko11Hero315.phases.crates 10) :
    NetHack.Soko11Hero315.weight 10 hero box = NetHack.Soko11Hero315.weight 14 hero box :=
  of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp weights_checked10 hero heroInside) box boxInside)
end NetHack.Soko11PairCandidate321
