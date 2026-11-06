/- Equality of pair/scalar data on every valid phase11 hero/crate input.
This alone does not transfer oracle transitions or prove lower321. -/
import NetHack.Soko11PairCandidate321.Conditional
import NetHack.Sokoban.PackedHeroEquality
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.PackedHeroEquality
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def heroMask11 : Nat := 0xff80000000000001fffffe00000000000007fffff80000000000000380000000000000001ffffffc000000000003fffffff000000000000fffffffc0000000000000000e00000000000007ffffffff80000000001ffffffffe000000000000070000000000000001ffffffff000000000007fffffffc0000000000000038000000000000000000fffff8000007ffffffffffffe00000000000000000000
def heroMaskCheck11 : Bool := (NetHack.Soko11Hero315.phases.heroes 11).all fun hero => decide (read3 heroMask11 hero = 7)
def wordEqualityCheck11 : Bool :=
  (NetHack.Soko11Hero315.phases.crates 11).all fun a =>
    (NetHack.Soko11Hero315.phases.crates 11).all fun b =>
      decide ((lookup (tables 11) (code [a,b]) &&& heroMask11) =
        (lookup (tables 14) (code [a,b]) &&& heroMask11))
def weightEqualityCheck11 : Bool :=
  (NetHack.Soko11Hero315.phases.heroes 11).all fun hero =>
    (NetHack.Soko11Hero315.phases.crates 11).all fun box =>
      decide (NetHack.Soko11Hero315.weight 11 hero box = NetHack.Soko11Hero315.weight 14 hero box)
theorem heroMask_checked11 : heroMaskCheck11 = true := by decide +kernel
theorem words_checked11 : wordEqualityCheck11 = true := by decide +kernel
theorem weights_checked11 : weightEqualityCheck11 = true := by decide +kernel

theorem pair_bonus_eq11 (hero a b : Cell)
    (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes 11)
    (aInside : a ∈ NetHack.Soko11Hero315.phases.crates 11)
    (bInside : b ∈ NetHack.Soko11Hero315.phases.crates 11) : bonus 11 hero [a,b] = bonus 14 hero [a,b] := by
  have full := of_decide_eq_true (List.all_eq_true.mp heroMask_checked11 hero heroInside)
  have same := of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp words_checked11 a aInside) b bInside)
  exact read3_eq_of_masked _ _ heroMask11 hero full same

theorem scalar_weight_eq11 (hero box : Cell)
    (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes 11)
    (boxInside : box ∈ NetHack.Soko11Hero315.phases.crates 11) :
    NetHack.Soko11Hero315.weight 11 hero box = NetHack.Soko11Hero315.weight 14 hero box :=
  of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp weights_checked11 hero heroInside) box boxInside)
end NetHack.Soko11PairCandidate321
