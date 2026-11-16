import Owner1007.ActorPrices11
namespace Owner1007.LeftDebt11
open NetHack.Sokoban
abbrev weight := NetHack.Soko11Hero315.weight
def debtCheck (phase : Nat) : Bool :=
 decide (weight phase 186 185 + weight phase 186 212 ≤ -2) &&
 decide (weight phase 212 211 + weight phase 212 186 ≤ -2)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem after_debts : (List.range 16).all debtCheck = true := by decide +kernel
theorem debts (phase : Nat) (active : phase < 16) :
 weight phase 186 185 + weight phase 186 212 ≤ -2 ∧
 weight phase 212 211 + weight phase 212 186 ≤ -2 := by
 have row := List.all_eq_true.mp after_debts phase (List.mem_range.mpr active)
 exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp row).1,
   of_decide_eq_true (Bool.and_eq_true_iff.mp row).2⟩
#print axioms after_debts
#print axioms debts
end Owner1007.LeftDebt11
