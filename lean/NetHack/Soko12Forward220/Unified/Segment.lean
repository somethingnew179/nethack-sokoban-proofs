import NetHack.Soko12Forward220.Unified.Base
namespace NetHack.Soko12Forward220.Unified
theorem segment_sound (check : Nat → Bool) (start length : Nat)
    (checked : (List.range' start length).all check = true)
    (index : Nat) (lower : start ≤ index) (upper : index < start + length) : check index = true := by
  apply List.all_eq_true.mp checked index
  exact List.mem_range'_1.mpr ⟨lower, upper⟩
end NetHack.Soko12Forward220.Unified
