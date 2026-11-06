/- Kernel lemmas for comparing literal three-bit hero columns in bulk.
Mask equality is a normal checked Nat equality, not native reflection. -/
import NetHack.Sokoban.Model
namespace NetHack.Sokoban.PackedHeroEquality

def read3 (word hero : Nat) : Nat := (word >>> (3*hero)) % 8

theorem masked_read3 (word mask hero : Nat) (full : read3 mask hero = 7) :
    read3 (word &&& mask) hero = read3 word hero := by
  have distribute : read3 (word &&& mask) hero = read3 word hero &&& read3 mask hero := by
    unfold read3
    rw [Nat.shiftRight_and_distrib]
    exact Nat.and_mod_two_pow (n := 3)
  rw [distribute,full]
  change read3 word hero &&& (2^3-1) = read3 word hero
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))

theorem read3_eq_of_masked (left right mask hero : Nat)
    (full : read3 mask hero = 7) (same : left &&& mask = right &&& mask) :
    read3 left hero = read3 right hero := by
  rw [←masked_read3 left mask hero full,←masked_read3 right mask hero full,same]

end NetHack.Sokoban.PackedHeroEquality
