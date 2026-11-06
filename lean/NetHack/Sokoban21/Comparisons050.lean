/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons049
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c7000 (pattern : Twelve) (guard : d1865 pattern = 1) : d481 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d481, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2846 pattern childGuard
    simpa only [d1865, d481, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d481, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6999 pattern childGuard
    simpa only [d1865, d481, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7001 (pattern : Twelve) (guard : d1865 pattern = 1) : d502 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d502, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6989 pattern childGuard
    simpa only [d502, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d502, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7000 pattern childGuard
    simpa only [d502, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7002 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7003 (pattern : Twelve) (guard : d1865 pattern = 1) : d482 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d482, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2850 pattern childGuard
    simpa only [d1865, d482, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d482, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7002 pattern childGuard
    simpa only [d1865, d482, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7004 (pattern : Twelve) (guard : d1865 pattern = 1) : d503 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d503, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7003 pattern childGuard
    simpa only [d503, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d503, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d503, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7005 (pattern : Twelve) (guard : d1865 pattern = 1) : d535 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d535, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7001 pattern childGuard
    simpa only [d535, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d535, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7004 pattern childGuard
    simpa only [d535, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7006 (pattern : Twelve) (guard : d1865 pattern = 1) : d562 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d562, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6998 pattern childGuard
    simpa only [d562, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d562, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7005 pattern childGuard
    simpa only [d562, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7007 (pattern : Twelve) (guard : d1865 pattern = 1) : d588 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d588, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6993 pattern childGuard
    simpa only [d588, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d588, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7006 pattern childGuard
    simpa only [d588, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7008 (pattern : Twelve) (guard : d1865 pattern = 1) : d483 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1609 pattern childGuard
    simpa only [d1865, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7009 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7010 (pattern : Twelve) (guard : d1865 pattern = 1) : d484 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7009 pattern childGuard
    simpa only [d1865, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7011 (pattern : Twelve) (guard : d1865 pattern = 1) : d504 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7008 pattern childGuard
    simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7010 pattern childGuard
    simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7012 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7013 (pattern : Twelve) (guard : d1865 pattern = 1) : d485 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7012 pattern childGuard
    simpa only [d1865, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7014 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d13 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7015 (pattern : Twelve) (guard : d1865 pattern = 1) : d486 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d486, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2865 pattern childGuard
    simpa only [d1865, d486, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d486, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7014 pattern childGuard
    simpa only [d1865, d486, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7016 (pattern : Twelve) (guard : d1865 pattern = 1) : d505 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d505, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7013 pattern childGuard
    simpa only [d505, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d505, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7015 pattern childGuard
    simpa only [d505, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7017 (pattern : Twelve) (guard : d1865 pattern = 1) : d536 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d536, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7011 pattern childGuard
    simpa only [d536, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d536, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7016 pattern childGuard
    simpa only [d536, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7018 (pattern : Twelve) (guard : d1865 pattern = 1) : d487 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1865, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7019 (pattern : Twelve) (guard : d1865 pattern = 1) : d506 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7013 pattern childGuard
    simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7018 pattern childGuard
    simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7020 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7021 (pattern : Twelve) (guard : d1865 pattern = 1) : d480 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d480, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d480, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d480, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7020 pattern childGuard
    simpa only [d1865, d480, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7022 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7023 (pattern : Twelve) (guard : d1865 pattern = 1) : d170 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2874 pattern childGuard
    simpa only [d1865, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7022 pattern childGuard
    simpa only [d1865, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7024 (pattern : Twelve) (guard : d1865 pattern = 1) : d507 pattern ≤ (0 : Int) + d32 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d507, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d507, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d507, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7023 pattern childGuard
    simpa only [d507, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7025 (pattern : Twelve) (guard : d1865 pattern = 1) : d537 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d537, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7019 pattern childGuard
    simpa only [d537, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d537, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7024 pattern childGuard
    simpa only [d537, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7026 (pattern : Twelve) (guard : d1865 pattern = 1) : d563 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d563, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7017 pattern childGuard
    simpa only [d563, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d563, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7025 pattern childGuard
    simpa only [d563, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7027 (pattern : Twelve) (guard : d1865 pattern = 1) : d508 pattern ≤ (0 : Int) + d33 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d508, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d508, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d508, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d508, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7028 (pattern : Twelve) (guard : d1865 pattern = 1) : d538 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d538, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7019 pattern childGuard
    simpa only [d538, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d538, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7027 pattern childGuard
    simpa only [d538, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7029 (pattern : Twelve) (guard : d1865 pattern = 1) : d487 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d487, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d487, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d487, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6999 pattern childGuard
    simpa only [d1865, d487, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7030 (pattern : Twelve) (guard : d1865 pattern = 1) : d509 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d509, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7029 pattern childGuard
    simpa only [d509, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7031 (pattern : Twelve) (guard : d1865 pattern = 1) : d539 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d539, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7030 pattern childGuard
    simpa only [d539, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d539, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7004 pattern childGuard
    simpa only [d539, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7032 (pattern : Twelve) (guard : d1865 pattern = 1) : d564 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d564, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7028 pattern childGuard
    simpa only [d564, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d564, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7031 pattern childGuard
    simpa only [d564, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7033 (pattern : Twelve) (guard : d1865 pattern = 1) : d589 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d589, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7026 pattern childGuard
    simpa only [d589, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d589, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7032 pattern childGuard
    simpa only [d589, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7034 (pattern : Twelve) (guard : d1865 pattern = 1) : d606 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d606, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7007 pattern childGuard
    simpa only [d606, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d606, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7033 pattern childGuard
    simpa only [d606, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7035 (pattern : Twelve) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7036 (pattern : Twelve) (guard : d1865 pattern = 1) : d488 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7035 pattern childGuard
    simpa only [d1865, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7037 (pattern : Twelve) (guard : d1865 pattern = 1) : d510 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7008 pattern childGuard
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7036 pattern childGuard
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7038 (pattern : Twelve) (guard : d1865 pattern = 1) : d511 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7013 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7039 (pattern : Twelve) (guard : d1865 pattern = 1) : d540 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7037 pattern childGuard
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7038 pattern childGuard
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7040 (pattern : Twelve) (guard : d1865 pattern = 1) : d512 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7013 pattern childGuard
    simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6990 pattern childGuard
    simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7041 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d513, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6990 pattern childGuard
    simpa only [d513, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7042 (pattern : Twelve) (guard : d1865 pattern = 1) : d541 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d541, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7040 pattern childGuard
    simpa only [d541, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d541, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7041 pattern childGuard
    simpa only [d541, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7043 (pattern : Twelve) (guard : d1865 pattern = 1) : d565 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d565, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7039 pattern childGuard
    simpa only [d565, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d565, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7042 pattern childGuard
    simpa only [d565, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7044 (pattern : Twelve) (guard : d1865 pattern = 1) : d542 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7038 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7045 (pattern : Twelve) (guard : d1865 pattern = 1) : d566 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d566, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7044 pattern childGuard
    simpa only [d566, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d566, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7031 pattern childGuard
    simpa only [d566, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7046 (pattern : Twelve) (guard : d1865 pattern = 1) : d590 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d590, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7043 pattern childGuard
    simpa only [d590, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d590, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7045 pattern childGuard
    simpa only [d590, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7047 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7048 (pattern : Twelve) (guard : d1865 pattern = 1) : d489 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7047 pattern childGuard
    simpa only [d1865, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7049 (pattern : Twelve) (guard : d1865 pattern = 1) : d514 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7048 pattern childGuard
    simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7018 pattern childGuard
    simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7050 (pattern : Twelve) (guard : d1865 pattern = 1) : d515 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7051 (pattern : Twelve) (guard : d1865 pattern = 1) : d543 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7049 pattern childGuard
    simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7050 pattern childGuard
    simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7052 (pattern : Twelve) (guard : d1865 pattern = 1) : d509 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7018 pattern childGuard
    simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7053 (pattern : Twelve) (guard : d1865 pattern = 1) : d515 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d515, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d515, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d515, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7054 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (0 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d544, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7053 pattern childGuard
    simpa only [d544, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7055 (pattern : Twelve) (guard : d1865 pattern = 1) : d567 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d567, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7051 pattern childGuard
    simpa only [d567, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d567, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7054 pattern childGuard
    simpa only [d567, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7056 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7050 pattern childGuard
    simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7057 (pattern : Twelve) (guard : d1865 pattern = 1) : d568 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d568, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7056 pattern childGuard
    simpa only [d568, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d568, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7031 pattern childGuard
    simpa only [d568, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7058 (pattern : Twelve) (guard : d1865 pattern = 1) : d591 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d591, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7055 pattern childGuard
    simpa only [d591, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d591, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7057 pattern childGuard
    simpa only [d591, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7059 (pattern : Twelve) (guard : d1865 pattern = 1) : d607 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d607, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7046 pattern childGuard
    simpa only [d607, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d607, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7058 pattern childGuard
    simpa only [d607, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7060 (pattern : Twelve) (guard : d1865 pattern = 1) : d618 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d618, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7034 pattern childGuard
    simpa only [d618, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d618, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7059 pattern childGuard
    simpa only [d618, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7061 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7062 (pattern : Twelve) (guard : d1865 pattern = 1) : d490 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7061 pattern childGuard
    simpa only [d1865, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7063 (pattern : Twelve) (guard : d0 pattern = 1) : d13 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7064 (pattern : Twelve) (guard : d1865 pattern = 1) : d491 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7063 pattern childGuard
    simpa only [d1865, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7065 (pattern : Twelve) (guard : d1865 pattern = 1) : d516 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7062 pattern childGuard
    simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7064 pattern childGuard
    simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7066 (pattern : Twelve) (guard : d1865 pattern = 1) : d517 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7036 pattern childGuard
    simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7018 pattern childGuard
    simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7067 (pattern : Twelve) (guard : d1865 pattern = 1) : d545 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7065 pattern childGuard
    simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7066 pattern childGuard
    simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7068 (pattern : Twelve) (guard : d1865 pattern = 1) : d492 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1865, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7069 (pattern : Twelve) (guard : d1865 pattern = 1) : d518 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d518, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7068 pattern childGuard
    simpa only [d518, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7070 (pattern : Twelve) (guard : d1865 pattern = 1) : d546 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d546, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7066 pattern childGuard
    simpa only [d546, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d546, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7069 pattern childGuard
    simpa only [d546, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7071 (pattern : Twelve) (guard : d1865 pattern = 1) : d569 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d569, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7067 pattern childGuard
    simpa only [d569, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d569, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7070 pattern childGuard
    simpa only [d569, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7072 (pattern : Twelve) (guard : d1865 pattern = 1) : d547 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7066 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7073 (pattern : Twelve) (guard : d1865 pattern = 1) : d570 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d570, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7072 pattern childGuard
    simpa only [d570, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d570, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7031 pattern childGuard
    simpa only [d570, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7074 (pattern : Twelve) (guard : d1865 pattern = 1) : d592 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d592, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7071 pattern childGuard
    simpa only [d592, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d592, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7073 pattern childGuard
    simpa only [d592, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7075 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7076 (pattern : Twelve) (guard : d1865 pattern = 1) : d493 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7075 pattern childGuard
    simpa only [d1865, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7077 (pattern : Twelve) (guard : d1865 pattern = 1) : d494 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1865, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7078 (pattern : Twelve) (guard : d1865 pattern = 1) : d519 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7076 pattern childGuard
    simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7077 pattern childGuard
    simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7079 (pattern : Twelve) (guard : d1865 pattern = 1) : d520 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7018 pattern childGuard
    simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7080 (pattern : Twelve) (guard : d1865 pattern = 1) : d548 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7078 pattern childGuard
    simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7079 pattern childGuard
    simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7081 (pattern : Twelve) (guard : d1865 pattern = 1) : d521 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7018 pattern childGuard
    simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7077 pattern childGuard
    simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7082 (pattern : Twelve) (guard : d1865 pattern = 1) : d520 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7029 pattern childGuard
    simpa only [d520, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d520, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d520, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7083 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7081 pattern childGuard
    simpa only [d549, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7082 pattern childGuard
    simpa only [d549, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7084 (pattern : Twelve) (guard : d1865 pattern = 1) : d571 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d571, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7080 pattern childGuard
    simpa only [d571, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d571, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7083 pattern childGuard
    simpa only [d571, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7085 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7081 pattern childGuard
    simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7079 pattern childGuard
    simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7086 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7087 (pattern : Twelve) (guard : d1865 pattern = 1) : d494 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d494, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d1865, d494, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d494, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7086 pattern childGuard
    simpa only [d1865, d494, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7088 (pattern : Twelve) (guard : d1865 pattern = 1) : d521 pattern ≤ (0 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7029 pattern childGuard
    simpa only [d521, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d521, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7087 pattern childGuard
    simpa only [d521, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7089 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d12 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7090 (pattern : Twelve) (guard : d1865 pattern = 1) : d495 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d495, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2946 pattern childGuard
    simpa only [d1865, d495, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d495, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7089 pattern childGuard
    simpa only [d1865, d495, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7091 (pattern : Twelve) (guard : d1865 pattern = 1) : d522 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7090 pattern childGuard
    simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7092 (pattern : Twelve) (guard : d1865 pattern = 1) : d550 pattern ≤ (0 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d550, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7088 pattern childGuard
    simpa only [d550, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d550, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7091 pattern childGuard
    simpa only [d550, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7093 (pattern : Twelve) (guard : d1865 pattern = 1) : d572 pattern ≤ (0 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d572, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7085 pattern childGuard
    simpa only [d572, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d572, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7092 pattern childGuard
    simpa only [d572, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7094 (pattern : Twelve) (guard : d1865 pattern = 1) : d593 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d593, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7084 pattern childGuard
    simpa only [d593, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d593, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7093 pattern childGuard
    simpa only [d593, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7095 (pattern : Twelve) (guard : d1865 pattern = 1) : d608 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d608, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7074 pattern childGuard
    simpa only [d608, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d608, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7094 pattern childGuard
    simpa only [d608, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7096 (pattern : Twelve) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7097 (pattern : Twelve) (guard : d1865 pattern = 1) : d496 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7096 pattern childGuard
    simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7098 (pattern : Twelve) (guard : d1865 pattern = 1) : d523 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7097 pattern childGuard
    simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7018 pattern childGuard
    simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7099 (pattern : Twelve) (guard : d1865 pattern = 1) : d551 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7098 pattern childGuard
    simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7050 pattern childGuard
    simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7100 (pattern : Twelve) (guard : d1865 pattern = 1) : d573 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d573, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7099 pattern childGuard
    simpa only [d573, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d573, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7054 pattern childGuard
    simpa only [d573, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7101 (pattern : Twelve) (guard : d1865 pattern = 1) : d594 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d594, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7100 pattern childGuard
    simpa only [d594, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d594, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7057 pattern childGuard
    simpa only [d594, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7102 (pattern : Twelve) (guard : d1865 pattern = 1) : d609 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d609, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7101 pattern childGuard
    simpa only [d609, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d609, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d609, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7103 (pattern : Twelve) (guard : d1865 pattern = 1) : d619 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d619, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7095 pattern childGuard
    simpa only [d619, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d619, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7102 pattern childGuard
    simpa only [d619, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7104 (pattern : Twelve) (guard : d1865 pattern = 1) : d624 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d624, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7060 pattern childGuard
    simpa only [d624, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d624, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7103 pattern childGuard
    simpa only [d624, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7105 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6990 pattern childGuard
    simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7106 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7105 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7041 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7107 (pattern : Twelve) (guard : d1865 pattern = 1) : d574 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d574, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d574, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d574, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7106 pattern childGuard
    simpa only [d574, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7108 (pattern : Twelve) (guard : d1865 pattern = 1) : d524 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d524, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d524, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d524, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7000 pattern childGuard
    simpa only [d524, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7109 (pattern : Twelve) (guard : d1865 pattern = 1) : d552 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d552, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7108 pattern childGuard
    simpa only [d552, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d552, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7004 pattern childGuard
    simpa only [d552, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7110 (pattern : Twelve) (guard : d1865 pattern = 1) : d575 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d575, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d575, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d575, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7109 pattern childGuard
    simpa only [d575, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7111 (pattern : Twelve) (guard : d1865 pattern = 1) : d595 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d595, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7107 pattern childGuard
    simpa only [d595, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d595, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7110 pattern childGuard
    simpa only [d595, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7112 (pattern : Twelve) (guard : d1865 pattern = 1) : d525 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d525, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d525, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d525, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7015 pattern childGuard
    simpa only [d525, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7113 (pattern : Twelve) (guard : d1865 pattern = 1) : d553 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d553, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d553, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d553, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7112 pattern childGuard
    simpa only [d553, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7114 (pattern : Twelve) (guard : d1865 pattern = 1) : d554 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d554, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d554, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d554, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7024 pattern childGuard
    simpa only [d554, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7115 (pattern : Twelve) (guard : d1865 pattern = 1) : d576 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d576, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7113 pattern childGuard
    simpa only [d576, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d576, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7114 pattern childGuard
    simpa only [d576, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7116 (pattern : Twelve) (guard : d1865 pattern = 1) : d555 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d555, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d555, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d555, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7027 pattern childGuard
    simpa only [d555, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7117 (pattern : Twelve) (guard : d1865 pattern = 1) : d577 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d577, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7116 pattern childGuard
    simpa only [d577, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d577, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7031 pattern childGuard
    simpa only [d577, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7118 (pattern : Twelve) (guard : d1865 pattern = 1) : d596 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d596, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7115 pattern childGuard
    simpa only [d596, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d596, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7117 pattern childGuard
    simpa only [d596, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7119 (pattern : Twelve) (guard : d1865 pattern = 1) : d610 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7111 pattern childGuard
    simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7118 pattern childGuard
    simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7120 (pattern : Twelve) (guard : d1865 pattern = 1) : d578 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d578, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d578, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d578, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7031 pattern childGuard
    simpa only [d578, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7121 (pattern : Twelve) (guard : d1865 pattern = 1) : d597 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d597, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7107 pattern childGuard
    simpa only [d597, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d597, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7120 pattern childGuard
    simpa only [d597, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7122 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7056 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7054 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7123 (pattern : Twelve) (guard : d1865 pattern = 1) : d598 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d598, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7122 pattern childGuard
    simpa only [d598, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d598, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7057 pattern childGuard
    simpa only [d598, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7124 (pattern : Twelve) (guard : d1865 pattern = 1) : d611 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7121 pattern childGuard
    simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7123 pattern childGuard
    simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7125 (pattern : Twelve) (guard : d1865 pattern = 1) : d620 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d620, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7119 pattern childGuard
    simpa only [d620, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d620, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7124 pattern childGuard
    simpa only [d620, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7126 (pattern : Twelve) (guard : d1865 pattern = 1) : d556 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d556, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7069 pattern childGuard
    simpa only [d556, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7127 (pattern : Twelve) (guard : d1865 pattern = 1) : d579 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d579, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d579, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d579, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7126 pattern childGuard
    simpa only [d579, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7128 (pattern : Twelve) (guard : d1865 pattern = 1) : d580 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d580, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d580, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d580, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7031 pattern childGuard
    simpa only [d580, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7129 (pattern : Twelve) (guard : d1865 pattern = 1) : d599 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d599, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7127 pattern childGuard
    simpa only [d599, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d599, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7128 pattern childGuard
    simpa only [d599, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7130 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7085 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7083 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7131 (pattern : Twelve) (guard : d1865 pattern = 1) : d600 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d600, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7130 pattern childGuard
    simpa only [d600, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d600, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7093 pattern childGuard
    simpa only [d600, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7132 (pattern : Twelve) (guard : d1865 pattern = 1) : d612 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d612, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7129 pattern childGuard
    simpa only [d612, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d612, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7131 pattern childGuard
    simpa only [d612, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7133 (pattern : Twelve) (guard : d1865 pattern = 1) : d613 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d613, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7123 pattern childGuard
    simpa only [d613, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d613, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d613, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7134 (pattern : Twelve) (guard : d1865 pattern = 1) : d621 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d621, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7132 pattern childGuard
    simpa only [d621, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d621, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7133 pattern childGuard
    simpa only [d621, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7135 (pattern : Twelve) (guard : d1865 pattern = 1) : d625 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d625, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7125 pattern childGuard
    simpa only [d625, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d625, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7134 pattern childGuard
    simpa only [d625, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7136 (pattern : Twelve) (guard : d1865 pattern = 1) : d627 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7104 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7135 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7137 (pattern : Twelve) (guard : d1865 pattern = 1) : d628 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7136 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7135 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7138 (pattern : Twelve) (guard : d1865 pattern = 1) : d526 pattern ≤ (0 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d526, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d526, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d526, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7090 pattern childGuard
    simpa only [d526, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7139 (pattern : Twelve) (guard : d1865 pattern = 1) : d557 pattern ≤ (0 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d557, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7138 pattern childGuard
    simpa only [d557, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d557, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7004 pattern childGuard
    simpa only [d557, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
