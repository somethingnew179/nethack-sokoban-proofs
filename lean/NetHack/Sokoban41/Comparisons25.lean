/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons24
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c4000 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (15 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3998 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3999 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4001 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (15 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4000 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4002 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (15 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4001 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4003 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (15 : Int) + d325 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3995 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4002 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4004 (pattern : Ten) (guard : d350 pattern = 1) : d160 pattern ≤ (15 : Int) + d344 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3986 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4003 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4005 (pattern : Ten) (guard : d350 pattern = 1) : d157 pattern ≤ (15 : Int) + d341 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3990 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3993 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4006 (pattern : Ten) (guard : d350 pattern = 1) : d158 pattern ≤ (15 : Int) + d342 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4005 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4001 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4007 (pattern : Ten) (guard : d350 pattern = 1) : d159 pattern ≤ (15 : Int) + d343 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4006 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4008 (pattern : Ten) (guard : d350 pattern = 1) : d161 pattern ≤ (15 : Int) + d345 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3986 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4007 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4009 (pattern : Ten) (guard : d350 pattern = 1) : d165 pattern ≤ (15 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4004 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4008 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4010 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (15 : Int) + d309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4011 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (15 : Int) + d313 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3962 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4010 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4012 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (15 : Int) + d317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4011 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3988 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4013 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (15 : Int) + d318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3990 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4014 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (15 : Int) + d321 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4012 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4013 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4015 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (15 : Int) + d322 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3994 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4016 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (15 : Int) + d324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4014 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4015 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4017 (pattern : Ten) (guard : d350 pattern = 1) : d162 pattern ≤ (15 : Int) + d333 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4016 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4018 (pattern : Ten) (guard : d350 pattern = 1) : d163 pattern ≤ (15 : Int) + d334 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4003 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4019 (pattern : Ten) (guard : d350 pattern = 1) : d166 pattern ≤ (15 : Int) + d336 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4017 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4018 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4020 (pattern : Ten) (guard : d350 pattern = 1) : d168 pattern ≤ (15 : Int) + d347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4009 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4019 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4021 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (15 : Int) + d8 pattern := by
  change (7 : Int) ≤ (15 : Int) + 8
  decide
theorem c4022 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (15 : Int) + d8 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4021 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3996 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4023 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (15 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4022 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3997 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4024 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (15 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4025 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (15 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4023 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4024 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4026 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (15 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4025 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4027 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (15 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4026 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4028 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (15 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4027 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4029 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (15 : Int) + d10 pattern := by
  change (9 : Int) ≤ (15 : Int) + 10
  decide
theorem c4030 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (15 : Int) + d10 pattern := by
  omega
theorem c4031 (pattern : Ten) (guard : d1 pattern = 1) : d39 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4029 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4032 (pattern : Ten) (guard : d1 pattern = 1) : d41 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4031 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4033 (pattern : Ten) (guard : d0 pattern = 1) : d41 pattern ≤ (15 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4034 (pattern : Ten) (guard : d350 pattern = 1) : d41 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4032 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4033 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4035 (pattern : Ten) (guard : d350 pattern = 1) : d47 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4034 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4036 (pattern : Ten) (guard : d350 pattern = 1) : d53 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4035 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4037 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4036 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4038 (pattern : Ten) (guard : d350 pattern = 1) : d164 pattern ≤ (15 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4028 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4037 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4039 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (15 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4028 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4040 (pattern : Ten) (guard : d350 pattern = 1) : d167 pattern ≤ (15 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4038 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4039 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4041 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (15 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4042 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (15 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4023 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4041 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4043 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (15 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4042 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4044 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (15 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4043 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4045 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (15 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4044 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4046 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (15 : Int) + d335 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4045 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4047 (pattern : Ten) (guard : d350 pattern = 1) : d61 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4037 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4048 (pattern : Ten) (guard : d350 pattern = 1) : d63 pattern ≤ (15 : Int) + d337 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4046 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4047 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4049 (pattern : Ten) (guard : d350 pattern = 1) : d169 pattern ≤ (15 : Int) + d348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4040 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4048 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4050 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (15 : Int) + d349 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4020 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4049 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4051 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (15 : Int) + d10 pattern := by
  change (0 : Int) ≤ (15 : Int) + 10
  decide
theorem c4052 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (15 : Int) + d10 pattern := by
  change (1 : Int) ≤ (15 : Int) + 10
  decide
theorem c4053 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4051 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4052 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4054 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (15 : Int) + d10 pattern := by
  change (2 : Int) ≤ (15 : Int) + 10
  decide
theorem c4055 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (15 : Int) + d10 pattern := by
  change (3 : Int) ≤ (15 : Int) + 10
  decide
theorem c4056 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4054 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4055 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4057 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4053 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4056 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4058 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (15 : Int) + d10 pattern := by
  change (4 : Int) ≤ (15 : Int) + 10
  decide
theorem c4059 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (15 : Int) + d10 pattern := by
  change (5 : Int) ≤ (15 : Int) + 10
  decide
theorem c4060 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4058 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4059 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4061 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4060 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4062 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4057 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4061 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4063 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (15 : Int) + d10 pattern := by
  change (6 : Int) ≤ (15 : Int) + 10
  decide
theorem c4064 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (15 : Int) + d10 pattern := by
  change (7 : Int) ≤ (15 : Int) + 10
  decide
theorem c4065 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4063 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4064 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4066 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4065 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4067 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4066 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4068 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4062 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4067 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4069 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4055 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4058 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4070 (pattern : Ten) (guard : d1 pattern = 1) : d314 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4056 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4069 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4071 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4059 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4063 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4072 (pattern : Ten) (guard : d1 pattern = 1) : d315 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4060 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4071 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4073 (pattern : Ten) (guard : d1 pattern = 1) : d320 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4070 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4072 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4074 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (15 : Int) + d10 pattern := by
  change (8 : Int) ≤ (15 : Int) + 10
  decide
theorem c4075 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4064 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4074 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4076 (pattern : Ten) (guard : d1 pattern = 1) : d316 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4065 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4075 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4077 (pattern : Ten) (guard : d1 pattern = 1) : d319 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4076 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4078 (pattern : Ten) (guard : d1 pattern = 1) : d323 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4073 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4077 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4079 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4074 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4029 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4080 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4029 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4081 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4079 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4080 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4082 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4081 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4083 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4082 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4084 (pattern : Ten) (guard : d1 pattern = 1) : d325 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4078 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4083 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4085 (pattern : Ten) (guard : d1 pattern = 1) : d344 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4068 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4084 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4086 (pattern : Ten) (guard : d1 pattern = 1) : d341 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4072 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4076 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4087 (pattern : Ten) (guard : d1 pattern = 1) : d342 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4086 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4082 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4088 (pattern : Ten) (guard : d1 pattern = 1) : d343 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4087 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4089 (pattern : Ten) (guard : d1 pattern = 1) : d345 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4068 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4088 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4090 (pattern : Ten) (guard : d1 pattern = 1) : d346 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4085 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4089 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4091 (pattern : Ten) (guard : d1 pattern = 1) : d309 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4052 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4054 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4092 (pattern : Ten) (guard : d1 pattern = 1) : d313 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4053 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4091 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4093 (pattern : Ten) (guard : d1 pattern = 1) : d317 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4092 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4070 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4094 (pattern : Ten) (guard : d1 pattern = 1) : d318 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4072 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4095 (pattern : Ten) (guard : d1 pattern = 1) : d321 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4093 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4094 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4096 (pattern : Ten) (guard : d1 pattern = 1) : d322 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4077 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4097 (pattern : Ten) (guard : d1 pattern = 1) : d324 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4095 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4096 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4098 (pattern : Ten) (guard : d1 pattern = 1) : d333 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4097 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4099 (pattern : Ten) (guard : d1 pattern = 1) : d334 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4084 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4100 (pattern : Ten) (guard : d1 pattern = 1) : d336 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4098 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4099 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4101 (pattern : Ten) (guard : d1 pattern = 1) : d347 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4090 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4100 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4102 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4079 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4103 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4102 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4104 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4103 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4105 (pattern : Ten) (guard : d1 pattern = 1) : d214 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4104 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4106 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4083 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4107 (pattern : Ten) (guard : d1 pattern = 1) : d335 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4106 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4108 (pattern : Ten) (guard : d1 pattern = 1) : d337 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4107 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4109 (pattern : Ten) (guard : d1 pattern = 1) : d348 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4105 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4108 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4110 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (15 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4101 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4109 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4111 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (11 : Int) + d0 pattern := by
  omega
theorem c4112 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (11 : Int) + d1 pattern := by
  change (0 : Int) ≤ (11 : Int) + 1
  decide
theorem c4113 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (11 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4111 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4112 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4114 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (11 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4115 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (11 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4113 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4114 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4116 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (11 : Int) + d2 pattern := by
  omega
theorem c4117 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (11 : Int) + d3 pattern := by
  change (2 : Int) ≤ (11 : Int) + 3
  decide
theorem c4118 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (11 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4116 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4117 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4119 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (11 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4120 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (11 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4118 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4119 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4121 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (11 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4115 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4120 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4122 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (11 : Int) + d4 pattern := by
  omega
theorem c4123 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (11 : Int) + d5 pattern := by
  change (4 : Int) ≤ (11 : Int) + 5
  decide
theorem c4124 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (11 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4122 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4123 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4125 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (11 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4126 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (11 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4124 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4125 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4127 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (11 : Int) + d10 pattern := by
  omega
theorem c4128 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (11 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4126 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4129 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (11 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4121 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4128 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4130 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (11 : Int) + d6 pattern := by
  omega
theorem c4131 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (11 : Int) + d7 pattern := by
  change (6 : Int) ≤ (11 : Int) + 7
  decide
theorem c4132 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (11 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4130 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4131 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4133 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (11 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4134 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (11 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4132 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4133 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4135 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (11 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4134 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4136 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (11 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4135 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4137 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (11 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4129 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4136 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4138 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (11 : Int) + d310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4139 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (11 : Int) + d314 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4118 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4138 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4140 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (11 : Int) + d311 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4141 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (11 : Int) + d315 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4124 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4140 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4142 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (11 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4139 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4141 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4143 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (11 : Int) + d312 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4144 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (11 : Int) + d316 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4132 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4143 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4145 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (11 : Int) + d319 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4144 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4146 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (11 : Int) + d323 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4142 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4145 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4147 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (11 : Int) + d8 pattern := by
  omega
theorem c4148 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (11 : Int) + d9 pattern := by
  change (8 : Int) ≤ (11 : Int) + 9
  decide
theorem c4149 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (11 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4147 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4148 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4150 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (11 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4151 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (11 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4149 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4150 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4152 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (11 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4151 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4153 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (11 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4152 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4154 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (11 : Int) + d325 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4146 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4153 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4155 (pattern : Ten) (guard : d350 pattern = 1) : d160 pattern ≤ (11 : Int) + d344 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4137 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4154 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4156 (pattern : Ten) (guard : d350 pattern = 1) : d157 pattern ≤ (11 : Int) + d341 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4141 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4144 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4157 (pattern : Ten) (guard : d350 pattern = 1) : d158 pattern ≤ (11 : Int) + d342 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4156 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4152 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4158 (pattern : Ten) (guard : d350 pattern = 1) : d159 pattern ≤ (11 : Int) + d343 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4157 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4159 (pattern : Ten) (guard : d350 pattern = 1) : d161 pattern ≤ (11 : Int) + d345 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4137 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4158 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
