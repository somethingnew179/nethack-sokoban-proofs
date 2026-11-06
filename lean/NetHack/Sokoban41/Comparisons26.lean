/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons25
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c4160 (pattern : Ten) (guard : d350 pattern = 1) : d165 pattern ≤ (11 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4155 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4159 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4161 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (11 : Int) + d309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4162 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (11 : Int) + d313 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4113 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4161 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4163 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (11 : Int) + d317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4162 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4139 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4164 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (11 : Int) + d318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4141 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4165 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (11 : Int) + d321 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4163 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4164 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4166 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (11 : Int) + d322 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4145 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4167 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (11 : Int) + d324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4165 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4166 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4168 (pattern : Ten) (guard : d350 pattern = 1) : d162 pattern ≤ (11 : Int) + d333 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4167 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4169 (pattern : Ten) (guard : d350 pattern = 1) : d163 pattern ≤ (11 : Int) + d334 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4154 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4170 (pattern : Ten) (guard : d350 pattern = 1) : d166 pattern ≤ (11 : Int) + d336 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4168 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4169 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4171 (pattern : Ten) (guard : d350 pattern = 1) : d168 pattern ≤ (11 : Int) + d347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4160 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4170 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4172 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (11 : Int) + d8 pattern := by
  change (7 : Int) ≤ (11 : Int) + 8
  decide
theorem c4173 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (11 : Int) + d8 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4172 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4147 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4174 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (11 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4173 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4148 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4175 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (11 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4176 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (11 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4174 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4175 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4177 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (11 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4176 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4178 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (11 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4177 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4179 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (11 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4178 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4180 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (11 : Int) + d10 pattern := by
  change (9 : Int) ≤ (11 : Int) + 10
  decide
theorem c4181 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (11 : Int) + d10 pattern := by
  omega
theorem c4182 (pattern : Ten) (guard : d1 pattern = 1) : d39 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4180 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4183 (pattern : Ten) (guard : d1 pattern = 1) : d41 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4182 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4184 (pattern : Ten) (guard : d0 pattern = 1) : d41 pattern ≤ (11 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4185 (pattern : Ten) (guard : d350 pattern = 1) : d41 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4183 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4184 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4186 (pattern : Ten) (guard : d350 pattern = 1) : d47 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4185 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4187 (pattern : Ten) (guard : d350 pattern = 1) : d53 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4186 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4188 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4187 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4189 (pattern : Ten) (guard : d350 pattern = 1) : d164 pattern ≤ (11 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4179 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4188 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4190 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (11 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4179 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4191 (pattern : Ten) (guard : d350 pattern = 1) : d167 pattern ≤ (11 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4189 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4190 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4192 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (11 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4193 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (11 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4174 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4192 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4194 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (11 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4193 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4195 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (11 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4194 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4196 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (11 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4195 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4197 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (11 : Int) + d335 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4196 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4198 (pattern : Ten) (guard : d350 pattern = 1) : d61 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4188 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4199 (pattern : Ten) (guard : d350 pattern = 1) : d63 pattern ≤ (11 : Int) + d337 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4197 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4198 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4200 (pattern : Ten) (guard : d350 pattern = 1) : d169 pattern ≤ (11 : Int) + d348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4191 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4199 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4201 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (11 : Int) + d349 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4171 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4200 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4202 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (11 : Int) + d10 pattern := by
  change (0 : Int) ≤ (11 : Int) + 10
  decide
theorem c4203 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (11 : Int) + d10 pattern := by
  change (1 : Int) ≤ (11 : Int) + 10
  decide
theorem c4204 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4202 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4203 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4205 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (11 : Int) + d10 pattern := by
  change (2 : Int) ≤ (11 : Int) + 10
  decide
theorem c4206 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (11 : Int) + d10 pattern := by
  change (3 : Int) ≤ (11 : Int) + 10
  decide
theorem c4207 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4205 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4206 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4208 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4204 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4207 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4209 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (11 : Int) + d10 pattern := by
  change (4 : Int) ≤ (11 : Int) + 10
  decide
theorem c4210 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (11 : Int) + d10 pattern := by
  change (5 : Int) ≤ (11 : Int) + 10
  decide
theorem c4211 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4209 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4210 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4212 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4211 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4213 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4208 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4212 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4214 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (11 : Int) + d10 pattern := by
  change (6 : Int) ≤ (11 : Int) + 10
  decide
theorem c4215 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (11 : Int) + d10 pattern := by
  change (7 : Int) ≤ (11 : Int) + 10
  decide
theorem c4216 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4214 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4217 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4216 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4218 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4217 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4219 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4213 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4218 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4220 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4206 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4209 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4221 (pattern : Ten) (guard : d1 pattern = 1) : d314 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4207 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4220 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4222 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4210 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4214 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4223 (pattern : Ten) (guard : d1 pattern = 1) : d315 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4211 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4222 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4224 (pattern : Ten) (guard : d1 pattern = 1) : d320 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4221 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4223 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4225 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (11 : Int) + d10 pattern := by
  change (8 : Int) ≤ (11 : Int) + 10
  decide
theorem c4226 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4225 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4227 (pattern : Ten) (guard : d1 pattern = 1) : d316 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4216 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4226 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4228 (pattern : Ten) (guard : d1 pattern = 1) : d319 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4227 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4229 (pattern : Ten) (guard : d1 pattern = 1) : d323 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4224 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4228 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4230 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4225 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4180 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4231 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4180 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4232 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4230 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4231 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4233 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4232 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4234 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4233 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4235 (pattern : Ten) (guard : d1 pattern = 1) : d325 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4229 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4234 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4236 (pattern : Ten) (guard : d1 pattern = 1) : d344 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4219 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4235 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4237 (pattern : Ten) (guard : d1 pattern = 1) : d341 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4223 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4227 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4238 (pattern : Ten) (guard : d1 pattern = 1) : d342 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4237 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4233 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4239 (pattern : Ten) (guard : d1 pattern = 1) : d343 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4238 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4240 (pattern : Ten) (guard : d1 pattern = 1) : d345 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4219 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4239 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4241 (pattern : Ten) (guard : d1 pattern = 1) : d346 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4236 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4240 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4242 (pattern : Ten) (guard : d1 pattern = 1) : d309 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4203 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4205 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4243 (pattern : Ten) (guard : d1 pattern = 1) : d313 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4204 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4242 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4244 (pattern : Ten) (guard : d1 pattern = 1) : d317 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4243 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4221 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4245 (pattern : Ten) (guard : d1 pattern = 1) : d318 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4223 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4246 (pattern : Ten) (guard : d1 pattern = 1) : d321 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4244 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4245 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4247 (pattern : Ten) (guard : d1 pattern = 1) : d322 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4228 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4248 (pattern : Ten) (guard : d1 pattern = 1) : d324 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4246 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4247 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4249 (pattern : Ten) (guard : d1 pattern = 1) : d333 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4248 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4250 (pattern : Ten) (guard : d1 pattern = 1) : d334 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4235 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4251 (pattern : Ten) (guard : d1 pattern = 1) : d336 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4249 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4250 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4252 (pattern : Ten) (guard : d1 pattern = 1) : d347 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4241 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4251 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4253 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4230 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4254 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4253 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4255 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4254 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4256 (pattern : Ten) (guard : d1 pattern = 1) : d214 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4255 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4257 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4234 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4258 (pattern : Ten) (guard : d1 pattern = 1) : d335 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4257 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4259 (pattern : Ten) (guard : d1 pattern = 1) : d337 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4258 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4260 (pattern : Ten) (guard : d1 pattern = 1) : d348 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4256 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4259 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4261 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (11 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4252 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4260 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4262 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (12 : Int) + d0 pattern := by
  omega
theorem c4263 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (12 : Int) + d1 pattern := by
  change (0 : Int) ≤ (12 : Int) + 1
  decide
theorem c4264 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (12 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4262 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4263 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4265 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (12 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4266 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (12 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4264 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4267 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (12 : Int) + d2 pattern := by
  omega
theorem c4268 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (12 : Int) + d3 pattern := by
  change (2 : Int) ≤ (12 : Int) + 3
  decide
theorem c4269 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (12 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4267 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4268 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4270 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (12 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4271 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (12 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4270 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4272 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (12 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4266 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4271 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4273 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (12 : Int) + d4 pattern := by
  omega
theorem c4274 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (12 : Int) + d5 pattern := by
  change (4 : Int) ≤ (12 : Int) + 5
  decide
theorem c4275 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (12 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4273 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4274 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4276 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (12 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4277 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (12 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4275 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4276 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4278 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (12 : Int) + d10 pattern := by
  omega
theorem c4279 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (12 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4277 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4280 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (12 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4272 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4279 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4281 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (12 : Int) + d6 pattern := by
  omega
theorem c4282 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (12 : Int) + d7 pattern := by
  change (6 : Int) ≤ (12 : Int) + 7
  decide
theorem c4283 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (12 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4281 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4282 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4284 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (12 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4285 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (12 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4283 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4284 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4286 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (12 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4285 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4287 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (12 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4286 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4288 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (12 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4280 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4287 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4289 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (12 : Int) + d310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4290 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (12 : Int) + d314 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4289 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4291 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (12 : Int) + d311 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4292 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (12 : Int) + d315 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4275 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4291 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4293 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (12 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4290 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4292 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4294 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (12 : Int) + d312 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4295 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (12 : Int) + d316 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4283 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4294 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4296 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (12 : Int) + d319 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4295 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4297 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (12 : Int) + d323 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4293 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4296 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4298 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (12 : Int) + d8 pattern := by
  omega
theorem c4299 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (12 : Int) + d9 pattern := by
  change (8 : Int) ≤ (12 : Int) + 9
  decide
theorem c4300 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (12 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4298 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4299 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4301 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (12 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4302 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (12 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4300 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4301 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4303 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (12 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4302 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4304 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (12 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4303 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4305 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (12 : Int) + d325 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4297 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4304 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4306 (pattern : Ten) (guard : d350 pattern = 1) : d160 pattern ≤ (12 : Int) + d344 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4288 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4305 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4307 (pattern : Ten) (guard : d350 pattern = 1) : d157 pattern ≤ (12 : Int) + d341 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4292 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4295 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4308 (pattern : Ten) (guard : d350 pattern = 1) : d158 pattern ≤ (12 : Int) + d342 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4307 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4303 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4309 (pattern : Ten) (guard : d350 pattern = 1) : d159 pattern ≤ (12 : Int) + d343 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4308 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4310 (pattern : Ten) (guard : d350 pattern = 1) : d161 pattern ≤ (12 : Int) + d345 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4288 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4309 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4311 (pattern : Ten) (guard : d350 pattern = 1) : d165 pattern ≤ (12 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4306 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4310 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4312 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (12 : Int) + d309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4313 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (12 : Int) + d313 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4264 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4312 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4314 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (12 : Int) + d317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4313 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4290 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4315 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (12 : Int) + d318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4292 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4316 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (12 : Int) + d321 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4314 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4315 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4317 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (12 : Int) + d322 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4296 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4318 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (12 : Int) + d324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4316 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4317 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4319 (pattern : Ten) (guard : d350 pattern = 1) : d162 pattern ≤ (12 : Int) + d333 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4318 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
