/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons043
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c6160 (pattern : Twelve) (guard : d0 pattern = 1) : d436 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6161 (pattern : Twelve) (guard : d1858 pattern = 1) : d436 pattern ≤ (0 : Int) + d315 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6159 pattern childGuard
    simpa only [d1858, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6160 pattern childGuard
    simpa only [d1858, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6162 (pattern : Twelve) (guard : d1858 pattern = 1) : d461 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d461, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6157 pattern childGuard
    simpa only [d461, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d461, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6161 pattern childGuard
    simpa only [d461, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6163 (pattern : Twelve) (guard : d1858 pattern = 1) : d462 pattern ≤ (0 : Int) + d327 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d462, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6151 pattern childGuard
    simpa only [d462, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d462, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d462, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6164 (pattern : Twelve) (guard : d1858 pattern = 1) : d468 pattern ≤ (0 : Int) + d335 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d468, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6162 pattern childGuard
    simpa only [d468, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d468, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6163 pattern childGuard
    simpa only [d468, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6165 (pattern : Twelve) (guard : d1858 pattern = 1) : d472 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d472, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6153 pattern childGuard
    simpa only [d472, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d472, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6164 pattern childGuard
    simpa only [d472, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6166 (pattern : Twelve) (guard : d1858 pattern = 1) : d474 pattern ≤ (0 : Int) + d341 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d474, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6138 pattern childGuard
    simpa only [d474, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d474, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6165 pattern childGuard
    simpa only [d474, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6167 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d53 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6168 (pattern : Twelve) (guard : d1852 pattern = 1) : d439 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d439, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2180 pattern childGuard
    simpa only [d1852, d439, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d439, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6167 pattern childGuard
    simpa only [d1852, d439, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6169 (pattern : Twelve) (guard : d1858 pattern = 1) : d451 pattern ≤ (0 : Int) + d316 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d451, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6168 pattern childGuard
    simpa only [d1858, d451, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d451, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6145 pattern childGuard
    simpa only [d1858, d451, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6170 (pattern : Twelve) (guard : d1858 pattern = 1) : d459 pattern ≤ (0 : Int) + d328 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d459, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6142 pattern childGuard
    simpa only [d459, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d459, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6169 pattern childGuard
    simpa only [d459, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6171 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6172 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d432, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6171 pattern childGuard
    simpa only [d1852, d432, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6173 (pattern : Twelve) (guard : d1858 pattern = 1) : d432 pattern ≤ (0 : Int) + d317 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6172 pattern childGuard
    simpa only [d1858, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6150 pattern childGuard
    simpa only [d1858, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6174 (pattern : Twelve) (guard : d1858 pattern = 1) : d460 pattern ≤ (0 : Int) + d329 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d460, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6142 pattern childGuard
    simpa only [d460, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d460, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6173 pattern childGuard
    simpa only [d460, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6175 (pattern : Twelve) (guard : d1858 pattern = 1) : d467 pattern ≤ (0 : Int) + d336 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d467, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6170 pattern childGuard
    simpa only [d467, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d467, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6174 pattern childGuard
    simpa only [d467, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6176 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6177 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d441, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6176 pattern childGuard
    simpa only [d1852, d441, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6178 (pattern : Twelve) (guard : d1858 pattern = 1) : d441 pattern ≤ (0 : Int) + d318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6177 pattern childGuard
    simpa only [d1858, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6156 pattern childGuard
    simpa only [d1858, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6179 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6180 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d436, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6179 pattern childGuard
    simpa only [d1852, d436, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6181 (pattern : Twelve) (guard : d1858 pattern = 1) : d436 pattern ≤ (0 : Int) + d319 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6180 pattern childGuard
    simpa only [d1858, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6160 pattern childGuard
    simpa only [d1858, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6182 (pattern : Twelve) (guard : d1858 pattern = 1) : d461 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d461, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6178 pattern childGuard
    simpa only [d461, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d461, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6181 pattern childGuard
    simpa only [d461, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6183 (pattern : Twelve) (guard : d1858 pattern = 1) : d462 pattern ≤ (0 : Int) + d331 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d462, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6173 pattern childGuard
    simpa only [d462, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d462, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d462, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6184 (pattern : Twelve) (guard : d1858 pattern = 1) : d468 pattern ≤ (0 : Int) + d337 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d468, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6182 pattern childGuard
    simpa only [d468, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d468, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6183 pattern childGuard
    simpa only [d468, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6185 (pattern : Twelve) (guard : d1858 pattern = 1) : d472 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d472, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6175 pattern childGuard
    simpa only [d472, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d472, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6184 pattern childGuard
    simpa only [d472, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6186 (pattern : Twelve) (guard : d1858 pattern = 1) : d472 pattern ≤ (0 : Int) + d342 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6185 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6165 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6187 (pattern : Twelve) (guard : d1858 pattern = 1) : d475 pattern ≤ (0 : Int) + d343 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d475, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6166 pattern childGuard
    simpa only [d475, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d475, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6186 pattern childGuard
    simpa only [d475, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6188 (pattern : Twelve) (guard : d1858 pattern = 1) : d452 pattern ≤ (0 : Int) + d316 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d452, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6168 pattern childGuard
    simpa only [d1858, d452, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d452, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6150 pattern childGuard
    simpa only [d1858, d452, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6189 (pattern : Twelve) (guard : d1858 pattern = 1) : d463 pattern ≤ (0 : Int) + d328 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d463, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6142 pattern childGuard
    simpa only [d463, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d463, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6188 pattern childGuard
    simpa only [d463, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6190 (pattern : Twelve) (guard : d1858 pattern = 1) : d469 pattern ≤ (0 : Int) + d336 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d469, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6189 pattern childGuard
    simpa only [d469, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d469, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6174 pattern childGuard
    simpa only [d469, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6191 (pattern : Twelve) (guard : d0 pattern = 1) : d442 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6192 (pattern : Twelve) (guard : d1858 pattern = 1) : d453 pattern ≤ (0 : Int) + d318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d453, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6177 pattern childGuard
    simpa only [d1858, d453, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d453, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6191 pattern childGuard
    simpa only [d1858, d453, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6193 (pattern : Twelve) (guard : d0 pattern = 1) : d443 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6194 (pattern : Twelve) (guard : d1858 pattern = 1) : d454 pattern ≤ (0 : Int) + d319 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d454, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6180 pattern childGuard
    simpa only [d1858, d454, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d454, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6193 pattern childGuard
    simpa only [d1858, d454, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6195 (pattern : Twelve) (guard : d1858 pattern = 1) : d464 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d464, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6192 pattern childGuard
    simpa only [d464, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d464, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6194 pattern childGuard
    simpa only [d464, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6196 (pattern : Twelve) (guard : d1858 pattern = 1) : d470 pattern ≤ (0 : Int) + d337 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d470, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6195 pattern childGuard
    simpa only [d470, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d470, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6183 pattern childGuard
    simpa only [d470, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6197 (pattern : Twelve) (guard : d1858 pattern = 1) : d473 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d473, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6190 pattern childGuard
    simpa only [d473, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d473, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6196 pattern childGuard
    simpa only [d473, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6198 (pattern : Twelve) (guard : d1858 pattern = 1) : d452 pattern ≤ (0 : Int) + d312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d452, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6144 pattern childGuard
    simpa only [d1858, d452, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d452, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6150 pattern childGuard
    simpa only [d1858, d452, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6199 (pattern : Twelve) (guard : d1858 pattern = 1) : d463 pattern ≤ (0 : Int) + d324 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d463, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6142 pattern childGuard
    simpa only [d463, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d463, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6198 pattern childGuard
    simpa only [d463, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6200 (pattern : Twelve) (guard : d1858 pattern = 1) : d469 pattern ≤ (0 : Int) + d334 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d469, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6199 pattern childGuard
    simpa only [d469, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d469, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6152 pattern childGuard
    simpa only [d469, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6201 (pattern : Twelve) (guard : d1858 pattern = 1) : d453 pattern ≤ (0 : Int) + d314 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d453, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6155 pattern childGuard
    simpa only [d1858, d453, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d453, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6191 pattern childGuard
    simpa only [d1858, d453, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6202 (pattern : Twelve) (guard : d1858 pattern = 1) : d454 pattern ≤ (0 : Int) + d315 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d454, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6159 pattern childGuard
    simpa only [d1858, d454, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d454, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6193 pattern childGuard
    simpa only [d1858, d454, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6203 (pattern : Twelve) (guard : d1858 pattern = 1) : d464 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d464, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6201 pattern childGuard
    simpa only [d464, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d464, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6202 pattern childGuard
    simpa only [d464, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6204 (pattern : Twelve) (guard : d1858 pattern = 1) : d470 pattern ≤ (0 : Int) + d335 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d470, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6203 pattern childGuard
    simpa only [d470, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d470, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6163 pattern childGuard
    simpa only [d470, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6205 (pattern : Twelve) (guard : d1858 pattern = 1) : d473 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d473, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6200 pattern childGuard
    simpa only [d473, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d473, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6204 pattern childGuard
    simpa only [d473, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6206 (pattern : Twelve) (guard : d1858 pattern = 1) : d473 pattern ≤ (0 : Int) + d342 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6197 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6205 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6207 (pattern : Twelve) (guard : d1858 pattern = 1) : d476 pattern ≤ (0 : Int) + d344 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d476, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6187 pattern childGuard
    simpa only [d476, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d476, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6206 pattern childGuard
    simpa only [d476, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6208 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (0 : Int) + d824 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6209 (pattern : Twelve) (guard : d1852 pattern = 1) : d426 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d426, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d426, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d426, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6208 pattern childGuard
    simpa only [d1852, d426, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6210 (pattern : Twelve) (guard : d0 pattern = 1) : d1070 pattern ≤ (0 : Int) + d909 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6211 (pattern : Twelve) (guard : d1858 pattern = 1) : d1078 pattern ≤ (0 : Int) + d980 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1078, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6209 pattern childGuard
    simpa only [d1858, d1078, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1078, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6210 pattern childGuard
    simpa only [d1858, d1078, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6212 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6213 (pattern : Twelve) (guard : d1852 pattern = 1) : d1071 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1071, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d1071, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1071, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6212 pattern childGuard
    simpa only [d1852, d1071, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6214 (pattern : Twelve) (guard : d0 pattern = 1) : d1072 pattern ≤ (0 : Int) + d910 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6215 (pattern : Twelve) (guard : d1858 pattern = 1) : d1079 pattern ≤ (0 : Int) + d981 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1079, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6213 pattern childGuard
    simpa only [d1858, d1079, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1079, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6214 pattern childGuard
    simpa only [d1858, d1079, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6216 (pattern : Twelve) (guard : d1858 pattern = 1) : d1088 pattern ≤ (0 : Int) + d991 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1088, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6211 pattern childGuard
    simpa only [d1088, d991, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1088, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6215 pattern childGuard
    simpa only [d1088, d991, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6217 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d824 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6218 (pattern : Twelve) (guard : d1852 pattern = 1) : d430 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d430, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d430, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d430, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6217 pattern childGuard
    simpa only [d1852, d430, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6219 (pattern : Twelve) (guard : d0 pattern = 1) : d1073 pattern ≤ (0 : Int) + d910 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6220 (pattern : Twelve) (guard : d1858 pattern = 1) : d1080 pattern ≤ (0 : Int) + d982 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1080, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6218 pattern childGuard
    simpa only [d1858, d1080, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1080, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6219 pattern childGuard
    simpa only [d1858, d1080, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6221 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6222 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d432, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6221 pattern childGuard
    simpa only [d1852, d432, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6223 (pattern : Twelve) (guard : d0 pattern = 1) : d1072 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6224 (pattern : Twelve) (guard : d1858 pattern = 1) : d1081 pattern ≤ (0 : Int) + d983 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1081, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6222 pattern childGuard
    simpa only [d1858, d1081, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1081, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6223 pattern childGuard
    simpa only [d1858, d1081, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6225 (pattern : Twelve) (guard : d1858 pattern = 1) : d1089 pattern ≤ (0 : Int) + d992 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1089, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6220 pattern childGuard
    simpa only [d1089, d992, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1089, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6224 pattern childGuard
    simpa only [d1089, d992, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6226 (pattern : Twelve) (guard : d1858 pattern = 1) : d1095 pattern ≤ (0 : Int) + d1000 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1095, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6216 pattern childGuard
    simpa only [d1095, d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1095, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6225 pattern childGuard
    simpa only [d1095, d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6227 (pattern : Twelve) (guard : d0 pattern = 1) : d194 pattern ≤ (0 : Int) + d828 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6228 (pattern : Twelve) (guard : d1852 pattern = 1) : d434 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d434, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d434, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d434, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6227 pattern childGuard
    simpa only [d1852, d434, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6229 (pattern : Twelve) (guard : d0 pattern = 1) : d1074 pattern ≤ (0 : Int) + d911 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6230 (pattern : Twelve) (guard : d1858 pattern = 1) : d1082 pattern ≤ (0 : Int) + d984 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1082, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6228 pattern childGuard
    simpa only [d1858, d1082, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1082, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6229 pattern childGuard
    simpa only [d1858, d1082, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6231 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d829 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6232 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (0 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d436, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6231 pattern childGuard
    simpa only [d1852, d436, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6233 (pattern : Twelve) (guard : d0 pattern = 1) : d1075 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6234 (pattern : Twelve) (guard : d1858 pattern = 1) : d1083 pattern ≤ (0 : Int) + d985 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1083, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6232 pattern childGuard
    simpa only [d1858, d1083, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1083, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6233 pattern childGuard
    simpa only [d1858, d1083, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6235 (pattern : Twelve) (guard : d1858 pattern = 1) : d1090 pattern ≤ (0 : Int) + d993 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1090, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6230 pattern childGuard
    simpa only [d1090, d993, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1090, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6234 pattern childGuard
    simpa only [d1090, d993, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6236 (pattern : Twelve) (guard : d1858 pattern = 1) : d1091 pattern ≤ (0 : Int) + d994 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1091, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6224 pattern childGuard
    simpa only [d1091, d994, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1091, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d1091, d994, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6237 (pattern : Twelve) (guard : d1858 pattern = 1) : d1096 pattern ≤ (0 : Int) + d1001 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1096, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6235 pattern childGuard
    simpa only [d1096, d1001, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1096, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6236 pattern childGuard
    simpa only [d1096, d1001, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6238 (pattern : Twelve) (guard : d1858 pattern = 1) : d1099 pattern ≤ (0 : Int) + d1004 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1099, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6226 pattern childGuard
    simpa only [d1099, d1004, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1099, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6237 pattern childGuard
    simpa only [d1099, d1004, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6239 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d824 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6240 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d438, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6239 pattern childGuard
    simpa only [d1852, d438, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6241 (pattern : Twelve) (guard : d0 pattern = 1) : d1073 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6242 (pattern : Twelve) (guard : d1858 pattern = 1) : d1084 pattern ≤ (0 : Int) + d986 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1084, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6240 pattern childGuard
    simpa only [d1858, d1084, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1084, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6241 pattern childGuard
    simpa only [d1858, d1084, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6243 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d832 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6244 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d432, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6243 pattern childGuard
    simpa only [d1852, d432, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6245 (pattern : Twelve) (guard : d1858 pattern = 1) : d1081 pattern ≤ (0 : Int) + d987 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1081, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6244 pattern childGuard
    simpa only [d1858, d1081, d987, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1081, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6223 pattern childGuard
    simpa only [d1858, d1081, d987, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6246 (pattern : Twelve) (guard : d1858 pattern = 1) : d1092 pattern ≤ (0 : Int) + d995 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1092, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6242 pattern childGuard
    simpa only [d1092, d995, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1092, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6245 pattern childGuard
    simpa only [d1092, d995, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6247 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d834 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6248 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (0 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d441, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6247 pattern childGuard
    simpa only [d1852, d441, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6249 (pattern : Twelve) (guard : d0 pattern = 1) : d1074 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6250 (pattern : Twelve) (guard : d1858 pattern = 1) : d1085 pattern ≤ (0 : Int) + d988 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1085, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6248 pattern childGuard
    simpa only [d1858, d1085, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1085, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6249 pattern childGuard
    simpa only [d1858, d1085, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6251 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d836 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6252 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (0 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d436, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6251 pattern childGuard
    simpa only [d1852, d436, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6253 (pattern : Twelve) (guard : d1858 pattern = 1) : d1083 pattern ≤ (0 : Int) + d989 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1083, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6252 pattern childGuard
    simpa only [d1858, d1083, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1083, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6233 pattern childGuard
    simpa only [d1858, d1083, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6254 (pattern : Twelve) (guard : d1858 pattern = 1) : d1093 pattern ≤ (0 : Int) + d996 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1093, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6250 pattern childGuard
    simpa only [d1093, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1093, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6253 pattern childGuard
    simpa only [d1093, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6255 (pattern : Twelve) (guard : d1858 pattern = 1) : d1091 pattern ≤ (0 : Int) + d997 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1091, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6245 pattern childGuard
    simpa only [d1091, d997, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1091, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d1091, d997, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6256 (pattern : Twelve) (guard : d1858 pattern = 1) : d1097 pattern ≤ (0 : Int) + d1002 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1097, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6254 pattern childGuard
    simpa only [d1097, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1097, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6255 pattern childGuard
    simpa only [d1097, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6257 (pattern : Twelve) (guard : d1858 pattern = 1) : d1100 pattern ≤ (0 : Int) + d1005 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1100, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6246 pattern childGuard
    simpa only [d1100, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1100, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6256 pattern childGuard
    simpa only [d1100, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6258 (pattern : Twelve) (guard : d1858 pattern = 1) : d1102 pattern ≤ (0 : Int) + d1007 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1102, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6238 pattern childGuard
    simpa only [d1102, d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1102, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6257 pattern childGuard
    simpa only [d1102, d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6259 (pattern : Twelve) (guard : d1858 pattern = 1) : d1092 pattern ≤ (0 : Int) + d998 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1092, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6242 pattern childGuard
    simpa only [d1092, d998, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1092, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6224 pattern childGuard
    simpa only [d1092, d998, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6260 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d828 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6261 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d441, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6260 pattern childGuard
    simpa only [d1852, d441, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6262 (pattern : Twelve) (guard : d1858 pattern = 1) : d1085 pattern ≤ (0 : Int) + d990 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1085, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6261 pattern childGuard
    simpa only [d1858, d1085, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1085, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6249 pattern childGuard
    simpa only [d1858, d1085, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6263 (pattern : Twelve) (guard : d1858 pattern = 1) : d1093 pattern ≤ (0 : Int) + d999 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1093, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6262 pattern childGuard
    simpa only [d1093, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1093, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6234 pattern childGuard
    simpa only [d1093, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6264 (pattern : Twelve) (guard : d1858 pattern = 1) : d1097 pattern ≤ (0 : Int) + d1003 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1097, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6263 pattern childGuard
    simpa only [d1097, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1097, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6236 pattern childGuard
    simpa only [d1097, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6265 (pattern : Twelve) (guard : d1858 pattern = 1) : d1100 pattern ≤ (0 : Int) + d1006 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1100, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6259 pattern childGuard
    simpa only [d1100, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1100, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6264 pattern childGuard
    simpa only [d1100, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6266 (pattern : Twelve) (guard : d1858 pattern = 1) : d1100 pattern ≤ (0 : Int) + d1008 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6265 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6257 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6267 (pattern : Twelve) (guard : d1858 pattern = 1) : d1103 pattern ≤ (0 : Int) + d1009 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1103, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6258 pattern childGuard
    simpa only [d1103, d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1103, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6266 pattern childGuard
    simpa only [d1103, d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6268 (pattern : Twelve) (guard : d0 pattern = 1) : d1076 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6269 (pattern : Twelve) (guard : d1858 pattern = 1) : d1086 pattern ≤ (0 : Int) + d990 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1086, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6261 pattern childGuard
    simpa only [d1858, d1086, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1086, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6268 pattern childGuard
    simpa only [d1858, d1086, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6270 (pattern : Twelve) (guard : d0 pattern = 1) : d1077 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6271 (pattern : Twelve) (guard : d1858 pattern = 1) : d1087 pattern ≤ (0 : Int) + d985 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1087, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6232 pattern childGuard
    simpa only [d1858, d1087, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1087, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6270 pattern childGuard
    simpa only [d1858, d1087, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6272 (pattern : Twelve) (guard : d1858 pattern = 1) : d1094 pattern ≤ (0 : Int) + d999 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1094, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6269 pattern childGuard
    simpa only [d1094, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1094, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6271 pattern childGuard
    simpa only [d1094, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6273 (pattern : Twelve) (guard : d1858 pattern = 1) : d1098 pattern ≤ (0 : Int) + d1003 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1098, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6272 pattern childGuard
    simpa only [d1098, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1098, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6236 pattern childGuard
    simpa only [d1098, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6274 (pattern : Twelve) (guard : d1858 pattern = 1) : d1101 pattern ≤ (0 : Int) + d1006 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1101, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6259 pattern childGuard
    simpa only [d1101, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1101, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6273 pattern childGuard
    simpa only [d1101, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6275 (pattern : Twelve) (guard : d1858 pattern = 1) : d1086 pattern ≤ (0 : Int) + d988 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1086, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6248 pattern childGuard
    simpa only [d1858, d1086, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1086, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6268 pattern childGuard
    simpa only [d1858, d1086, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6276 (pattern : Twelve) (guard : d1858 pattern = 1) : d1087 pattern ≤ (0 : Int) + d989 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1087, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6252 pattern childGuard
    simpa only [d1858, d1087, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1087, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6270 pattern childGuard
    simpa only [d1858, d1087, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6277 (pattern : Twelve) (guard : d1858 pattern = 1) : d1094 pattern ≤ (0 : Int) + d996 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1094, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6275 pattern childGuard
    simpa only [d1094, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1094, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6276 pattern childGuard
    simpa only [d1094, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6278 (pattern : Twelve) (guard : d1858 pattern = 1) : d1098 pattern ≤ (0 : Int) + d1002 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1098, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6277 pattern childGuard
    simpa only [d1098, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1098, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6255 pattern childGuard
    simpa only [d1098, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6279 (pattern : Twelve) (guard : d1858 pattern = 1) : d1101 pattern ≤ (0 : Int) + d1005 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1101, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6246 pattern childGuard
    simpa only [d1101, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1101, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6278 pattern childGuard
    simpa only [d1101, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6280 (pattern : Twelve) (guard : d1858 pattern = 1) : d1101 pattern ≤ (0 : Int) + d1008 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6274 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6279 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6281 (pattern : Twelve) (guard : d1858 pattern = 1) : d1104 pattern ≤ (0 : Int) + d1010 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1104, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6267 pattern childGuard
    simpa only [d1104, d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1104, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6280 pattern childGuard
    simpa only [d1104, d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6282 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (0 : Int) + d1284 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6283 (pattern : Twelve) (guard : d1852 pattern = 1) : d1070 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1070, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d1070, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1070, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6282 pattern childGuard
    simpa only [d1852, d1070, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6284 (pattern : Twelve) (guard : d1858 pattern = 1) : d1472 pattern ≤ (0 : Int) + d1412 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1472, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6283 pattern childGuard
    simpa only [d1858, d1472, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1472, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c544 pattern childGuard
    simpa only [d1858, d1472, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6285 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6286 (pattern : Twelve) (guard : d1852 pattern = 1) : d1072 pattern ≤ (0 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1072, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2361 pattern childGuard
    simpa only [d1852, d1072, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1072, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6285 pattern childGuard
    simpa only [d1852, d1072, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6287 (pattern : Twelve) (guard : d1858 pattern = 1) : d1473 pattern ≤ (0 : Int) + d1413 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1473, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6286 pattern childGuard
    simpa only [d1858, d1473, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1473, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c547 pattern childGuard
    simpa only [d1858, d1473, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6288 (pattern : Twelve) (guard : d1858 pattern = 1) : d1479 pattern ≤ (0 : Int) + d1417 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1479, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6284 pattern childGuard
    simpa only [d1479, d1417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1479, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6287 pattern childGuard
    simpa only [d1479, d1417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6289 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1284 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6290 (pattern : Twelve) (guard : d1852 pattern = 1) : d1073 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1073, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d1073, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1073, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6289 pattern childGuard
    simpa only [d1852, d1073, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6291 (pattern : Twelve) (guard : d1858 pattern = 1) : d1474 pattern ≤ (0 : Int) + d1414 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1474, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6290 pattern childGuard
    simpa only [d1858, d1474, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1474, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c550 pattern childGuard
    simpa only [d1858, d1474, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6292 (pattern : Twelve) (guard : d1858 pattern = 1) : d1480 pattern ≤ (0 : Int) + d1418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1480, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6291 pattern childGuard
    simpa only [d1480, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1480, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6287 pattern childGuard
    simpa only [d1480, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6293 (pattern : Twelve) (guard : d1858 pattern = 1) : d1484 pattern ≤ (0 : Int) + d1421 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1484, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6288 pattern childGuard
    simpa only [d1484, d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1484, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6292 pattern childGuard
    simpa only [d1484, d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6294 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6295 (pattern : Twelve) (guard : d1852 pattern = 1) : d1074 pattern ≤ (0 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1074, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1852, d1074, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1074, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6294 pattern childGuard
    simpa only [d1852, d1074, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6296 (pattern : Twelve) (guard : d1858 pattern = 1) : d1475 pattern ≤ (0 : Int) + d1415 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1475, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6295 pattern childGuard
    simpa only [d1858, d1475, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1475, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c555 pattern childGuard
    simpa only [d1858, d1475, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6297 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1288 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6298 (pattern : Twelve) (guard : d1852 pattern = 1) : d1075 pattern ≤ (0 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1075, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2374 pattern childGuard
    simpa only [d1852, d1075, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1075, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6297 pattern childGuard
    simpa only [d1852, d1075, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6299 (pattern : Twelve) (guard : d1858 pattern = 1) : d1476 pattern ≤ (0 : Int) + d1416 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1476, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6298 pattern childGuard
    simpa only [d1858, d1476, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1476, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c558 pattern childGuard
    simpa only [d1858, d1476, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
