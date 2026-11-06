/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons079
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c11200 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d128, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11199 pattern childGuard
    simpa only [d1848, d128, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d128, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11144 pattern childGuard
    simpa only [d1848, d128, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11201 (pattern : Twelve) (guard : d1901 pattern = 1) : d388 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11142 pattern childGuard
    simpa only [d1901, d388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11200 pattern childGuard
    simpa only [d1901, d388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11202 (pattern : Twelve) (guard : d1901 pattern = 1) : d401 pattern ≤ (1 : Int) + d1910 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d401, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11194 pattern childGuard
    simpa only [d401, d1910, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d401, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11201 pattern childGuard
    simpa only [d401, d1910, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11203 (pattern : Twelve) (guard : d1901 pattern = 1) : d408 pattern ≤ (1 : Int) + d1911 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d408, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11189 pattern childGuard
    simpa only [d408, d1911, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d408, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11202 pattern childGuard
    simpa only [d408, d1911, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11204 (pattern : Twelve) (guard : d1901 pattern = 1) : d414 pattern ≤ (1 : Int) + d1912 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d414, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11153 pattern childGuard
    simpa only [d414, d1912, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d414, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11203 pattern childGuard
    simpa only [d414, d1912, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11205 (pattern : Twelve) (guard : d1901 pattern = 1) : d418 pattern ≤ (1 : Int) + d1914 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d418, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11204 pattern childGuard
    simpa only [d418, d1914, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d418, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11155 pattern childGuard
    simpa only [d418, d1914, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11206 (pattern : Twelve) (guard : d1901 pattern = 1) : d421 pattern ≤ (1 : Int) + d1915 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d421, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11179 pattern childGuard
    simpa only [d421, d1915, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d421, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11205 pattern childGuard
    simpa only [d421, d1915, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11207 (pattern : Twelve) (guard : d1901 pattern = 1) : d421 pattern ≤ (1 : Int) + d1919 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d421, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11170 pattern childGuard
    simpa only [d421, d1919, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d421, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11205 pattern childGuard
    simpa only [d421, d1919, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11208 (pattern : Twelve) (guard : d1901 pattern = 1) : d421 pattern ≤ (1 : Int) + d1920 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11206 pattern childGuard
    simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11207 pattern childGuard
    simpa only [d1920, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11209 (pattern : Twelve) (guard : d1901 pattern = 1) : d424 pattern ≤ (1 : Int) + d1920 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11182 pattern childGuard
    simpa only [d424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11208 pattern childGuard
    simpa only [d424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11210 (pattern : Twelve) (guard : d0 pattern = 1) : d366 pattern ≤ (1 : Int) + d1278 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11211 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d7 pattern := by
  omega
theorem c11212 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d1 pattern := by
  omega
theorem c11213 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d2 pattern := by
  change (1 : Int) ≤ (1 : Int) + 2
  decide
theorem c11214 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11213 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11215 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (1 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11211 pattern childGuard
    simpa only [d814, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11214 pattern childGuard
    simpa only [d814, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11216 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11217 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11215 pattern childGuard
    simpa only [d1848, d818, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11216 pattern childGuard
    simpa only [d1848, d818, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11218 (pattern : Twelve) (guard : d1901 pattern = 1) : d1030 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11210 pattern childGuard
    simpa only [d1901, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11217 pattern childGuard
    simpa only [d1901, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11219 (pattern : Twelve) (guard : d1901 pattern = 1) : d1038 pattern ≤ (1 : Int) + d1921 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1038, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11065 pattern childGuard
    simpa only [d1038, d1921, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1038, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11218 pattern childGuard
    simpa only [d1038, d1921, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11220 (pattern : Twelve) (guard : d0 pattern = 1) : d366 pattern ≤ (1 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11221 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) ≤ (1 : Int) + 2
  decide
theorem c11222 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11221 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11223 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d3 pattern := by
  change (1 : Int) ≤ (1 : Int) + 3
  decide
theorem c11224 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11223 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11225 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11222 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11224 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11226 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11227 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11226 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11228 (pattern : Twelve) (guard : d1901 pattern = 1) : d1031 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11220 pattern childGuard
    simpa only [d1901, d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11227 pattern childGuard
    simpa only [d1901, d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11229 (pattern : Twelve) (guard : d0 pattern = 1) : d29 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11230 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d6 pattern := by
  change (2 : Int) ≤ (1 : Int) + 6
  decide
theorem c11231 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d6 pattern := by
  change (4 : Int) ≤ (1 : Int) + 6
  decide
theorem c11232 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11230 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11233 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d6 pattern := by
  change (3 : Int) ≤ (1 : Int) + 6
  decide
theorem c11234 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (1 : Int) + d6 pattern := by
  change (5 : Int) ≤ (1 : Int) + 6
  decide
theorem c11235 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11236 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11232 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11235 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11237 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11238 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11236 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11239 (pattern : Twelve) (guard : d1901 pattern = 1) : d1032 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11229 pattern childGuard
    simpa only [d1901, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11238 pattern childGuard
    simpa only [d1901, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11240 (pattern : Twelve) (guard : d1901 pattern = 1) : d1039 pattern ≤ (1 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1039, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11228 pattern childGuard
    simpa only [d1039, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1039, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11239 pattern childGuard
    simpa only [d1039, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11241 (pattern : Twelve) (guard : d1901 pattern = 1) : d1048 pattern ≤ (1 : Int) + d1922 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1048, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11219 pattern childGuard
    simpa only [d1048, d1922, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1048, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11240 pattern childGuard
    simpa only [d1048, d1922, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11242 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (1 : Int) + d1279 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11243 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1276 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11244 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (1 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11215 pattern childGuard
    simpa only [d1848, d818, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11243 pattern childGuard
    simpa only [d1848, d818, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11245 (pattern : Twelve) (guard : d1901 pattern = 1) : d1033 pattern ≤ (1 : Int) + d1279 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11242 pattern childGuard
    simpa only [d1901, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11244 pattern childGuard
    simpa only [d1901, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11246 (pattern : Twelve) (guard : d1901 pattern = 1) : d1040 pattern ≤ (1 : Int) + d1923 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1040, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11083 pattern childGuard
    simpa only [d1040, d1923, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1040, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11245 pattern childGuard
    simpa only [d1040, d1923, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11247 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d1848, d36, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11068 pattern childGuard
    simpa only [d1848, d36, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11248 (pattern : Twelve) (guard : d1901 pattern = 1) : d36 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11084 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11247 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11249 (pattern : Twelve) (guard : d1901 pattern = 1) : d1041 pattern ≤ (1 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1041, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11248 pattern childGuard
    simpa only [d1041, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1041, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11239 pattern childGuard
    simpa only [d1041, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11250 (pattern : Twelve) (guard : d1901 pattern = 1) : d1049 pattern ≤ (1 : Int) + d1924 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1049, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11246 pattern childGuard
    simpa only [d1049, d1924, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1049, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11249 pattern childGuard
    simpa only [d1049, d1924, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11251 (pattern : Twelve) (guard : d1901 pattern = 1) : d1054 pattern ≤ (1 : Int) + d1925 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1054, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11241 pattern childGuard
    simpa only [d1054, d1925, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1054, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11250 pattern childGuard
    simpa only [d1054, d1925, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11252 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (1 : Int) + d1278 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11253 (pattern : Twelve) (guard : d1901 pattern = 1) : d1033 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11252 pattern childGuard
    simpa only [d1901, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11217 pattern childGuard
    simpa only [d1901, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11254 (pattern : Twelve) (guard : d1901 pattern = 1) : d1040 pattern ≤ (1 : Int) + d1921 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1040, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11101 pattern childGuard
    simpa only [d1040, d1921, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1040, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11253 pattern childGuard
    simpa only [d1040, d1921, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11255 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (1 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11256 (pattern : Twelve) (guard : d1901 pattern = 1) : d36 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11255 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11227 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11257 (pattern : Twelve) (guard : d1901 pattern = 1) : d1041 pattern ≤ (1 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1041, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11256 pattern childGuard
    simpa only [d1041, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1041, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11239 pattern childGuard
    simpa only [d1041, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11258 (pattern : Twelve) (guard : d1901 pattern = 1) : d1049 pattern ≤ (1 : Int) + d1922 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1049, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11254 pattern childGuard
    simpa only [d1049, d1922, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1049, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11257 pattern childGuard
    simpa only [d1049, d1922, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11259 (pattern : Twelve) (guard : d1901 pattern = 1) : d1042 pattern ≤ (1 : Int) + d1923 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1042, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11111 pattern childGuard
    simpa only [d1042, d1923, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1042, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11245 pattern childGuard
    simpa only [d1042, d1923, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11260 (pattern : Twelve) (guard : d1901 pattern = 1) : d1050 pattern ≤ (1 : Int) + d1924 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1050, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11259 pattern childGuard
    simpa only [d1050, d1924, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1050, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11249 pattern childGuard
    simpa only [d1050, d1924, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11261 (pattern : Twelve) (guard : d1901 pattern = 1) : d1055 pattern ≤ (1 : Int) + d1925 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1055, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11258 pattern childGuard
    simpa only [d1055, d1925, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1055, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11260 pattern childGuard
    simpa only [d1055, d1925, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11262 (pattern : Twelve) (guard : d1901 pattern = 1) : d1060 pattern ≤ (1 : Int) + d1925 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11251 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11261 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11263 (pattern : Twelve) (guard : d1901 pattern = 1) : d1043 pattern ≤ (1 : Int) + d1923 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1043, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11123 pattern childGuard
    simpa only [d1043, d1923, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1043, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11245 pattern childGuard
    simpa only [d1043, d1923, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11264 (pattern : Twelve) (guard : d1901 pattern = 1) : d1051 pattern ≤ (1 : Int) + d1924 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1051, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11263 pattern childGuard
    simpa only [d1051, d1924, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1051, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11249 pattern childGuard
    simpa only [d1051, d1924, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11265 (pattern : Twelve) (guard : d0 pattern = 1) : d40 pattern ≤ (1 : Int) + d1282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11266 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d9 pattern := by
  omega
theorem c11267 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d4 pattern := by
  change (3 : Int) ≤ (1 : Int) + 4
  decide
theorem c11268 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11267 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11269 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (1 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11266 pattern childGuard
    simpa only [d815, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11268 pattern childGuard
    simpa only [d815, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11270 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1277 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11271 (pattern : Twelve) (guard : d1848 pattern = 1) : d820 pattern ≤ (1 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d820, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11269 pattern childGuard
    simpa only [d1848, d820, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d820, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11270 pattern childGuard
    simpa only [d1848, d820, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11272 (pattern : Twelve) (guard : d1901 pattern = 1) : d1034 pattern ≤ (1 : Int) + d1282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11265 pattern childGuard
    simpa only [d1901, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11271 pattern childGuard
    simpa only [d1901, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11273 (pattern : Twelve) (guard : d1901 pattern = 1) : d1044 pattern ≤ (1 : Int) + d1926 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1044, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11141 pattern childGuard
    simpa only [d1044, d1926, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1044, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11272 pattern childGuard
    simpa only [d1044, d1926, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11274 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d4 pattern := by
  change (2 : Int) ≤ (1 : Int) + 4
  decide
theorem c11275 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11127 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11274 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11276 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d5 pattern := by
  change (3 : Int) ≤ (1 : Int) + 5
  decide
theorem c11277 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11276 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11278 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11275 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11277 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11279 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11278 pattern childGuard
    simpa only [d1848, d40, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11144 pattern childGuard
    simpa only [d1848, d40, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11280 (pattern : Twelve) (guard : d1901 pattern = 1) : d40 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11142 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11279 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11281 (pattern : Twelve) (guard : d0 pattern = 1) : d42 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11282 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  omega
theorem c11283 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11284 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11285 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11283 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11284 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11286 (pattern : Twelve) (guard : d1848 pattern = 1) : d822 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11285 pattern childGuard
    simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11287 (pattern : Twelve) (guard : d1901 pattern = 1) : d1035 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11281 pattern childGuard
    simpa only [d1901, d1035, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11286 pattern childGuard
    simpa only [d1901, d1035, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11288 (pattern : Twelve) (guard : d1901 pattern = 1) : d1045 pattern ≤ (1 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1045, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11280 pattern childGuard
    simpa only [d1045, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1045, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11287 pattern childGuard
    simpa only [d1045, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11289 (pattern : Twelve) (guard : d1901 pattern = 1) : d1052 pattern ≤ (1 : Int) + d1927 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1052, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11273 pattern childGuard
    simpa only [d1052, d1927, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1052, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11288 pattern childGuard
    simpa only [d1052, d1927, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11290 (pattern : Twelve) (guard : d1901 pattern = 1) : d1056 pattern ≤ (1 : Int) + d1928 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1056, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11264 pattern childGuard
    simpa only [d1056, d1928, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1056, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11289 pattern childGuard
    simpa only [d1056, d1928, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11291 (pattern : Twelve) (guard : d1901 pattern = 1) : d1057 pattern ≤ (1 : Int) + d1929 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1057, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11260 pattern childGuard
    simpa only [d1057, d1929, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1057, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11154 pattern childGuard
    simpa only [d1057, d1929, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11292 (pattern : Twelve) (guard : d1901 pattern = 1) : d1061 pattern ≤ (1 : Int) + d1930 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1061, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11290 pattern childGuard
    simpa only [d1061, d1930, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1061, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11291 pattern childGuard
    simpa only [d1061, d1930, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11293 (pattern : Twelve) (guard : d1901 pattern = 1) : d1064 pattern ≤ (1 : Int) + d1931 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1064, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11262 pattern childGuard
    simpa only [d1064, d1931, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1064, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11292 pattern childGuard
    simpa only [d1064, d1931, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11294 (pattern : Twelve) (guard : d1901 pattern = 1) : d1042 pattern ≤ (1 : Int) + d1921 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1042, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11176 pattern childGuard
    simpa only [d1042, d1921, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1042, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11253 pattern childGuard
    simpa only [d1042, d1921, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11295 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (1 : Int) + d1283 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11296 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d1848, d36, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11078 pattern childGuard
    simpa only [d1848, d36, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11297 (pattern : Twelve) (guard : d1901 pattern = 1) : d36 pattern ≤ (1 : Int) + d1283 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11295 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11296 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11298 (pattern : Twelve) (guard : d1901 pattern = 1) : d1041 pattern ≤ (1 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1041, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11297 pattern childGuard
    simpa only [d1041, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1041, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11239 pattern childGuard
    simpa only [d1041, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11299 (pattern : Twelve) (guard : d1901 pattern = 1) : d1050 pattern ≤ (1 : Int) + d1932 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1050, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11294 pattern childGuard
    simpa only [d1050, d1932, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1050, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11298 pattern childGuard
    simpa only [d1050, d1932, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11300 (pattern : Twelve) (guard : d1901 pattern = 1) : d1050 pattern ≤ (1 : Int) + d1933 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11299 pattern childGuard
    simpa only [d1933, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11260 pattern childGuard
    simpa only [d1933, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11301 (pattern : Twelve) (guard : d1901 pattern = 1) : d1058 pattern ≤ (1 : Int) + d1928 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1058, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11260 pattern childGuard
    simpa only [d1058, d1928, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1058, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11289 pattern childGuard
    simpa only [d1058, d1928, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11302 (pattern : Twelve) (guard : d1901 pattern = 1) : d1062 pattern ≤ (1 : Int) + d1930 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1062, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11301 pattern childGuard
    simpa only [d1062, d1930, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1062, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11291 pattern childGuard
    simpa only [d1062, d1930, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11303 (pattern : Twelve) (guard : d1901 pattern = 1) : d1065 pattern ≤ (1 : Int) + d1934 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1065, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11300 pattern childGuard
    simpa only [d1065, d1934, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1065, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11302 pattern childGuard
    simpa only [d1065, d1934, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11304 (pattern : Twelve) (guard : d1901 pattern = 1) : d1067 pattern ≤ (1 : Int) + d1935 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1067, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11293 pattern childGuard
    simpa only [d1067, d1935, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1067, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11303 pattern childGuard
    simpa only [d1067, d1935, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11305 (pattern : Twelve) (guard : d1901 pattern = 1) : d1050 pattern ≤ (1 : Int) + d1922 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1050, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11294 pattern childGuard
    simpa only [d1050, d1922, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1050, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11257 pattern childGuard
    simpa only [d1050, d1922, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11306 (pattern : Twelve) (guard : d1901 pattern = 1) : d1050 pattern ≤ (1 : Int) + d1925 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11305 pattern childGuard
    simpa only [d1925, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11260 pattern childGuard
    simpa only [d1925, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11307 (pattern : Twelve) (guard : d1901 pattern = 1) : d1065 pattern ≤ (1 : Int) + d1931 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1065, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11306 pattern childGuard
    simpa only [d1065, d1931, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1065, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11302 pattern childGuard
    simpa only [d1065, d1931, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11308 (pattern : Twelve) (guard : d1901 pattern = 1) : d1065 pattern ≤ (1 : Int) + d1935 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11307 pattern childGuard
    simpa only [d1935, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11303 pattern childGuard
    simpa only [d1935, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11309 (pattern : Twelve) (guard : d1901 pattern = 1) : d1068 pattern ≤ (1 : Int) + d1935 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11304 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11308 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11310 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (1 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11184 pattern childGuard
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11195 pattern childGuard
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11311 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (1 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11185 pattern childGuard
    simpa only [d873, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11310 pattern childGuard
    simpa only [d873, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11312 (pattern : Twelve) (guard : d1848 pattern = 1) : d880 pattern ≤ (1 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d880, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11311 pattern childGuard
    simpa only [d1848, d880, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d880, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11270 pattern childGuard
    simpa only [d1848, d880, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11313 (pattern : Twelve) (guard : d1901 pattern = 1) : d1036 pattern ≤ (1 : Int) + d1282 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11265 pattern childGuard
    simpa only [d1901, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11312 pattern childGuard
    simpa only [d1901, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11314 (pattern : Twelve) (guard : d1901 pattern = 1) : d1046 pattern ≤ (1 : Int) + d1926 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1046, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11141 pattern childGuard
    simpa only [d1046, d1926, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1046, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11313 pattern childGuard
    simpa only [d1046, d1926, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11315 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11267 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11316 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (1 : Int) + d5 pattern := by
  change (4 : Int) ≤ (1 : Int) + 5
  decide
theorem c11317 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d117, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11316 pattern childGuard
    simpa only [d117, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11318 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11315 pattern childGuard
    simpa only [d119, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11317 pattern childGuard
    simpa only [d119, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11319 (pattern : Twelve) (guard : d1848 pattern = 1) : d125 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d125, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11318 pattern childGuard
    simpa only [d1848, d125, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d125, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11144 pattern childGuard
    simpa only [d1848, d125, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11320 (pattern : Twelve) (guard : d1901 pattern = 1) : d1037 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11142 pattern childGuard
    simpa only [d1901, d1037, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11319 pattern childGuard
    simpa only [d1901, d1037, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11321 (pattern : Twelve) (guard : d1848 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  omega
theorem c11322 (pattern : Twelve) (guard : d1901 pattern = 1) : d889 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11281 pattern childGuard
    simpa only [d1901, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d1901, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11323 (pattern : Twelve) (guard : d1901 pattern = 1) : d1047 pattern ≤ (1 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1047, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11320 pattern childGuard
    simpa only [d1047, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1047, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11322 pattern childGuard
    simpa only [d1047, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11324 (pattern : Twelve) (guard : d1901 pattern = 1) : d1053 pattern ≤ (1 : Int) + d1927 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1053, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11314 pattern childGuard
    simpa only [d1053, d1927, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1053, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11323 pattern childGuard
    simpa only [d1053, d1927, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11325 (pattern : Twelve) (guard : d1901 pattern = 1) : d1059 pattern ≤ (1 : Int) + d1928 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1059, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11260 pattern childGuard
    simpa only [d1059, d1928, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1059, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11324 pattern childGuard
    simpa only [d1059, d1928, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11326 (pattern : Twelve) (guard : d1901 pattern = 1) : d1063 pattern ≤ (1 : Int) + d1930 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1063, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11325 pattern childGuard
    simpa only [d1063, d1930, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1063, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11291 pattern childGuard
    simpa only [d1063, d1930, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11327 (pattern : Twelve) (guard : d1901 pattern = 1) : d1066 pattern ≤ (1 : Int) + d1931 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1066, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11306 pattern childGuard
    simpa only [d1066, d1931, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1066, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11326 pattern childGuard
    simpa only [d1066, d1931, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11328 (pattern : Twelve) (guard : d1901 pattern = 1) : d1066 pattern ≤ (1 : Int) + d1934 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1066, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11300 pattern childGuard
    simpa only [d1066, d1934, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1066, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11326 pattern childGuard
    simpa only [d1066, d1934, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11329 (pattern : Twelve) (guard : d1901 pattern = 1) : d1066 pattern ≤ (1 : Int) + d1935 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11327 pattern childGuard
    simpa only [d1935, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11328 pattern childGuard
    simpa only [d1935, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11330 (pattern : Twelve) (guard : d1901 pattern = 1) : d1069 pattern ≤ (1 : Int) + d1935 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11309 pattern childGuard
    simpa only [d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11329 pattern childGuard
    simpa only [d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11331 (pattern : Twelve) (guard : d0 pattern = 1) : d1444 pattern ≤ (1 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11332 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11223 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11333 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11213 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11274 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11334 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11332 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11333 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11335 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11336 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11335 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11337 (pattern : Twelve) (guard : d1901 pattern = 1) : d1445 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11331 pattern childGuard
    simpa only [d1901, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11336 pattern childGuard
    simpa only [d1901, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11338 (pattern : Twelve) (guard : d1901 pattern = 1) : d1448 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1448, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11228 pattern childGuard
    simpa only [d1448, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d1448, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11337 pattern childGuard
    simpa only [d1448, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11339 (pattern : Twelve) (guard : d0 pattern = 1) : d29 pattern ≤ (1 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
