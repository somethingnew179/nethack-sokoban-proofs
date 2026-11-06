/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GoalComparisons01
import NetHack.Sokoban41.Comparisons35
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem goalC320 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC321 (pattern : Ten) (guard : d800 pattern = 1) : d289 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d289, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC254 pattern childGuard
    simpa only [d800, d289, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d289, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC320 pattern childGuard
    simpa only [d800, d289, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC322 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC323 (pattern : Ten) (guard : d799 pattern = 1) : d290 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d290, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC252 pattern childGuard
    simpa only [d799, d290, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d290, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC322 pattern childGuard
    simpa only [d799, d290, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC324 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC325 (pattern : Ten) (guard : d800 pattern = 1) : d291 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d291, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC323 pattern childGuard
    simpa only [d800, d291, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d291, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC324 pattern childGuard
    simpa only [d800, d291, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC326 (pattern : Ten) (guard : d358 pattern = 1) : d292 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5611 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC327 (pattern : Ten) (guard : d794 pattern = 1) : d293 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d794, d293, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC326 pattern childGuard
    simpa only [d794, d293, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d794, d293, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC243 pattern childGuard
    simpa only [d794, d293, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC328 (pattern : Ten) (guard : d795 pattern = 1) : d294 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d794 pattern = 1 := by simpa only [d795, d294, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC327 pattern childGuard
    simpa only [d795, d294, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d795, d294, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC245 pattern childGuard
    simpa only [d795, d294, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC329 (pattern : Ten) (guard : d796 pattern = 1) : d295 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d795 pattern = 1 := by simpa only [d796, d295, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC328 pattern childGuard
    simpa only [d796, d295, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d796, d295, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC247 pattern childGuard
    simpa only [d796, d295, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC330 (pattern : Ten) (guard : d797 pattern = 1) : d296 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d296, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC329 pattern childGuard
    simpa only [d797, d296, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d296, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC249 pattern childGuard
    simpa only [d797, d296, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC331 (pattern : Ten) (guard : d798 pattern = 1) : d297 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d297, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC330 pattern childGuard
    simpa only [d798, d297, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d297, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC251 pattern childGuard
    simpa only [d798, d297, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC332 (pattern : Ten) (guard : d799 pattern = 1) : d298 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d298, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC331 pattern childGuard
    simpa only [d799, d298, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d298, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC253 pattern childGuard
    simpa only [d799, d298, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC333 (pattern : Ten) (guard : d0 pattern = 1) : d299 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC334 (pattern : Ten) (guard : d800 pattern = 1) : d300 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d300, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC332 pattern childGuard
    simpa only [d800, d300, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d300, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC333 pattern childGuard
    simpa only [d800, d300, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC335 (pattern : Ten) (guard : d795 pattern = 1) : d173 pattern ≤ (0 : Int) + d802 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d794 pattern = 1 := by simpa only [d795, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC285 pattern childGuard
    simpa only [d795, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d795, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC231 pattern childGuard
    simpa only [d795, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC336 (pattern : Ten) (guard : d796 pattern = 1) : d302 pattern ≤ (0 : Int) + d803 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d795 pattern = 1 := by simpa only [d796, d302, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC335 pattern childGuard
    simpa only [d796, d302, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d796, d302, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC233 pattern childGuard
    simpa only [d796, d302, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC337 (pattern : Ten) (guard : d797 pattern = 1) : d304 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d304, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC336 pattern childGuard
    simpa only [d797, d304, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d304, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC235 pattern childGuard
    simpa only [d797, d304, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC338 (pattern : Ten) (guard : d0 pattern = 1) : d305 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC339 (pattern : Ten) (guard : d798 pattern = 1) : d306 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d306, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC337 pattern childGuard
    simpa only [d798, d306, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d306, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC338 pattern childGuard
    simpa only [d798, d306, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC340 (pattern : Ten) (guard : d799 pattern = 1) : d307 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d307, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC339 pattern childGuard
    simpa only [d799, d307, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d307, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC239 pattern childGuard
    simpa only [d799, d307, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC341 (pattern : Ten) (guard : d800 pattern = 1) : d308 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d308, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC340 pattern childGuard
    simpa only [d800, d308, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d308, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC241 pattern childGuard
    simpa only [d800, d308, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC342 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d72 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC343 (pattern : Ten) (guard : d797 pattern = 1) : d211 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d211, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC248 pattern childGuard
    simpa only [d797, d211, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d211, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC342 pattern childGuard
    simpa only [d797, d211, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC344 (pattern : Ten) (guard : d798 pattern = 1) : d326 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d326, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC343 pattern childGuard
    simpa only [d798, d326, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d326, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC251 pattern childGuard
    simpa only [d798, d326, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC345 (pattern : Ten) (guard : d0 pattern = 1) : d327 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC346 (pattern : Ten) (guard : d799 pattern = 1) : d329 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d329, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC344 pattern childGuard
    simpa only [d799, d329, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d329, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC345 pattern childGuard
    simpa only [d799, d329, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC347 (pattern : Ten) (guard : d0 pattern = 1) : d330 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC348 (pattern : Ten) (guard : d800 pattern = 1) : d331 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d331, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC346 pattern childGuard
    simpa only [d800, d331, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d331, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC347 pattern childGuard
    simpa only [d800, d331, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC349 (pattern : Ten) (guard : d0 pattern = 1) : d324 pattern ≤ (0 : Int) + d72 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC350 (pattern : Ten) (guard : d797 pattern = 1) : d332 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d332, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC248 pattern childGuard
    simpa only [d797, d332, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d332, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC349 pattern childGuard
    simpa only [d797, d332, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC351 (pattern : Ten) (guard : d0 pattern = 1) : d332 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC352 (pattern : Ten) (guard : d798 pattern = 1) : d332 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC350 pattern childGuard
    simpa only [d798, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC351 pattern childGuard
    simpa only [d798, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC353 (pattern : Ten) (guard : d0 pattern = 1) : d336 pattern ≤ (0 : Int) + d812 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC354 (pattern : Ten) (guard : d799 pattern = 1) : d338 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d338, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC352 pattern childGuard
    simpa only [d799, d338, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d338, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC353 pattern childGuard
    simpa only [d799, d338, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC355 (pattern : Ten) (guard : d0 pattern = 1) : d339 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC356 (pattern : Ten) (guard : d800 pattern = 1) : d340 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d340, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC354 pattern childGuard
    simpa only [d800, d340, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d340, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC355 pattern childGuard
    simpa only [d800, d340, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC357 (pattern : Ten) (guard : d0 pattern = 1) : d325 pattern ≤ (0 : Int) + d72 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC358 (pattern : Ten) (guard : d797 pattern = 1) : d344 pattern ≤ (0 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d796 pattern = 1 := by simpa only [d797, d344, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC248 pattern childGuard
    simpa only [d797, d344, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d797, d344, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC357 pattern childGuard
    simpa only [d797, d344, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC359 (pattern : Ten) (guard : d0 pattern = 1) : d345 pattern ≤ (0 : Int) + d808 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC360 (pattern : Ten) (guard : d798 pattern = 1) : d346 pattern ≤ (0 : Int) + d809 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d797 pattern = 1 := by simpa only [d798, d346, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC358 pattern childGuard
    simpa only [d798, d346, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d798, d346, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC359 pattern childGuard
    simpa only [d798, d346, d809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC361 (pattern : Ten) (guard : d799 pattern = 1) : d347 pattern ≤ (0 : Int) + d813 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d798 pattern = 1 := by simpa only [d799, d347, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC360 pattern childGuard
    simpa only [d799, d347, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d799, d347, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC353 pattern childGuard
    simpa only [d799, d347, d813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC362 (pattern : Ten) (guard : d0 pattern = 1) : d348 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC363 (pattern : Ten) (guard : d800 pattern = 1) : d349 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d799 pattern = 1 := by simpa only [d800, d349, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC361 pattern childGuard
    simpa only [d800, d349, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d800, d349, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC362 pattern childGuard
    simpa only [d800, d349, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
