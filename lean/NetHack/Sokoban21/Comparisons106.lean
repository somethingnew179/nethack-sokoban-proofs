/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons105
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c14840 (pattern : Twelve) (guard : d2301 pattern = 1) : d968 pattern ≤ (2 : Int) + d2440 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d968, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14817 pattern childGuard
    simpa only [d968, d2440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d968, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14829 pattern childGuard
    simpa only [d968, d2440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14841 (pattern : Twelve) (guard : d2301 pattern = 1) : d972 pattern ≤ (2 : Int) + d2442 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d972, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14840 pattern childGuard
    simpa only [d972, d2442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d972, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14831 pattern childGuard
    simpa only [d972, d2442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14842 (pattern : Twelve) (guard : d2301 pattern = 1) : d974 pattern ≤ (2 : Int) + d2443 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d974, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14839 pattern childGuard
    simpa only [d974, d2443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d974, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14841 pattern childGuard
    simpa only [d974, d2443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14843 (pattern : Twelve) (guard : d2301 pattern = 1) : d976 pattern ≤ (2 : Int) + d2443 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14833 pattern childGuard
    simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14842 pattern childGuard
    simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14844 (pattern : Twelve) (guard : d2301 pattern = 1) : d962 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d962, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14834 pattern childGuard
    simpa only [d962, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d962, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14814 pattern childGuard
    simpa only [d962, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14845 (pattern : Twelve) (guard : d2301 pattern = 1) : d969 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14844 pattern childGuard
    simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14817 pattern childGuard
    simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14846 (pattern : Twelve) (guard : d2301 pattern = 1) : d975 pattern ≤ (2 : Int) + d2443 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d975, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14845 pattern childGuard
    simpa only [d975, d2443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d975, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14841 pattern childGuard
    simpa only [d975, d2443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14847 (pattern : Twelve) (guard : d2301 pattern = 1) : d977 pattern ≤ (2 : Int) + d2443 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14846 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14842 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14848 (pattern : Twelve) (guard : d2301 pattern = 1) : d978 pattern ≤ (2 : Int) + d2443 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14843 pattern childGuard
    simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14847 pattern childGuard
    simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14849 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d873 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14850 (pattern : Twelve) (guard : d2301 pattern = 1) : d251 pattern ≤ (2 : Int) + d2384 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d251, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14320 pattern childGuard
    simpa only [d2301, d251, d2384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d251, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14849 pattern childGuard
    simpa only [d2301, d251, d2384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14851 (pattern : Twelve) (guard : d2301 pattern = 1) : d267 pattern ≤ (2 : Int) + d2444 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d267, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14742 pattern childGuard
    simpa only [d267, d2444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d267, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14850 pattern childGuard
    simpa only [d267, d2444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14852 (pattern : Twelve) (guard : d2301 pattern = 1) : d251 pattern ≤ (2 : Int) + d2445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d251, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14320 pattern childGuard
    simpa only [d2301, d251, d2445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d251, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14779 pattern childGuard
    simpa only [d2301, d251, d2445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14853 (pattern : Twelve) (guard : d2301 pattern = 1) : d945 pattern ≤ (2 : Int) + d1690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d945, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14405 pattern childGuard
    simpa only [d2301, d945, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d945, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2301, d945, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14854 (pattern : Twelve) (guard : d2301 pattern = 1) : d952 pattern ≤ (2 : Int) + d2446 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d952, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14852 pattern childGuard
    simpa only [d952, d2446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d952, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14853 pattern childGuard
    simpa only [d952, d2446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14855 (pattern : Twelve) (guard : d2301 pattern = 1) : d960 pattern ≤ (2 : Int) + d2447 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d960, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14851 pattern childGuard
    simpa only [d960, d2447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d960, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14854 pattern childGuard
    simpa only [d960, d2447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14856 (pattern : Twelve) (guard : d2301 pattern = 1) : d968 pattern ≤ (2 : Int) + d2448 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d968, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14817 pattern childGuard
    simpa only [d968, d2448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d968, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14855 pattern childGuard
    simpa only [d968, d2448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14857 (pattern : Twelve) (guard : d2301 pattern = 1) : d972 pattern ≤ (2 : Int) + d2449 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d972, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14856 pattern childGuard
    simpa only [d972, d2449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d972, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14831 pattern childGuard
    simpa only [d972, d2449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14858 (pattern : Twelve) (guard : d2301 pattern = 1) : d975 pattern ≤ (2 : Int) + d2450 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d975, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14845 pattern childGuard
    simpa only [d975, d2450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d975, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14857 pattern childGuard
    simpa only [d975, d2450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14859 (pattern : Twelve) (guard : d2301 pattern = 1) : d974 pattern ≤ (2 : Int) + d2450 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d974, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14839 pattern childGuard
    simpa only [d974, d2450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d974, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14857 pattern childGuard
    simpa only [d974, d2450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14860 (pattern : Twelve) (guard : d2301 pattern = 1) : d977 pattern ≤ (2 : Int) + d2450 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14858 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14859 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14861 (pattern : Twelve) (guard : d2301 pattern = 1) : d979 pattern ≤ (2 : Int) + d2451 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d979, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14848 pattern childGuard
    simpa only [d979, d2451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d979, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14860 pattern childGuard
    simpa only [d979, d2451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14862 (pattern : Twelve) (guard : d0 pattern = 1) : d1275 pattern ≤ (2 : Int) + d1275 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14863 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (2 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13321 pattern childGuard
    simpa only [d872, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14026 pattern childGuard
    simpa only [d872, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14864 (pattern : Twelve) (guard : d26 pattern = 1) : d1278 pattern ≤ (2 : Int) + d1275 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14862 pattern childGuard
    simpa only [d26, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14863 pattern childGuard
    simpa only [d26, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14865 (pattern : Twelve) (guard : d2301 pattern = 1) : d1380 pattern ≤ (2 : Int) + d2390 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1380, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14864 pattern childGuard
    simpa only [d2301, d1380, d2390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1380, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14030 pattern childGuard
    simpa only [d2301, d1380, d2390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14866 (pattern : Twelve) (guard : d2301 pattern = 1) : d1385 pattern ≤ (2 : Int) + d2452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1385, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14800 pattern childGuard
    simpa only [d1385, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1385, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14865 pattern childGuard
    simpa only [d1385, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14867 (pattern : Twelve) (guard : d26 pattern = 1) : d19 pattern ≤ (2 : Int) + d19 pattern := by
  omega
theorem c14868 (pattern : Twelve) (guard : d2301 pattern = 1) : d1381 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14867 pattern childGuard
    simpa only [d2301, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14036 pattern childGuard
    simpa only [d2301, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14869 (pattern : Twelve) (guard : d2301 pattern = 1) : d1386 pattern ≤ (2 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14868 pattern childGuard
    simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14870 (pattern : Twelve) (guard : d2301 pattern = 1) : d1393 pattern ≤ (2 : Int) + d2453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1393, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14866 pattern childGuard
    simpa only [d1393, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1393, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14869 pattern childGuard
    simpa only [d1393, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14871 (pattern : Twelve) (guard : d26 pattern = 1) : d1279 pattern ≤ (2 : Int) + d1275 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14862 pattern childGuard
    simpa only [d26, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13422 pattern childGuard
    simpa only [d26, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14872 (pattern : Twelve) (guard : d2301 pattern = 1) : d1382 pattern ≤ (2 : Int) + d2390 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1382, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14871 pattern childGuard
    simpa only [d2301, d1382, d2390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1382, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14030 pattern childGuard
    simpa only [d2301, d1382, d2390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14873 (pattern : Twelve) (guard : d2301 pattern = 1) : d1387 pattern ≤ (2 : Int) + d2452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1387, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14807 pattern childGuard
    simpa only [d1387, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1387, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14872 pattern childGuard
    simpa only [d1387, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14874 (pattern : Twelve) (guard : d2301 pattern = 1) : d942 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14388 pattern childGuard
    simpa only [d2301, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14036 pattern childGuard
    simpa only [d2301, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14875 (pattern : Twelve) (guard : d2301 pattern = 1) : d1388 pattern ≤ (2 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1388, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14874 pattern childGuard
    simpa only [d1388, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1388, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1388, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14876 (pattern : Twelve) (guard : d2301 pattern = 1) : d1394 pattern ≤ (2 : Int) + d2453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1394, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14873 pattern childGuard
    simpa only [d1394, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1394, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14875 pattern childGuard
    simpa only [d1394, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14877 (pattern : Twelve) (guard : d2301 pattern = 1) : d1398 pattern ≤ (2 : Int) + d2453 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14870 pattern childGuard
    simpa only [d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14876 pattern childGuard
    simpa only [d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14878 (pattern : Twelve) (guard : d2301 pattern = 1) : d1389 pattern ≤ (2 : Int) + d2452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1389, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14813 pattern childGuard
    simpa only [d1389, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1389, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14865 pattern childGuard
    simpa only [d1389, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14879 (pattern : Twelve) (guard : d2301 pattern = 1) : d1395 pattern ≤ (2 : Int) + d2453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1395, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14878 pattern childGuard
    simpa only [d1395, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1395, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14869 pattern childGuard
    simpa only [d1395, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14880 (pattern : Twelve) (guard : d2301 pattern = 1) : d1399 pattern ≤ (2 : Int) + d2453 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14879 pattern childGuard
    simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14876 pattern childGuard
    simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14881 (pattern : Twelve) (guard : d2301 pattern = 1) : d1403 pattern ≤ (2 : Int) + d2453 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14877 pattern childGuard
    simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14880 pattern childGuard
    simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14882 (pattern : Twelve) (guard : d0 pattern = 1) : d1276 pattern ≤ (2 : Int) + d1276 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14883 (pattern : Twelve) (guard : d26 pattern = 1) : d1282 pattern ≤ (2 : Int) + d1276 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14882 pattern childGuard
    simpa only [d26, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13424 pattern childGuard
    simpa only [d26, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14884 (pattern : Twelve) (guard : d2301 pattern = 1) : d1383 pattern ≤ (2 : Int) + d2392 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1383, d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14883 pattern childGuard
    simpa only [d2301, d1383, d2392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1383, d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14779 pattern childGuard
    simpa only [d2301, d1383, d2392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14885 (pattern : Twelve) (guard : d2301 pattern = 1) : d1390 pattern ≤ (2 : Int) + d2454 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1390, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14825 pattern childGuard
    simpa only [d1390, d2454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1390, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14884 pattern childGuard
    simpa only [d1390, d2454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14886 (pattern : Twelve) (guard : d2301 pattern = 1) : d945 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14405 pattern childGuard
    simpa only [d2301, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14074 pattern childGuard
    simpa only [d2301, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14887 (pattern : Twelve) (guard : d2301 pattern = 1) : d1391 pattern ≤ (2 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1391, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14886 pattern childGuard
    simpa only [d1391, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1391, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1391, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14888 (pattern : Twelve) (guard : d2301 pattern = 1) : d1396 pattern ≤ (2 : Int) + d2455 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1396, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14885 pattern childGuard
    simpa only [d1396, d2455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1396, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14887 pattern childGuard
    simpa only [d1396, d2455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14889 (pattern : Twelve) (guard : d2301 pattern = 1) : d1400 pattern ≤ (2 : Int) + d2456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1400, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14876 pattern childGuard
    simpa only [d1400, d2456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1400, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14888 pattern childGuard
    simpa only [d1400, d2456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14890 (pattern : Twelve) (guard : d2301 pattern = 1) : d1401 pattern ≤ (2 : Int) + d2457 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1401, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14876 pattern childGuard
    simpa only [d1401, d2457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1401, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1401, d2457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14891 (pattern : Twelve) (guard : d2301 pattern = 1) : d1404 pattern ≤ (2 : Int) + d2458 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1404, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14889 pattern childGuard
    simpa only [d1404, d2458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1404, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14890 pattern childGuard
    simpa only [d1404, d2458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14892 (pattern : Twelve) (guard : d2301 pattern = 1) : d1405 pattern ≤ (2 : Int) + d2459 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1405, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14881 pattern childGuard
    simpa only [d1405, d2459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1405, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14891 pattern childGuard
    simpa only [d1405, d2459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14893 (pattern : Twelve) (guard : d26 pattern = 1) : d1283 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14387 pattern childGuard
    simpa only [d26, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13333 pattern childGuard
    simpa only [d26, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14894 (pattern : Twelve) (guard : d2301 pattern = 1) : d1384 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14893 pattern childGuard
    simpa only [d2301, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14036 pattern childGuard
    simpa only [d2301, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14895 (pattern : Twelve) (guard : d2301 pattern = 1) : d1392 pattern ≤ (2 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1392, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14894 pattern childGuard
    simpa only [d1392, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1392, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1392, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14896 (pattern : Twelve) (guard : d2301 pattern = 1) : d1397 pattern ≤ (2 : Int) + d2453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1397, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14878 pattern childGuard
    simpa only [d1397, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1397, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14895 pattern childGuard
    simpa only [d1397, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14897 (pattern : Twelve) (guard : d2301 pattern = 1) : d1402 pattern ≤ (2 : Int) + d2453 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14896 pattern childGuard
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14876 pattern childGuard
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14898 (pattern : Twelve) (guard : d2301 pattern = 1) : d1406 pattern ≤ (2 : Int) + d2459 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1406, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14897 pattern childGuard
    simpa only [d1406, d2459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1406, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14891 pattern childGuard
    simpa only [d1406, d2459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14899 (pattern : Twelve) (guard : d2301 pattern = 1) : d1408 pattern ≤ (2 : Int) + d2459 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14892 pattern childGuard
    simpa only [d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14898 pattern childGuard
    simpa only [d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14900 (pattern : Twelve) (guard : d2301 pattern = 1) : d1407 pattern ≤ (2 : Int) + d2459 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1407, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14880 pattern childGuard
    simpa only [d1407, d2459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1407, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14891 pattern childGuard
    simpa only [d1407, d2459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14901 (pattern : Twelve) (guard : d2301 pattern = 1) : d1409 pattern ≤ (2 : Int) + d2459 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14900 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14898 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14902 (pattern : Twelve) (guard : d2301 pattern = 1) : d1410 pattern ≤ (2 : Int) + d2459 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14899 pattern childGuard
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14901 pattern childGuard
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14903 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1277 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14904 (pattern : Twelve) (guard : d2301 pattern = 1) : d1383 pattern ≤ (2 : Int) + d2398 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1383, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14883 pattern childGuard
    simpa only [d2301, d1383, d2398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1383, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14903 pattern childGuard
    simpa only [d2301, d1383, d2398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14905 (pattern : Twelve) (guard : d2301 pattern = 1) : d1390 pattern ≤ (2 : Int) + d2460 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1390, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14825 pattern childGuard
    simpa only [d1390, d2460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1390, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14904 pattern childGuard
    simpa only [d1390, d2460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14906 (pattern : Twelve) (guard : d2301 pattern = 1) : d945 pattern ≤ (2 : Int) + d2461 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d945, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14405 pattern childGuard
    simpa only [d2301, d945, d2461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d945, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14784 pattern childGuard
    simpa only [d2301, d945, d2461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14907 (pattern : Twelve) (guard : d2301 pattern = 1) : d1391 pattern ≤ (2 : Int) + d2462 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1391, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14906 pattern childGuard
    simpa only [d1391, d2462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1391, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1391, d2462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14908 (pattern : Twelve) (guard : d2301 pattern = 1) : d1396 pattern ≤ (2 : Int) + d2463 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1396, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14905 pattern childGuard
    simpa only [d1396, d2463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1396, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14907 pattern childGuard
    simpa only [d1396, d2463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14909 (pattern : Twelve) (guard : d2301 pattern = 1) : d1400 pattern ≤ (2 : Int) + d2464 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1400, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14876 pattern childGuard
    simpa only [d1400, d2464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1400, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14908 pattern childGuard
    simpa only [d1400, d2464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14910 (pattern : Twelve) (guard : d2301 pattern = 1) : d1404 pattern ≤ (2 : Int) + d2465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1404, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14909 pattern childGuard
    simpa only [d1404, d2465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1404, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14890 pattern childGuard
    simpa only [d1404, d2465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14911 (pattern : Twelve) (guard : d2301 pattern = 1) : d1407 pattern ≤ (2 : Int) + d2466 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1407, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14880 pattern childGuard
    simpa only [d1407, d2466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1407, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14910 pattern childGuard
    simpa only [d1407, d2466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14912 (pattern : Twelve) (guard : d2301 pattern = 1) : d1406 pattern ≤ (2 : Int) + d2466 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1406, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14897 pattern childGuard
    simpa only [d1406, d2466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1406, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14910 pattern childGuard
    simpa only [d1406, d2466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14913 (pattern : Twelve) (guard : d2301 pattern = 1) : d1409 pattern ≤ (2 : Int) + d2466 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14911 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14912 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14914 (pattern : Twelve) (guard : d2301 pattern = 1) : d1411 pattern ≤ (2 : Int) + d2467 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1411, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14902 pattern childGuard
    simpa only [d1411, d2467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1411, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14913 pattern childGuard
    simpa only [d1411, d2467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14915 (pattern : Twelve) (guard : d26 pattern = 1) : d1324 pattern ≤ (2 : Int) + d1324 pattern := by
  omega
theorem c14916 (pattern : Twelve) (guard : d2301 pattern = 1) : d1689 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14915 pattern childGuard
    simpa only [d2301, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14068 pattern childGuard
    simpa only [d2301, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14917 (pattern : Twelve) (guard : d2301 pattern = 1) : d1693 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14868 pattern childGuard
    simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14916 pattern childGuard
    simpa only [d1693, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14918 (pattern : Twelve) (guard : d26 pattern = 1) : d25 pattern ≤ (2 : Int) + d25 pattern := by
  omega
theorem c14919 (pattern : Twelve) (guard : d2301 pattern = 1) : d1690 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14918 pattern childGuard
    simpa only [d2301, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14074 pattern childGuard
    simpa only [d2301, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14920 (pattern : Twelve) (guard : d2301 pattern = 1) : d1694 pattern ≤ (2 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14919 pattern childGuard
    simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14921 (pattern : Twelve) (guard : d2301 pattern = 1) : d1697 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14917 pattern childGuard
    simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14920 pattern childGuard
    simpa only [d1697, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14922 (pattern : Twelve) (guard : d2301 pattern = 1) : d1691 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14451 pattern childGuard
    simpa only [d2301, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14068 pattern childGuard
    simpa only [d2301, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14923 (pattern : Twelve) (guard : d2301 pattern = 1) : d1695 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1695, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14874 pattern childGuard
    simpa only [d1695, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1695, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14922 pattern childGuard
    simpa only [d1695, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14924 (pattern : Twelve) (guard : d2301 pattern = 1) : d1698 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1698, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14923 pattern childGuard
    simpa only [d1698, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1698, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14887 pattern childGuard
    simpa only [d1698, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14925 (pattern : Twelve) (guard : d2301 pattern = 1) : d1700 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14921 pattern childGuard
    simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14924 pattern childGuard
    simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14926 (pattern : Twelve) (guard : d2301 pattern = 1) : d1692 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14465 pattern childGuard
    simpa only [d2301, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14784 pattern childGuard
    simpa only [d2301, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14927 (pattern : Twelve) (guard : d2301 pattern = 1) : d1696 pattern ≤ (2 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1696, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14886 pattern childGuard
    simpa only [d1696, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1696, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14926 pattern childGuard
    simpa only [d1696, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14928 (pattern : Twelve) (guard : d2301 pattern = 1) : d1252 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14469 pattern childGuard
    simpa only [d2301, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14826 pattern childGuard
    simpa only [d2301, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14929 (pattern : Twelve) (guard : d2301 pattern = 1) : d1626 pattern ≤ (2 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1626, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14928 pattern childGuard
    simpa only [d1626, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1626, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1626, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14930 (pattern : Twelve) (guard : d2301 pattern = 1) : d1699 pattern ≤ (2 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1699, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14927 pattern childGuard
    simpa only [d1699, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1699, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14929 pattern childGuard
    simpa only [d1699, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14931 (pattern : Twelve) (guard : d2301 pattern = 1) : d1701 pattern ≤ (2 : Int) + d1992 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1701, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14924 pattern childGuard
    simpa only [d1701, d1992, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1701, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14930 pattern childGuard
    simpa only [d1701, d1992, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14932 (pattern : Twelve) (guard : d2301 pattern = 1) : d1702 pattern ≤ (2 : Int) + d1715 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1702, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14924 pattern childGuard
    simpa only [d1702, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1702, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1702, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14933 (pattern : Twelve) (guard : d2301 pattern = 1) : d1703 pattern ≤ (2 : Int) + d2346 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1703, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14931 pattern childGuard
    simpa only [d1703, d2346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1703, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14932 pattern childGuard
    simpa only [d1703, d2346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14934 (pattern : Twelve) (guard : d2301 pattern = 1) : d1704 pattern ≤ (2 : Int) + d2347 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1704, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14925 pattern childGuard
    simpa only [d1704, d2347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1704, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14933 pattern childGuard
    simpa only [d1704, d2347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14935 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14936 (pattern : Twelve) (guard : d2301 pattern = 1) : d1692 pattern ≤ (2 : Int) + d2410 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1692, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14465 pattern childGuard
    simpa only [d2301, d1692, d2410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1692, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14935 pattern childGuard
    simpa only [d2301, d1692, d2410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14937 (pattern : Twelve) (guard : d2301 pattern = 1) : d1696 pattern ≤ (2 : Int) + d2468 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1696, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14886 pattern childGuard
    simpa only [d1696, d2468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1696, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14936 pattern childGuard
    simpa only [d1696, d2468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14938 (pattern : Twelve) (guard : d2301 pattern = 1) : d1252 pattern ≤ (2 : Int) + d2469 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d1252, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14469 pattern childGuard
    simpa only [d2301, d1252, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d1252, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13925 pattern childGuard
    simpa only [d2301, d1252, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14939 (pattern : Twelve) (guard : d2301 pattern = 1) : d1626 pattern ≤ (2 : Int) + d2470 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1626, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14938 pattern childGuard
    simpa only [d1626, d2470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1626, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d1626, d2470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14940 (pattern : Twelve) (guard : d2301 pattern = 1) : d1699 pattern ≤ (2 : Int) + d2471 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1699, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14937 pattern childGuard
    simpa only [d1699, d2471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1699, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14939 pattern childGuard
    simpa only [d1699, d2471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14941 (pattern : Twelve) (guard : d2301 pattern = 1) : d1701 pattern ≤ (2 : Int) + d2472 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1701, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14924 pattern childGuard
    simpa only [d1701, d2472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1701, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14940 pattern childGuard
    simpa only [d1701, d2472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14942 (pattern : Twelve) (guard : d2301 pattern = 1) : d1703 pattern ≤ (2 : Int) + d2473 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1703, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14941 pattern childGuard
    simpa only [d1703, d2473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1703, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14932 pattern childGuard
    simpa only [d1703, d2473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14943 (pattern : Twelve) (guard : d2301 pattern = 1) : d1704 pattern ≤ (2 : Int) + d2474 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1704, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14925 pattern childGuard
    simpa only [d1704, d2474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d1704, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14942 pattern childGuard
    simpa only [d1704, d2474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14944 (pattern : Twelve) (guard : d2301 pattern = 1) : d1704 pattern ≤ (2 : Int) + d2475 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14934 pattern childGuard
    simpa only [d2475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14943 pattern childGuard
    simpa only [d2475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14945 (pattern : Twelve) (guard : d26 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c14946 (pattern : Twelve) (guard : d0 pattern = 1) : d185 pattern ≤ (0 : Int) + d2357 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14947 (pattern : Twelve) (guard : d2355 pattern = 1) : d425 pattern ≤ (0 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d425, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14945 pattern childGuard
    simpa only [d2355, d425, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d425, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14946 pattern childGuard
    simpa only [d2355, d425, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14948 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (0 : Int) + d2358 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14949 (pattern : Twelve) (guard : d2355 pattern = 1) : d426 pattern ≤ (0 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d426, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14945 pattern childGuard
    simpa only [d2355, d426, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d426, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14948 pattern childGuard
    simpa only [d2355, d426, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14950 (pattern : Twelve) (guard : d2355 pattern = 1) : d444 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d444, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14947 pattern childGuard
    simpa only [d444, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d444, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14949 pattern childGuard
    simpa only [d444, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14951 (pattern : Twelve) (guard : d0 pattern = 1) : d445 pattern ≤ (0 : Int) + d2418 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14952 (pattern : Twelve) (guard : d2356 pattern = 1) : d455 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14950 pattern childGuard
    simpa only [d2356, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14951 pattern childGuard
    simpa only [d2356, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14953 (pattern : Twelve) (guard : d0 pattern = 1) : d188 pattern ≤ (0 : Int) + d2357 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14954 (pattern : Twelve) (guard : d2355 pattern = 1) : d429 pattern ≤ (0 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d429, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14945 pattern childGuard
    simpa only [d2355, d429, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d429, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14953 pattern childGuard
    simpa only [d2355, d429, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14955 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d2358 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14956 (pattern : Twelve) (guard : d2355 pattern = 1) : d430 pattern ≤ (0 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d430, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14945 pattern childGuard
    simpa only [d2355, d430, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d430, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14955 pattern childGuard
    simpa only [d2355, d430, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14957 (pattern : Twelve) (guard : d2355 pattern = 1) : d446 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d446, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14954 pattern childGuard
    simpa only [d446, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d446, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14956 pattern childGuard
    simpa only [d446, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14958 (pattern : Twelve) (guard : d0 pattern = 1) : d447 pattern ≤ (0 : Int) + d2418 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14959 (pattern : Twelve) (guard : d2356 pattern = 1) : d456 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14957 pattern childGuard
    simpa only [d2356, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14958 pattern childGuard
    simpa only [d2356, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14960 (pattern : Twelve) (guard : d2356 pattern = 1) : d465 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14952 pattern childGuard
    simpa only [d465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14959 pattern childGuard
    simpa only [d465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14961 (pattern : Twelve) (guard : d26 pattern = 1) : d30 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2858 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14962 (pattern : Twelve) (guard : d0 pattern = 1) : d193 pattern ≤ (0 : Int) + d2360 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14963 (pattern : Twelve) (guard : d2355 pattern = 1) : d433 pattern ≤ (0 : Int) + d2419 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d433, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14961 pattern childGuard
    simpa only [d2355, d433, d2419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d433, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14962 pattern childGuard
    simpa only [d2355, d433, d2419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14964 (pattern : Twelve) (guard : d0 pattern = 1) : d194 pattern ≤ (0 : Int) + d2361 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14965 (pattern : Twelve) (guard : d2355 pattern = 1) : d434 pattern ≤ (0 : Int) + d2420 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d434, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14961 pattern childGuard
    simpa only [d2355, d434, d2420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d434, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14964 pattern childGuard
    simpa only [d2355, d434, d2420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14966 (pattern : Twelve) (guard : d2355 pattern = 1) : d448 pattern ≤ (0 : Int) + d2421 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d448, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14963 pattern childGuard
    simpa only [d448, d2421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d448, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14965 pattern childGuard
    simpa only [d448, d2421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14967 (pattern : Twelve) (guard : d0 pattern = 1) : d449 pattern ≤ (0 : Int) + d2421 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14968 (pattern : Twelve) (guard : d2356 pattern = 1) : d457 pattern ≤ (0 : Int) + d2421 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14966 pattern childGuard
    simpa only [d2356, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14967 pattern childGuard
    simpa only [d2356, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14969 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d6 pattern := by
  change (2 : Int) ≤ (0 : Int) + 6
  decide
theorem c14970 (pattern : Twelve) (guard : d26 pattern = 1) : d30 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14971 (pattern : Twelve) (guard : d26 pattern = 1) : d35 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d26, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d26, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14972 (pattern : Twelve) (guard : d26 pattern = 1) : d56 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14970 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14971 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14973 (pattern : Twelve) (guard : d0 pattern = 1) : d196 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14974 (pattern : Twelve) (guard : d2355 pattern = 1) : d437 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14972 pattern childGuard
    simpa only [d2355, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14973 pattern childGuard
    simpa only [d2355, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14975 (pattern : Twelve) (guard : d2355 pattern = 1) : d432 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14972 pattern childGuard
    simpa only [d2355, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2355, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14976 (pattern : Twelve) (guard : d2355 pattern = 1) : d450 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14974 pattern childGuard
    simpa only [d450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14975 pattern childGuard
    simpa only [d450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14977 (pattern : Twelve) (guard : d2356 pattern = 1) : d458 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14976 pattern childGuard
    simpa only [d2356, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2356, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14978 (pattern : Twelve) (guard : d2356 pattern = 1) : d466 pattern ≤ (0 : Int) + d2476 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d466, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14968 pattern childGuard
    simpa only [d466, d2476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d466, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14977 pattern childGuard
    simpa only [d466, d2476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14979 (pattern : Twelve) (guard : d2356 pattern = 1) : d471 pattern ≤ (0 : Int) + d2477 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d471, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14960 pattern childGuard
    simpa only [d471, d2477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d471, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14978 pattern childGuard
    simpa only [d471, d2477, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
