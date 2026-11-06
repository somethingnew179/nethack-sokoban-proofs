/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons099
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c14000 (pattern : Twelve) (guard : d1848 pattern = 1) : d841 pattern ≤ (2 : Int) + d2291 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13992 pattern childGuard
    simpa only [d841, d2291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13999 pattern childGuard
    simpa only [d841, d2291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14001 (pattern : Twelve) (guard : d1848 pattern = 1) : d854 pattern ≤ (2 : Int) + d2292 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13987 pattern childGuard
    simpa only [d854, d2292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14000 pattern childGuard
    simpa only [d854, d2292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14002 (pattern : Twelve) (guard : d2279 pattern = 1) : d861 pattern ≤ (2 : Int) + d2292 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13981 pattern childGuard
    simpa only [d2279, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14001 pattern childGuard
    simpa only [d2279, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14003 (pattern : Twelve) (guard : d0 pattern = 1) : d922 pattern ≤ (2 : Int) + d2292 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14004 (pattern : Twelve) (guard : d2280 pattern = 1) : d1011 pattern ≤ (2 : Int) + d2292 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14002 pattern childGuard
    simpa only [d2280, d1011, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14003 pattern childGuard
    simpa only [d2280, d1011, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14005 (pattern : Twelve) (guard : d0 pattern = 1) : d857 pattern ≤ (2 : Int) + d2294 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14006 (pattern : Twelve) (guard : d1848 pattern = 1) : d832 pattern ≤ (2 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13983 pattern childGuard
    simpa only [d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13963 pattern childGuard
    simpa only [d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14007 (pattern : Twelve) (guard : d1848 pattern = 1) : d847 pattern ≤ (2 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d847, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13934 pattern childGuard
    simpa only [d847, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d847, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14006 pattern childGuard
    simpa only [d847, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14008 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d2 pattern := by
  change (1 : Int) ≤ (2 : Int) + 2
  decide
theorem c14009 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14008 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14010 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14009 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14011 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14012 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14010 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14011 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14013 (pattern : Twelve) (guard : d1848 pattern = 1) : d833 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14012 pattern childGuard
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13967 pattern childGuard
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14014 (pattern : Twelve) (guard : d1848 pattern = 1) : d848 pattern ≤ (2 : Int) + d2293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d848, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14013 pattern childGuard
    simpa only [d848, d2293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d848, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13999 pattern childGuard
    simpa only [d848, d2293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14015 (pattern : Twelve) (guard : d1848 pattern = 1) : d858 pattern ≤ (2 : Int) + d2294 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d858, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14007 pattern childGuard
    simpa only [d858, d2294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d858, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14014 pattern childGuard
    simpa only [d858, d2294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14016 (pattern : Twelve) (guard : d2279 pattern = 1) : d864 pattern ≤ (2 : Int) + d2294 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14005 pattern childGuard
    simpa only [d2279, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14015 pattern childGuard
    simpa only [d2279, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14017 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2294 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14018 (pattern : Twelve) (guard : d2280 pattern = 1) : d1012 pattern ≤ (2 : Int) + d2294 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14016 pattern childGuard
    simpa only [d2280, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14017 pattern childGuard
    simpa only [d2280, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14019 (pattern : Twelve) (guard : d2280 pattern = 1) : d1014 pattern ≤ (2 : Int) + d2295 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1014, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14004 pattern childGuard
    simpa only [d1014, d2295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1014, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14018 pattern childGuard
    simpa only [d1014, d2295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14020 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2292 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14021 (pattern : Twelve) (guard : d2280 pattern = 1) : d1013 pattern ≤ (2 : Int) + d2292 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14002 pattern childGuard
    simpa only [d2280, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14020 pattern childGuard
    simpa only [d2280, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14022 (pattern : Twelve) (guard : d2280 pattern = 1) : d1015 pattern ≤ (2 : Int) + d2295 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1015, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14021 pattern childGuard
    simpa only [d1015, d2295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1015, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14018 pattern childGuard
    simpa only [d1015, d2295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14023 (pattern : Twelve) (guard : d2280 pattern = 1) : d1016 pattern ≤ (2 : Int) + d2295 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14019 pattern childGuard
    simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14022 pattern childGuard
    simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14024 (pattern : Twelve) (guard : d2280 pattern = 1) : d1017 pattern ≤ (2 : Int) + d2295 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14023 pattern childGuard
    simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14022 pattern childGuard
    simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14025 (pattern : Twelve) (guard : d0 pattern = 1) : d1305 pattern ≤ (2 : Int) + d1977 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14026 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d8 pattern := by
  omega
theorem c14027 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13904 pattern childGuard
    simpa only [d1275, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14026 pattern childGuard
    simpa only [d1275, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14028 (pattern : Twelve) (guard : d0 pattern = 1) : d1276 pattern ≤ (2 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14029 (pattern : Twelve) (guard : d1848 pattern = 1) : d1279 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14027 pattern childGuard
    simpa only [d1848, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14028 pattern childGuard
    simpa only [d1848, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14030 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14031 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13413 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14030 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14032 (pattern : Twelve) (guard : d1848 pattern = 1) : d1285 pattern ≤ (2 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14029 pattern childGuard
    simpa only [d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14031 pattern childGuard
    simpa only [d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14033 (pattern : Twelve) (guard : d1848 pattern = 1) : d1295 pattern ≤ (2 : Int) + d1976 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1295, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13992 pattern childGuard
    simpa only [d1295, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1295, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14032 pattern childGuard
    simpa only [d1295, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14034 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (2 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14035 (pattern : Twelve) (guard : d1848 pattern = 1) : d817 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14034 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14036 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14037 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13418 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14036 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14038 (pattern : Twelve) (guard : d1848 pattern = 1) : d1286 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14035 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14037 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14039 (pattern : Twelve) (guard : d1848 pattern = 1) : d6 pattern ≤ (2 : Int) + d6 pattern := by
  omega
theorem c14040 (pattern : Twelve) (guard : d1848 pattern = 1) : d1296 pattern ≤ (2 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14038 pattern childGuard
    simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14039 pattern childGuard
    simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14041 (pattern : Twelve) (guard : d1848 pattern = 1) : d1306 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14033 pattern childGuard
    simpa only [d1306, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14040 pattern childGuard
    simpa only [d1306, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14042 (pattern : Twelve) (guard : d2279 pattern = 1) : d1313 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14025 pattern childGuard
    simpa only [d2279, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14041 pattern childGuard
    simpa only [d2279, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14043 (pattern : Twelve) (guard : d0 pattern = 1) : d1363 pattern ≤ (2 : Int) + d1977 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14044 (pattern : Twelve) (guard : d2280 pattern = 1) : d1428 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14042 pattern childGuard
    simpa only [d2280, d1428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14043 pattern childGuard
    simpa only [d2280, d1428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14045 (pattern : Twelve) (guard : d0 pattern = 1) : d1309 pattern ≤ (2 : Int) + d1988 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14046 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14047 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14008 pattern childGuard
    simpa only [d11, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13331 pattern childGuard
    simpa only [d11, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14048 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14046 pattern childGuard
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14047 pattern childGuard
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14049 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (2 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14050 (pattern : Twelve) (guard : d1848 pattern = 1) : d817 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14048 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14049 pattern childGuard
    simpa only [d1848, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14051 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14052 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13590 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14051 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14053 (pattern : Twelve) (guard : d1848 pattern = 1) : d1290 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14050 pattern childGuard
    simpa only [d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14052 pattern childGuard
    simpa only [d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14054 (pattern : Twelve) (guard : d1848 pattern = 1) : d1302 pattern ≤ (2 : Int) + d1987 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1302, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14053 pattern childGuard
    simpa only [d1302, d1987, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1302, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14039 pattern childGuard
    simpa only [d1302, d1987, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14055 (pattern : Twelve) (guard : d1848 pattern = 1) : d1310 pattern ≤ (2 : Int) + d1988 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1310, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14033 pattern childGuard
    simpa only [d1310, d1988, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1310, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14054 pattern childGuard
    simpa only [d1310, d1988, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14056 (pattern : Twelve) (guard : d2279 pattern = 1) : d1316 pattern ≤ (2 : Int) + d1988 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14045 pattern childGuard
    simpa only [d2279, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14055 pattern childGuard
    simpa only [d2279, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14057 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1988 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14058 (pattern : Twelve) (guard : d2280 pattern = 1) : d1429 pattern ≤ (2 : Int) + d1988 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14056 pattern childGuard
    simpa only [d2280, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14057 pattern childGuard
    simpa only [d2280, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14059 (pattern : Twelve) (guard : d2280 pattern = 1) : d1431 pattern ≤ (2 : Int) + d2296 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1431, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14044 pattern childGuard
    simpa only [d1431, d2296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1431, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14058 pattern childGuard
    simpa only [d1431, d2296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14060 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1977 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14061 (pattern : Twelve) (guard : d2280 pattern = 1) : d1430 pattern ≤ (2 : Int) + d1977 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14042 pattern childGuard
    simpa only [d2280, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14060 pattern childGuard
    simpa only [d2280, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14062 (pattern : Twelve) (guard : d2280 pattern = 1) : d1432 pattern ≤ (2 : Int) + d2296 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1432, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14061 pattern childGuard
    simpa only [d1432, d2296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1432, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14058 pattern childGuard
    simpa only [d1432, d2296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14063 (pattern : Twelve) (guard : d2280 pattern = 1) : d1433 pattern ≤ (2 : Int) + d2296 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14059 pattern childGuard
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14062 pattern childGuard
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14064 (pattern : Twelve) (guard : d2280 pattern = 1) : d1434 pattern ≤ (2 : Int) + d2296 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14063 pattern childGuard
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14062 pattern childGuard
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14065 (pattern : Twelve) (guard : d0 pattern = 1) : d1656 pattern ≤ (2 : Int) + d1656 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14066 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (2 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14067 (pattern : Twelve) (guard : d1848 pattern = 1) : d1644 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13454 pattern childGuard
    simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14066 pattern childGuard
    simpa only [d1848, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14068 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14069 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13454 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14068 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14070 (pattern : Twelve) (guard : d1848 pattern = 1) : d1647 pattern ≤ (2 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14067 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14069 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14071 (pattern : Twelve) (guard : d1848 pattern = 1) : d1651 pattern ≤ (2 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14038 pattern childGuard
    simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14070 pattern childGuard
    simpa only [d1651, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14072 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (2 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14073 (pattern : Twelve) (guard : d1848 pattern = 1) : d821 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13458 pattern childGuard
    simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14072 pattern childGuard
    simpa only [d1848, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14074 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14075 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13458 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14074 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14076 (pattern : Twelve) (guard : d1848 pattern = 1) : d1289 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14073 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14075 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14077 (pattern : Twelve) (guard : d1848 pattern = 1) : d1300 pattern ≤ (2 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14076 pattern childGuard
    simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14039 pattern childGuard
    simpa only [d1300, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14078 (pattern : Twelve) (guard : d1848 pattern = 1) : d1657 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14071 pattern childGuard
    simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14077 pattern childGuard
    simpa only [d1657, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14079 (pattern : Twelve) (guard : d2279 pattern = 1) : d1660 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14065 pattern childGuard
    simpa only [d2279, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14078 pattern childGuard
    simpa only [d2279, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14080 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d1656 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14081 (pattern : Twelve) (guard : d2280 pattern = 1) : d1714 pattern ≤ (2 : Int) + d1656 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14079 pattern childGuard
    simpa only [d2280, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14080 pattern childGuard
    simpa only [d2280, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14082 (pattern : Twelve) (guard : d0 pattern = 1) : d402 pattern ≤ (0 : Int) + d91 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14083 (pattern : Twelve) (guard : d1848 pattern = 1) : d392 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5265 pattern childGuard
    simpa only [d392, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5519 pattern childGuard
    simpa only [d392, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14084 (pattern : Twelve) (guard : d1848 pattern = 1) : d403 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5492 pattern childGuard
    simpa only [d403, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14083 pattern childGuard
    simpa only [d403, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14085 (pattern : Twelve) (guard : d2279 pattern = 1) : d409 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14082 pattern childGuard
    simpa only [d2279, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14084 pattern childGuard
    simpa only [d2279, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14086 (pattern : Twelve) (guard : d0 pattern = 1) : d403 pattern ≤ (0 : Int) + d93 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14087 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14088 (pattern : Twelve) (guard : d1848 pattern = 1) : d33 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14087 pattern childGuard
    simpa only [d1848, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14089 (pattern : Twelve) (guard : d1848 pattern = 1) : d379 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14088 pattern childGuard
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14090 (pattern : Twelve) (guard : d1848 pattern = 1) : d393 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d393, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14089 pattern childGuard
    simpa only [d393, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d393, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5517 pattern childGuard
    simpa only [d393, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14091 (pattern : Twelve) (guard : d1848 pattern = 1) : d404 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d404, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14090 pattern childGuard
    simpa only [d404, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d404, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5527 pattern childGuard
    simpa only [d404, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14092 (pattern : Twelve) (guard : d2279 pattern = 1) : d410 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14086 pattern childGuard
    simpa only [d2279, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14091 pattern childGuard
    simpa only [d2279, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14093 (pattern : Twelve) (guard : d2279 pattern = 1) : d415 pattern ≤ (0 : Int) + d2297 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d415, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14085 pattern childGuard
    simpa only [d415, d2297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2279 pattern = 1 := by simpa only [d415, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14092 pattern childGuard
    simpa only [d415, d2297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14094 (pattern : Twelve) (guard : d0 pattern = 1) : d416 pattern ≤ (0 : Int) + d2297 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14095 (pattern : Twelve) (guard : d2280 pattern = 1) : d419 pattern ≤ (0 : Int) + d2297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14093 pattern childGuard
    simpa only [d2280, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14094 pattern childGuard
    simpa only [d2280, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14096 (pattern : Twelve) (guard : d0 pattern = 1) : d407 pattern ≤ (0 : Int) + d97 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14097 (pattern : Twelve) (guard : d2279 pattern = 1) : d407 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14096 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5758 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14098 (pattern : Twelve) (guard : d0 pattern = 1) : d417 pattern ≤ (0 : Int) + d97 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14099 (pattern : Twelve) (guard : d2280 pattern = 1) : d420 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14097 pattern childGuard
    simpa only [d2280, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14098 pattern childGuard
    simpa only [d2280, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14100 (pattern : Twelve) (guard : d2280 pattern = 1) : d422 pattern ≤ (0 : Int) + d2298 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d422, d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14095 pattern childGuard
    simpa only [d422, d2298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d422, d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14099 pattern childGuard
    simpa only [d422, d2298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14101 (pattern : Twelve) (guard : d0 pattern = 1) : d407 pattern ≤ (0 : Int) + d91 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14102 (pattern : Twelve) (guard : d2279 pattern = 1) : d407 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14101 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5521 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14103 (pattern : Twelve) (guard : d0 pattern = 1) : d407 pattern ≤ (0 : Int) + d93 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14104 (pattern : Twelve) (guard : d2279 pattern = 1) : d407 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14103 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5528 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14105 (pattern : Twelve) (guard : d2279 pattern = 1) : d407 pattern ≤ (0 : Int) + d2297 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14102 pattern childGuard
    simpa only [d2297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14104 pattern childGuard
    simpa only [d2297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14106 (pattern : Twelve) (guard : d0 pattern = 1) : d417 pattern ≤ (0 : Int) + d2297 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14107 (pattern : Twelve) (guard : d2280 pattern = 1) : d420 pattern ≤ (0 : Int) + d2297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14105 pattern childGuard
    simpa only [d2280, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14106 pattern childGuard
    simpa only [d2280, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14108 (pattern : Twelve) (guard : d2280 pattern = 1) : d420 pattern ≤ (0 : Int) + d2298 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14107 pattern childGuard
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14099 pattern childGuard
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14109 (pattern : Twelve) (guard : d2280 pattern = 1) : d423 pattern ≤ (0 : Int) + d2298 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14100 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14108 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14110 (pattern : Twelve) (guard : d0 pattern = 1) : d418 pattern ≤ (0 : Int) + d2297 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14111 (pattern : Twelve) (guard : d2280 pattern = 1) : d421 pattern ≤ (0 : Int) + d2297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14105 pattern childGuard
    simpa only [d2280, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14110 pattern childGuard
    simpa only [d2280, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14112 (pattern : Twelve) (guard : d0 pattern = 1) : d418 pattern ≤ (0 : Int) + d97 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14113 (pattern : Twelve) (guard : d2280 pattern = 1) : d421 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14097 pattern childGuard
    simpa only [d2280, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14112 pattern childGuard
    simpa only [d2280, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14114 (pattern : Twelve) (guard : d2280 pattern = 1) : d421 pattern ≤ (0 : Int) + d2298 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14111 pattern childGuard
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14113 pattern childGuard
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14115 (pattern : Twelve) (guard : d2280 pattern = 1) : d424 pattern ≤ (0 : Int) + d2298 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14109 pattern childGuard
    simpa only [d424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14114 pattern childGuard
    simpa only [d424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14116 (pattern : Twelve) (guard : d0 pattern = 1) : d1048 pattern ≤ (0 : Int) + d853 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14117 (pattern : Twelve) (guard : d2279 pattern = 1) : d1054 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14116 pattern childGuard
    simpa only [d2279, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5586 pattern childGuard
    simpa only [d2279, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14118 (pattern : Twelve) (guard : d0 pattern = 1) : d1049 pattern ≤ (0 : Int) + d853 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14119 (pattern : Twelve) (guard : d2279 pattern = 1) : d1055 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14118 pattern childGuard
    simpa only [d2279, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5607 pattern childGuard
    simpa only [d2279, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14120 (pattern : Twelve) (guard : d2279 pattern = 1) : d1060 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14117 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2279 pattern = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14119 pattern childGuard
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14121 (pattern : Twelve) (guard : d0 pattern = 1) : d1061 pattern ≤ (0 : Int) + d853 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14122 (pattern : Twelve) (guard : d2280 pattern = 1) : d1064 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14120 pattern childGuard
    simpa only [d2280, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14121 pattern childGuard
    simpa only [d2280, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14123 (pattern : Twelve) (guard : d0 pattern = 1) : d1050 pattern ≤ (0 : Int) + d857 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14124 (pattern : Twelve) (guard : d2279 pattern = 1) : d1050 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14123 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5797 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14125 (pattern : Twelve) (guard : d0 pattern = 1) : d1062 pattern ≤ (0 : Int) + d857 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14126 (pattern : Twelve) (guard : d2280 pattern = 1) : d1065 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14124 pattern childGuard
    simpa only [d2280, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14125 pattern childGuard
    simpa only [d2280, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14127 (pattern : Twelve) (guard : d2280 pattern = 1) : d1067 pattern ≤ (0 : Int) + d2299 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1067, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14122 pattern childGuard
    simpa only [d1067, d2299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1067, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14126 pattern childGuard
    simpa only [d1067, d2299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14128 (pattern : Twelve) (guard : d0 pattern = 1) : d1050 pattern ≤ (0 : Int) + d853 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14129 (pattern : Twelve) (guard : d2279 pattern = 1) : d1050 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14128 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5607 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14130 (pattern : Twelve) (guard : d0 pattern = 1) : d1062 pattern ≤ (0 : Int) + d853 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14131 (pattern : Twelve) (guard : d2280 pattern = 1) : d1065 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14129 pattern childGuard
    simpa only [d2280, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14130 pattern childGuard
    simpa only [d2280, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14132 (pattern : Twelve) (guard : d2280 pattern = 1) : d1065 pattern ≤ (0 : Int) + d2299 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14131 pattern childGuard
    simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14126 pattern childGuard
    simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14133 (pattern : Twelve) (guard : d2280 pattern = 1) : d1068 pattern ≤ (0 : Int) + d2299 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14127 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14132 pattern childGuard
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14134 (pattern : Twelve) (guard : d0 pattern = 1) : d1063 pattern ≤ (0 : Int) + d853 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14135 (pattern : Twelve) (guard : d2280 pattern = 1) : d1066 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14129 pattern childGuard
    simpa only [d2280, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14134 pattern childGuard
    simpa only [d2280, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14136 (pattern : Twelve) (guard : d0 pattern = 1) : d1063 pattern ≤ (0 : Int) + d857 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14137 (pattern : Twelve) (guard : d2280 pattern = 1) : d1066 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14124 pattern childGuard
    simpa only [d2280, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14136 pattern childGuard
    simpa only [d2280, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14138 (pattern : Twelve) (guard : d2280 pattern = 1) : d1066 pattern ≤ (0 : Int) + d2299 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14135 pattern childGuard
    simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14137 pattern childGuard
    simpa only [d2299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14139 (pattern : Twelve) (guard : d2280 pattern = 1) : d1069 pattern ≤ (0 : Int) + d2299 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14133 pattern childGuard
    simpa only [d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14138 pattern childGuard
    simpa only [d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
