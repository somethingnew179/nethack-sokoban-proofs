/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons309
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43400 (p : Pattern) (guard : d8099 p = 1) : d2680 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2680, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42946 p hg
    simpa only [d8099, d2680, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2680, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21833 p hg
    simpa only [d8099, d2680, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43401 (p : Pattern) (guard : d8100 p = 1) : d2723 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2723, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43399 p hg
    simpa only [d8100, d2723, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2723, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43400 p hg
    simpa only [d8100, d2723, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43402 (p : Pattern) (guard : d8099 p = 1) : d2683 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2683, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42964 p hg
    simpa only [d8099, d2683, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2683, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21836 p hg
    simpa only [d8099, d2683, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43403 (p : Pattern) (guard : d8105 p = 1) : d2684 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2684, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43402 p hg
    simpa only [d8105, d2684, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2684, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2684, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43404 (p : Pattern) (guard : d8106 p = 1) : d2724 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2724, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43401 p hg
    simpa only [d8106, d2724, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2724, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43403 p hg
    simpa only [d8106, d2724, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43405 (p : Pattern) (guard : d5854 p = 1) : d2702 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2702, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35752 p hg
    simpa only [d5854, d2702, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2702, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2702, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43406 (p : Pattern) (guard : d8099 p = 1) : d2702 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43405 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21884 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43407 (p : Pattern) (guard : d8105 p = 1) : d2725 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2725, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43406 p hg
    simpa only [d8105, d2725, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2725, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22741 p hg
    simpa only [d8105, d2725, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43408 (p : Pattern) (guard : d8111 p = 1) : d2729 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2729, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43407 p hg
    simpa only [d8111, d2729, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2729, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42911 p hg
    simpa only [d8111, d2729, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43409 (p : Pattern) (guard : d8112 p = 1) : d2730 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2730, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43404 p hg
    simpa only [d8112, d2730, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2730, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43408 p hg
    simpa only [d8112, d2730, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43410 (p : Pattern) (guard : d5854 p = 1) : d2689 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2689, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35759 p hg
    simpa only [d5854, d2689, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2689, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2689, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43411 (p : Pattern) (guard : d8099 p = 1) : d2689 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43410 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21849 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43412 (p : Pattern) (guard : d8105 p = 1) : d2692 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2692, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43411 p hg
    simpa only [d8105, d2692, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2692, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22716 p hg
    simpa only [d8105, d2692, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43413 (p : Pattern) (guard : d8111 p = 1) : d2696 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2696, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43412 p hg
    simpa only [d8111, d2696, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2696, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42882 p hg
    simpa only [d8111, d2696, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43414 (p : Pattern) (guard : d8117 p = 1) : d2834 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2834, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43413 p hg
    simpa only [d8117, d2834, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2834, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d2834, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43415 (p : Pattern) (guard : d8118 p = 1) : d2835 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2835, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43409 p hg
    simpa only [d8118, d2835, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2835, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43414 p hg
    simpa only [d8118, d2835, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43416 (p : Pattern) (guard : d8117 p = 1) : d2834 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2834, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43378 p hg
    simpa only [d8117, d2834, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2834, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d2834, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43417 (p : Pattern) (guard : d8123 p = 1) : d2836 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2836, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43416 p hg
    simpa only [d8123, d2836, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2836, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2836, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43418 (p : Pattern) (guard : d8124 p = 1) : d2837 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2837, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43415 p hg
    simpa only [d8124, d2837, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2837, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43417 p hg
    simpa only [d8124, d2837, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43419 (p : Pattern) (guard : d5854 p = 1) : d2677 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35772 p hg
    simpa only [d5854, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43420 (p : Pattern) (guard : d8099 p = 1) : d2677 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43419 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21845 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43421 (p : Pattern) (guard : d8105 p = 1) : d2686 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2686, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43420 p hg
    simpa only [d8105, d2686, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2686, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22712 p hg
    simpa only [d8105, d2686, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43422 (p : Pattern) (guard : d8111 p = 1) : d2711 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2711, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43421 p hg
    simpa only [d8111, d2711, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2711, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42811 p hg
    simpa only [d8111, d2711, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43423 (p : Pattern) (guard : d8117 p = 1) : d2737 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2737, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43422 p hg
    simpa only [d8117, d2737, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2737, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42923 p hg
    simpa only [d8117, d2737, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43424 (p : Pattern) (guard : d0 p = 1) : d2838 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43425 (p : Pattern) (guard : d8123 p = 1) : d2839 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2839, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43423 p hg
    simpa only [d8123, d2839, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2839, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43424 p hg
    simpa only [d8123, d2839, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43426 (p : Pattern) (guard : d0 p = 1) : d2840 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43427 (p : Pattern) (guard : d8129 p = 1) : d2841 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2841, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43425 p hg
    simpa only [d8129, d2841, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2841, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43426 p hg
    simpa only [d8129, d2841, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43428 (p : Pattern) (guard : d8130 p = 1) : d2842 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2842, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43418 p hg
    simpa only [d8130, d2842, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2842, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43427 p hg
    simpa only [d8130, d2842, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43429 (p : Pattern) (guard : d8131 p = 1) : d2843 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2843, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43396 p hg
    simpa only [d8131, d2843, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2843, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43428 p hg
    simpa only [d8131, d2843, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43430 (p : Pattern) (guard : d8106 p = 1) : d2746 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d8106, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42792 p hg
    simpa only [d8106, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43431 (p : Pattern) (guard : d8111 p = 1) : d2746 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2746, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43421 p hg
    simpa only [d8111, d2746, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2746, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42931 p hg
    simpa only [d8111, d2746, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43432 (p : Pattern) (guard : d8112 p = 1) : d2746 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43430 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43431 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43433 (p : Pattern) (guard : d8117 p = 1) : d2749 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2749, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d8117, d2749, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2749, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42934 p hg
    simpa only [d8117, d2749, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43434 (p : Pattern) (guard : d8118 p = 1) : d2750 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2750, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43432 p hg
    simpa only [d8118, d2750, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2750, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43433 p hg
    simpa only [d8118, d2750, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43435 (p : Pattern) (guard : d8117 p = 1) : d2749 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2749, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42949 p hg
    simpa only [d8117, d2749, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2749, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42934 p hg
    simpa only [d8117, d2749, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43436 (p : Pattern) (guard : d8123 p = 1) : d2751 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2751, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43435 p hg
    simpa only [d8123, d2751, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2751, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42937 p hg
    simpa only [d8123, d2751, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43437 (p : Pattern) (guard : d8124 p = 1) : d2752 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2752, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43434 p hg
    simpa only [d8124, d2752, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2752, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43436 p hg
    simpa only [d8124, d2752, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43438 (p : Pattern) (guard : d8130 p = 1) : d2759 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2759, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43437 p hg
    simpa only [d8130, d2759, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2759, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42944 p hg
    simpa only [d8130, d2759, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43439 (p : Pattern) (guard : d5854 p = 1) : d2677 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35793 p hg
    simpa only [d5854, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43440 (p : Pattern) (guard : d8099 p = 1) : d2677 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43439 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21845 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43441 (p : Pattern) (guard : d8105 p = 1) : d2686 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2686, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43440 p hg
    simpa only [d8105, d2686, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2686, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22712 p hg
    simpa only [d8105, d2686, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43442 (p : Pattern) (guard : d8111 p = 1) : d2746 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2746, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43441 p hg
    simpa only [d8111, d2746, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2746, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42931 p hg
    simpa only [d8111, d2746, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43443 (p : Pattern) (guard : d0 p = 1) : d2753 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43444 (p : Pattern) (guard : d8117 p = 1) : d2760 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2760, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43442 p hg
    simpa only [d8117, d2760, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2760, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43443 p hg
    simpa only [d8117, d2760, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43445 (p : Pattern) (guard : d0 p = 1) : d2844 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43446 (p : Pattern) (guard : d8123 p = 1) : d2845 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2845, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43444 p hg
    simpa only [d8123, d2845, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2845, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43445 p hg
    simpa only [d8123, d2845, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43447 (p : Pattern) (guard : d0 p = 1) : d2846 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43448 (p : Pattern) (guard : d8129 p = 1) : d2847 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2847, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43446 p hg
    simpa only [d8129, d2847, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2847, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43447 p hg
    simpa only [d8129, d2847, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43449 (p : Pattern) (guard : d8135 p = 1) : d2848 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2848, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43448 p hg
    simpa only [d8135, d2848, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2848, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d8135, d2848, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43450 (p : Pattern) (guard : d8136 p = 1) : d2849 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2849, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43438 p hg
    simpa only [d8136, d2849, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2849, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43449 p hg
    simpa only [d8136, d2849, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43451 (p : Pattern) (guard : d8137 p = 1) : d2850 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2850, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43429 p hg
    simpa only [d8137, d2850, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2850, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43450 p hg
    simpa only [d8137, d2850, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43452 (p : Pattern) (guard : d8106 p = 1) : d2746 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2746, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43373 p hg
    simpa only [d8106, d2746, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2746, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42792 p hg
    simpa only [d8106, d2746, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43453 (p : Pattern) (guard : d8112 p = 1) : d2746 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43452 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43442 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43454 (p : Pattern) (guard : d8117 p = 1) : d2749 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43431 p hg
    simpa only [d8117, d2749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42934 p hg
    simpa only [d8117, d2749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43455 (p : Pattern) (guard : d8118 p = 1) : d2750 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2750, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43453 p hg
    simpa only [d8118, d2750, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2750, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43454 p hg
    simpa only [d8118, d2750, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43456 (p : Pattern) (guard : d8123 p = 1) : d2751 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2751, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43433 p hg
    simpa only [d8123, d2751, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2751, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42937 p hg
    simpa only [d8123, d2751, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43457 (p : Pattern) (guard : d8124 p = 1) : d2752 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2752, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43455 p hg
    simpa only [d8124, d2752, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2752, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43456 p hg
    simpa only [d8124, d2752, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43458 (p : Pattern) (guard : d8117 p = 1) : d2756 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2756, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42825 p hg
    simpa only [d8117, d2756, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2756, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42941 p hg
    simpa only [d8117, d2756, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43459 (p : Pattern) (guard : d8123 p = 1) : d2757 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2757, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43458 p hg
    simpa only [d8123, d2757, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2757, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2757, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43460 (p : Pattern) (guard : d8129 p = 1) : d2758 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2758, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43459 p hg
    simpa only [d8129, d2758, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2758, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2758, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43461 (p : Pattern) (guard : d8130 p = 1) : d2759 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2759, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43457 p hg
    simpa only [d8130, d2759, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2759, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43460 p hg
    simpa only [d8130, d2759, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43462 (p : Pattern) (guard : d5854 p = 1) : d2677 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35816 p hg
    simpa only [d5854, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43463 (p : Pattern) (guard : d8099 p = 1) : d2677 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43462 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21845 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43464 (p : Pattern) (guard : d8105 p = 1) : d2686 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43463 p hg
    simpa only [d8105, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22712 p hg
    simpa only [d8105, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43465 (p : Pattern) (guard : d8111 p = 1) : d2746 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2746, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43464 p hg
    simpa only [d8111, d2746, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2746, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42931 p hg
    simpa only [d8111, d2746, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43466 (p : Pattern) (guard : d0 p = 1) : d2753 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43467 (p : Pattern) (guard : d8117 p = 1) : d2760 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2760, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43465 p hg
    simpa only [d8117, d2760, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2760, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43466 p hg
    simpa only [d8117, d2760, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43468 (p : Pattern) (guard : d0 p = 1) : d2844 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43469 (p : Pattern) (guard : d8123 p = 1) : d2845 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2845, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43467 p hg
    simpa only [d8123, d2845, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2845, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43468 p hg
    simpa only [d8123, d2845, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43470 (p : Pattern) (guard : d8129 p = 1) : d2847 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2847, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43469 p hg
    simpa only [d8129, d2847, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2847, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43447 p hg
    simpa only [d8129, d2847, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43471 (p : Pattern) (guard : d8135 p = 1) : d2848 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2848, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43470 p hg
    simpa only [d8135, d2848, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2848, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d8135, d2848, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43472 (p : Pattern) (guard : d8136 p = 1) : d2849 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2849, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43461 p hg
    simpa only [d8136, d2849, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2849, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43471 p hg
    simpa only [d8136, d2849, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43473 (p : Pattern) (guard : d8123 p = 1) : d2772 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2772, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43386 p hg
    simpa only [d8123, d2772, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2772, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2772, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43474 (p : Pattern) (guard : d8129 p = 1) : d2773 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2773, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43473 p hg
    simpa only [d8129, d2773, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2773, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2773, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43475 (p : Pattern) (guard : d8135 p = 1) : d2774 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2774, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43474 p hg
    simpa only [d8135, d2774, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2774, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d2774, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43476 (p : Pattern) (guard : d8141 p = 1) : d2775 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d2775, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43475 p hg
    simpa only [d8141, d2775, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d2775, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8141, d2775, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43477 (p : Pattern) (guard : d8142 p = 1) : d2851 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2851, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43472 p hg
    simpa only [d8142, d2851, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2851, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43476 p hg
    simpa only [d8142, d2851, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43478 (p : Pattern) (guard : d8143 p = 1) : d2852 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2852, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43451 p hg
    simpa only [d8143, d2852, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2852, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43477 p hg
    simpa only [d8143, d2852, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43479 (p : Pattern) (guard : d8105 p = 1) : d2745 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2745, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43400 p hg
    simpa only [d8105, d2745, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2745, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2745, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43480 (p : Pattern) (guard : d8106 p = 1) : d2746 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2746, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43366 p hg
    simpa only [d8106, d2746, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2746, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43479 p hg
    simpa only [d8106, d2746, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43481 (p : Pattern) (guard : d8112 p = 1) : d2746 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43480 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43465 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43482 (p : Pattern) (guard : d0 p = 1) : d2748 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43483 (p : Pattern) (guard : d8117 p = 1) : d2749 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2749, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43442 p hg
    simpa only [d8117, d2749, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2749, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43482 p hg
    simpa only [d8117, d2749, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43484 (p : Pattern) (guard : d8118 p = 1) : d2750 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2750, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43481 p hg
    simpa only [d8118, d2750, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2750, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43483 p hg
    simpa only [d8118, d2750, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43485 (p : Pattern) (guard : d8123 p = 1) : d2751 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2751, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43454 p hg
    simpa only [d8123, d2751, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2751, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42937 p hg
    simpa only [d8123, d2751, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43486 (p : Pattern) (guard : d8124 p = 1) : d2752 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2752, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43484 p hg
    simpa only [d8124, d2752, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2752, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43485 p hg
    simpa only [d8124, d2752, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43487 (p : Pattern) (guard : d0 p = 1) : d2853 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43488 (p : Pattern) (guard : d8117 p = 1) : d2854 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2854, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42860 p hg
    simpa only [d8117, d2854, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2854, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43487 p hg
    simpa only [d8117, d2854, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43489 (p : Pattern) (guard : d8123 p = 1) : d2855 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2855, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43488 p hg
    simpa only [d8123, d2855, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2855, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43424 p hg
    simpa only [d8123, d2855, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43490 (p : Pattern) (guard : d0 p = 1) : d2858 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43491 (p : Pattern) (guard : d8129 p = 1) : d2859 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2859, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43489 p hg
    simpa only [d8129, d2859, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2859, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43490 p hg
    simpa only [d8129, d2859, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43492 (p : Pattern) (guard : d8130 p = 1) : d2860 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2860, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43486 p hg
    simpa only [d8130, d2860, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2860, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43491 p hg
    simpa only [d8130, d2860, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43493 (p : Pattern) (guard : d5854 p = 1) : d2677 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35834 p hg
    simpa only [d5854, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43494 (p : Pattern) (guard : d8099 p = 1) : d2677 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43493 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21845 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43495 (p : Pattern) (guard : d8105 p = 1) : d2686 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43494 p hg
    simpa only [d8105, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22712 p hg
    simpa only [d8105, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43496 (p : Pattern) (guard : d8111 p = 1) : d2746 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43495 p hg
    simpa only [d8111, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42931 p hg
    simpa only [d8111, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43497 (p : Pattern) (guard : d0 p = 1) : d2753 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43498 (p : Pattern) (guard : d8117 p = 1) : d2760 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2760, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43496 p hg
    simpa only [d8117, d2760, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2760, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43497 p hg
    simpa only [d8117, d2760, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43499 (p : Pattern) (guard : d0 p = 1) : d2844 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43500 (p : Pattern) (guard : d8123 p = 1) : d2845 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2845, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43498 p hg
    simpa only [d8123, d2845, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2845, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43499 p hg
    simpa only [d8123, d2845, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43501 (p : Pattern) (guard : d0 p = 1) : d2846 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43502 (p : Pattern) (guard : d8129 p = 1) : d2847 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2847, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43500 p hg
    simpa only [d8129, d2847, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2847, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43501 p hg
    simpa only [d8129, d2847, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43503 (p : Pattern) (guard : d0 p = 1) : d2865 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43504 (p : Pattern) (guard : d8135 p = 1) : d2866 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2866, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43502 p hg
    simpa only [d8135, d2866, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2866, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43503 p hg
    simpa only [d8135, d2866, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43505 (p : Pattern) (guard : d8136 p = 1) : d2867 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2867, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43492 p hg
    simpa only [d8136, d2867, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2867, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43504 p hg
    simpa only [d8136, d2867, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43506 (p : Pattern) (guard : d0 p = 1) : d2746 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43507 (p : Pattern) (guard : d8117 p = 1) : d2746 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43431 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43506 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43508 (p : Pattern) (guard : d0 p = 1) : d2868 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43509 (p : Pattern) (guard : d8123 p = 1) : d2869 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2869, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43507 p hg
    simpa only [d8123, d2869, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2869, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43508 p hg
    simpa only [d8123, d2869, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43510 (p : Pattern) (guard : d8129 p = 1) : d2870 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2870, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43509 p hg
    simpa only [d8129, d2870, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2870, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d8129, d2870, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43511 (p : Pattern) (guard : d8135 p = 1) : d2871 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2871, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43510 p hg
    simpa only [d8135, d2871, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2871, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d8135, d2871, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43512 (p : Pattern) (guard : d0 p = 1) : d2876 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43513 (p : Pattern) (guard : d8141 p = 1) : d2877 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d2877, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43511 p hg
    simpa only [d8141, d2877, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d2877, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43512 p hg
    simpa only [d8141, d2877, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43514 (p : Pattern) (guard : d8142 p = 1) : d2878 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2878, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43505 p hg
    simpa only [d8142, d2878, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2878, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43513 p hg
    simpa only [d8142, d2878, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43515 (p : Pattern) (guard : d0 p = 1) : d2746 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43516 (p : Pattern) (guard : d8117 p = 1) : d2746 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43442 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43515 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43517 (p : Pattern) (guard : d0 p = 1) : d2879 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43518 (p : Pattern) (guard : d8123 p = 1) : d2880 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2880, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43516 p hg
    simpa only [d8123, d2880, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2880, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43517 p hg
    simpa only [d8123, d2880, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43519 (p : Pattern) (guard : d0 p = 1) : d2882 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43520 (p : Pattern) (guard : d8129 p = 1) : d2883 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2883, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43518 p hg
    simpa only [d8129, d2883, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2883, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43519 p hg
    simpa only [d8129, d2883, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43521 (p : Pattern) (guard : d0 p = 1) : d2886 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43522 (p : Pattern) (guard : d8135 p = 1) : d2887 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2887, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43520 p hg
    simpa only [d8135, d2887, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2887, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43521 p hg
    simpa only [d8135, d2887, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43523 (p : Pattern) (guard : d0 p = 1) : d2876 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43524 (p : Pattern) (guard : d8141 p = 1) : d2888 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d2888, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43522 p hg
    simpa only [d8141, d2888, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d2888, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43523 p hg
    simpa only [d8141, d2888, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43525 (p : Pattern) (guard : d8147 p = 1) : d2889 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d2889, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43524 p hg
    simpa only [d8147, d2889, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d2889, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d2889, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43526 (p : Pattern) (guard : d8148 p = 1) : d2890 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d2890, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43514 p hg
    simpa only [d8148, d2890, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d2890, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43525 p hg
    simpa only [d8148, d2890, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43527 (p : Pattern) (guard : d8149 p = 1) : d2891 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d2891, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43478 p hg
    simpa only [d8149, d2891, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d2891, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43526 p hg
    simpa only [d8149, d2891, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43528 (p : Pattern) (guard : d8150 p = 1) : d2892 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d2892, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43355 p hg
    simpa only [d8150, d2892, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d2892, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43527 p hg
    simpa only [d8150, d2892, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43529 (p : Pattern) (guard : d8151 p = 1) : d2893 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43187 p hg
    simpa only [d8151, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43528 p hg
    simpa only [d8151, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43530 (p : Pattern) (guard : d8152 p = 1) : d2894 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42977 p hg
    simpa only [d8152, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43529 p hg
    simpa only [d8152, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43531 (p : Pattern) (guard : d8087 p = 1) : d324 p ≤ (0 : Int) + d324 p := by
  omega
theorem compare43532 (p : Pattern) (guard : d8088 p = 1) : d1504 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8088, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34326 p hg
    simpa only [d8088, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8087 p = 1 := by simpa only [d8088, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43531 p hg
    simpa only [d8088, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43533 (p : Pattern) (guard : d8091 p = 1) : d336 p ≤ (0 : Int) + d336 p := by
  omega
theorem compare43534 (p : Pattern) (guard : d8092 p = 1) : d1505 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34342 p hg
    simpa only [d8092, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43533 p hg
    simpa only [d8092, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43535 (p : Pattern) (guard : d8093 p = 1) : d1506 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43532 p hg
    simpa only [d8093, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43534 p hg
    simpa only [d8093, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43536 (p : Pattern) (guard : d8091 p = 1) : d343 p ≤ (0 : Int) + d343 p := by
  omega
theorem compare43537 (p : Pattern) (guard : d8092 p = 1) : d1507 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34352 p hg
    simpa only [d8092, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43536 p hg
    simpa only [d8092, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43538 (p : Pattern) (guard : d8096 p = 1) : d43 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34366 p hg
    simpa only [d8096, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43539 (p : Pattern) (guard : d8097 p = 1) : d1508 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43537 p hg
    simpa only [d8097, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43538 p hg
    simpa only [d8097, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
