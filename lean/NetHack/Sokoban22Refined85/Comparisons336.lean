/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons335
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47040 (p : Pattern) (guard : d8105 p = 1) : d3023 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3023, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39302 p hg
    simpa only [d8105, d3023, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3023, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24064 p hg
    simpa only [d8105, d3023, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47041 (p : Pattern) (guard : d8111 p = 1) : d3048 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3048, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47040 p hg
    simpa only [d8111, d3048, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3048, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d8111, d3048, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47042 (p : Pattern) (guard : d8112 p = 1) : d3055 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3055, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47039 p hg
    simpa only [d8112, d3055, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3055, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47041 p hg
    simpa only [d8112, d3055, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47043 (p : Pattern) (guard : d8105 p = 1) : d3007 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3007, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35307 p hg
    simpa only [d8105, d3007, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3007, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24043 p hg
    simpa only [d8105, d3007, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47044 (p : Pattern) (guard : d8111 p = 1) : d3043 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3043, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47043 p hg
    simpa only [d8111, d3043, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3043, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15472 p hg
    simpa only [d8111, d3043, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47045 (p : Pattern) (guard : d8117 p = 1) : d3056 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3056, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47044 p hg
    simpa only [d8117, d3056, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3056, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46738 p hg
    simpa only [d8117, d3056, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47046 (p : Pattern) (guard : d8118 p = 1) : d3057 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3057, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47042 p hg
    simpa only [d8118, d3057, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3057, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47045 p hg
    simpa only [d8118, d3057, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47047 (p : Pattern) (guard : d8124 p = 1) : d3060 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3060, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47046 p hg
    simpa only [d8124, d3060, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3060, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47016 p hg
    simpa only [d8124, d3060, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47048 (p : Pattern) (guard : d8130 p = 1) : d3064 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3064, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47047 p hg
    simpa only [d8130, d3064, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3064, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47020 p hg
    simpa only [d8130, d3064, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47049 (p : Pattern) (guard : d8131 p = 1) : d3065 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3065, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47037 p hg
    simpa only [d8131, d3065, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3065, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47048 p hg
    simpa only [d8131, d3065, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47050 (p : Pattern) (guard : d8118 p = 1) : d3067 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3067, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46922 p hg
    simpa only [d8118, d3067, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3067, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3067, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47051 (p : Pattern) (guard : d8124 p = 1) : d3068 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3068, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47050 p hg
    simpa only [d8124, d3068, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3068, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3068, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47052 (p : Pattern) (guard : d8130 p = 1) : d3069 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3069, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47051 p hg
    simpa only [d8130, d3069, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3069, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d3069, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47053 (p : Pattern) (guard : d8136 p = 1) : d3070 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3070, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47052 p hg
    simpa only [d8136, d3070, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3070, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d8136, d3070, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47054 (p : Pattern) (guard : d8137 p = 1) : d3071 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3071, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47049 p hg
    simpa only [d8137, d3071, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3071, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47053 p hg
    simpa only [d8137, d3071, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47055 (p : Pattern) (guard : d8138 p = 1) : d3072 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3072, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47023 p hg
    simpa only [d8138, d3072, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3072, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47054 p hg
    simpa only [d8138, d3072, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47056 (p : Pattern) (guard : d8100 p = 1) : d2993 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2993, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35300 p hg
    simpa only [d8100, d2993, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2993, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39364 p hg
    simpa only [d8100, d2993, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47057 (p : Pattern) (guard : d8106 p = 1) : d2994 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2994, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47056 p hg
    simpa only [d8106, d2994, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2994, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d2994, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47058 (p : Pattern) (guard : d8107 p = 1) : d2994 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46907 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47057 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47059 (p : Pattern) (guard : d8100 p = 1) : d2993 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2993, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35274 p hg
    simpa only [d8100, d2993, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2993, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39364 p hg
    simpa only [d8100, d2993, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47060 (p : Pattern) (guard : d8106 p = 1) : d2994 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2994, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47059 p hg
    simpa only [d8106, d2994, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2994, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d2994, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47061 (p : Pattern) (guard : d8105 p = 1) : d2995 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2995, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35307 p hg
    simpa only [d8105, d2995, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2995, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24029 p hg
    simpa only [d8105, d2995, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47062 (p : Pattern) (guard : d8111 p = 1) : d2996 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2996, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47061 p hg
    simpa only [d8111, d2996, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2996, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d2996, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47063 (p : Pattern) (guard : d8112 p = 1) : d2997 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2997, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47060 p hg
    simpa only [d8112, d2997, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2997, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47062 p hg
    simpa only [d8112, d2997, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47064 (p : Pattern) (guard : d8113 p = 1) : d2998 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2998, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47058 p hg
    simpa only [d8113, d2998, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2998, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47063 p hg
    simpa only [d8113, d2998, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47065 (p : Pattern) (guard : d8100 p = 1) : d2993 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2993, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35238 p hg
    simpa only [d8100, d2993, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2993, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39364 p hg
    simpa only [d8100, d2993, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47066 (p : Pattern) (guard : d8106 p = 1) : d2994 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2994, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47065 p hg
    simpa only [d8106, d2994, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2994, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d2994, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47067 (p : Pattern) (guard : d8105 p = 1) : d2995 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35137 p hg
    simpa only [d8105, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24029 p hg
    simpa only [d8105, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47068 (p : Pattern) (guard : d8111 p = 1) : d2996 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47067 p hg
    simpa only [d8111, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47069 (p : Pattern) (guard : d8112 p = 1) : d2997 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2997, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47066 p hg
    simpa only [d8112, d2997, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2997, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47068 p hg
    simpa only [d8112, d2997, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47070 (p : Pattern) (guard : d8118 p = 1) : d3000 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3000, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47069 p hg
    simpa only [d8118, d3000, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3000, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46996 p hg
    simpa only [d8118, d3000, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47071 (p : Pattern) (guard : d8119 p = 1) : d3001 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3001, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47064 p hg
    simpa only [d8119, d3001, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3001, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47070 p hg
    simpa only [d8119, d3001, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47072 (p : Pattern) (guard : d8106 p = 1) : d3003 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3003, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46932 p hg
    simpa only [d8106, d3003, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3003, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39261 p hg
    simpa only [d8106, d3003, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47073 (p : Pattern) (guard : d8105 p = 1) : d3002 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8105, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24037 p hg
    simpa only [d8105, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47074 (p : Pattern) (guard : d8111 p = 1) : d3004 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47073 p hg
    simpa only [d8111, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d8111, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47075 (p : Pattern) (guard : d8112 p = 1) : d3005 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3005, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47072 p hg
    simpa only [d8112, d3005, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3005, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47074 p hg
    simpa only [d8112, d3005, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47076 (p : Pattern) (guard : d8111 p = 1) : d3006 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47073 p hg
    simpa only [d8111, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47077 (p : Pattern) (guard : d0 p = 1) : d3008 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47078 (p : Pattern) (guard : d8117 p = 1) : d3009 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47076 p hg
    simpa only [d8117, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47077 p hg
    simpa only [d8117, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47079 (p : Pattern) (guard : d8118 p = 1) : d3010 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3010, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47075 p hg
    simpa only [d8118, d3010, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3010, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47078 p hg
    simpa only [d8118, d3010, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47080 (p : Pattern) (guard : d0 p = 1) : d3011 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47081 (p : Pattern) (guard : d8123 p = 1) : d3012 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47078 p hg
    simpa only [d8123, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47080 p hg
    simpa only [d8123, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47082 (p : Pattern) (guard : d8124 p = 1) : d3013 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3013, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47079 p hg
    simpa only [d8124, d3013, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3013, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47081 p hg
    simpa only [d8124, d3013, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47083 (p : Pattern) (guard : d8125 p = 1) : d3014 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3014, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47071 p hg
    simpa only [d8125, d3014, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3014, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47082 p hg
    simpa only [d8125, d3014, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47084 (p : Pattern) (guard : d8100 p = 1) : d2993 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2993, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35327 p hg
    simpa only [d8100, d2993, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2993, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39364 p hg
    simpa only [d8100, d2993, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47085 (p : Pattern) (guard : d8106 p = 1) : d2994 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2994, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47084 p hg
    simpa only [d8106, d2994, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2994, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d2994, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47086 (p : Pattern) (guard : d8105 p = 1) : d3015 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3015, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35333 p hg
    simpa only [d8105, d3015, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3015, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24055 p hg
    simpa only [d8105, d3015, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47087 (p : Pattern) (guard : d8111 p = 1) : d3016 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3016, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47086 p hg
    simpa only [d8111, d3016, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3016, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15448 p hg
    simpa only [d8111, d3016, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47088 (p : Pattern) (guard : d8112 p = 1) : d3017 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3017, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47085 p hg
    simpa only [d8112, d3017, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3017, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47087 p hg
    simpa only [d8112, d3017, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47089 (p : Pattern) (guard : d8105 p = 1) : d2995 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2995, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35340 p hg
    simpa only [d8105, d2995, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2995, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24029 p hg
    simpa only [d8105, d2995, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47090 (p : Pattern) (guard : d8111 p = 1) : d2996 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2996, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47089 p hg
    simpa only [d8111, d2996, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2996, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d2996, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47091 (p : Pattern) (guard : d8117 p = 1) : d3018 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3018, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47090 p hg
    simpa only [d8117, d3018, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3018, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46738 p hg
    simpa only [d8117, d3018, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47092 (p : Pattern) (guard : d8118 p = 1) : d3019 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3019, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47088 p hg
    simpa only [d8118, d3019, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3019, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47091 p hg
    simpa only [d8118, d3019, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47093 (p : Pattern) (guard : d8117 p = 1) : d3020 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3020, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47062 p hg
    simpa only [d8117, d3020, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3020, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47014 p hg
    simpa only [d8117, d3020, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47094 (p : Pattern) (guard : d8123 p = 1) : d3021 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3021, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47093 p hg
    simpa only [d8123, d3021, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3021, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3021, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47095 (p : Pattern) (guard : d8124 p = 1) : d3022 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3022, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47092 p hg
    simpa only [d8124, d3022, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3022, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47094 p hg
    simpa only [d8124, d3022, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47096 (p : Pattern) (guard : d0 p = 1) : d3024 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47097 (p : Pattern) (guard : d8117 p = 1) : d3025 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47074 p hg
    simpa only [d8117, d3025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47096 p hg
    simpa only [d8117, d3025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47098 (p : Pattern) (guard : d0 p = 1) : d3026 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47099 (p : Pattern) (guard : d8123 p = 1) : d3027 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47097 p hg
    simpa only [d8123, d3027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47098 p hg
    simpa only [d8123, d3027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47100 (p : Pattern) (guard : d0 p = 1) : d3029 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47101 (p : Pattern) (guard : d8129 p = 1) : d3030 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47099 p hg
    simpa only [d8129, d3030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47100 p hg
    simpa only [d8129, d3030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47102 (p : Pattern) (guard : d8130 p = 1) : d3031 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3031, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47095 p hg
    simpa only [d8130, d3031, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3031, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47101 p hg
    simpa only [d8130, d3031, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47103 (p : Pattern) (guard : d8131 p = 1) : d3032 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3032, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47083 p hg
    simpa only [d8131, d3032, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3032, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47102 p hg
    simpa only [d8131, d3032, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47104 (p : Pattern) (guard : d0 p = 1) : d2107 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47105 (p : Pattern) (guard : d8099 p = 1) : d2108 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39240 p hg
    simpa only [d8099, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47104 p hg
    simpa only [d8099, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47106 (p : Pattern) (guard : d8100 p = 1) : d3033 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3033, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35238 p hg
    simpa only [d8100, d3033, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3033, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47105 p hg
    simpa only [d8100, d3033, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47107 (p : Pattern) (guard : d8106 p = 1) : d3034 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3034, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47106 p hg
    simpa only [d8106, d3034, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3034, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39365 p hg
    simpa only [d8106, d3034, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47108 (p : Pattern) (guard : d8105 p = 1) : d3039 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8105, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24078 p hg
    simpa only [d8105, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47109 (p : Pattern) (guard : d8111 p = 1) : d3040 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47108 p hg
    simpa only [d8111, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47110 (p : Pattern) (guard : d8112 p = 1) : d3041 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3041, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47107 p hg
    simpa only [d8112, d3041, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3041, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47109 p hg
    simpa only [d8112, d3041, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47111 (p : Pattern) (guard : d8111 p = 1) : d3042 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47073 p hg
    simpa only [d8111, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d8111, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47112 (p : Pattern) (guard : d0 p = 1) : d3043 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47113 (p : Pattern) (guard : d8117 p = 1) : d3044 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47111 p hg
    simpa only [d8117, d3044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47112 p hg
    simpa only [d8117, d3044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47114 (p : Pattern) (guard : d8118 p = 1) : d3045 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3045, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47110 p hg
    simpa only [d8118, d3045, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3045, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47113 p hg
    simpa only [d8118, d3045, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47115 (p : Pattern) (guard : d0 p = 1) : d2999 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47116 (p : Pattern) (guard : d8123 p = 1) : d3046 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47113 p hg
    simpa only [d8123, d3046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47115 p hg
    simpa only [d8123, d3046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47117 (p : Pattern) (guard : d8124 p = 1) : d3047 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3047, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47114 p hg
    simpa only [d8124, d3047, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3047, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47116 p hg
    simpa only [d8124, d3047, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47118 (p : Pattern) (guard : d8111 p = 1) : d3048 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46970 p hg
    simpa only [d8111, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15431 p hg
    simpa only [d8111, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47119 (p : Pattern) (guard : d0 p = 1) : d3050 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47120 (p : Pattern) (guard : d8117 p = 1) : d3051 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47118 p hg
    simpa only [d8117, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47119 p hg
    simpa only [d8117, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47121 (p : Pattern) (guard : d8123 p = 1) : d3052 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47120 p hg
    simpa only [d8123, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47122 (p : Pattern) (guard : d8129 p = 1) : d3053 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47121 p hg
    simpa only [d8129, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47123 (p : Pattern) (guard : d8130 p = 1) : d3054 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3054, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47117 p hg
    simpa only [d8130, d3054, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3054, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47122 p hg
    simpa only [d8130, d3054, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47124 (p : Pattern) (guard : d8105 p = 1) : d3039 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3039, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35368 p hg
    simpa only [d8105, d3039, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3039, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24078 p hg
    simpa only [d8105, d3039, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47125 (p : Pattern) (guard : d8111 p = 1) : d3040 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3040, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47124 p hg
    simpa only [d8111, d3040, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3040, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d3040, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47126 (p : Pattern) (guard : d0 p = 1) : d3048 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47127 (p : Pattern) (guard : d8117 p = 1) : d3055 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3055, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47125 p hg
    simpa only [d8117, d3055, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3055, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47126 p hg
    simpa only [d8117, d3055, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47128 (p : Pattern) (guard : d0 p = 1) : d3056 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47129 (p : Pattern) (guard : d8123 p = 1) : d3057 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3057, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47127 p hg
    simpa only [d8123, d3057, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3057, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47128 p hg
    simpa only [d8123, d3057, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47130 (p : Pattern) (guard : d0 p = 1) : d3059 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47131 (p : Pattern) (guard : d8129 p = 1) : d3060 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3060, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47129 p hg
    simpa only [d8129, d3060, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3060, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47130 p hg
    simpa only [d8129, d3060, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47132 (p : Pattern) (guard : d0 p = 1) : d3063 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47133 (p : Pattern) (guard : d8135 p = 1) : d3064 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3064, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47131 p hg
    simpa only [d8135, d3064, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3064, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47132 p hg
    simpa only [d8135, d3064, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47134 (p : Pattern) (guard : d8136 p = 1) : d3065 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3065, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47123 p hg
    simpa only [d8136, d3065, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3065, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47133 p hg
    simpa only [d8136, d3065, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47135 (p : Pattern) (guard : d8137 p = 1) : d3066 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3066, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47103 p hg
    simpa only [d8137, d3066, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3066, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47134 p hg
    simpa only [d8137, d3066, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47136 (p : Pattern) (guard : d8100 p = 1) : d3033 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3033, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35274 p hg
    simpa only [d8100, d3033, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3033, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47105 p hg
    simpa only [d8100, d3033, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47137 (p : Pattern) (guard : d8106 p = 1) : d3034 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3034, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47136 p hg
    simpa only [d8106, d3034, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3034, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39365 p hg
    simpa only [d8106, d3034, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47138 (p : Pattern) (guard : d8112 p = 1) : d3041 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3041, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47137 p hg
    simpa only [d8112, d3041, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3041, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47125 p hg
    simpa only [d8112, d3041, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47139 (p : Pattern) (guard : d8118 p = 1) : d3045 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3045, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47138 p hg
    simpa only [d8118, d3045, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3045, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47113 p hg
    simpa only [d8118, d3045, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47140 (p : Pattern) (guard : d8124 p = 1) : d3047 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3047, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47139 p hg
    simpa only [d8124, d3047, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3047, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47116 p hg
    simpa only [d8124, d3047, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47141 (p : Pattern) (guard : d8130 p = 1) : d3054 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3054, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47140 p hg
    simpa only [d8130, d3054, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3054, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47122 p hg
    simpa only [d8130, d3054, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47142 (p : Pattern) (guard : d8105 p = 1) : d3039 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3039, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35735 p hg
    simpa only [d8105, d3039, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3039, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24078 p hg
    simpa only [d8105, d3039, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47143 (p : Pattern) (guard : d8111 p = 1) : d3040 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3040, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47142 p hg
    simpa only [d8111, d3040, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3040, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d3040, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47144 (p : Pattern) (guard : d8117 p = 1) : d3055 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3055, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47143 p hg
    simpa only [d8117, d3055, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3055, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47126 p hg
    simpa only [d8117, d3055, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47145 (p : Pattern) (guard : d8123 p = 1) : d3057 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3057, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47144 p hg
    simpa only [d8123, d3057, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3057, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47128 p hg
    simpa only [d8123, d3057, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47146 (p : Pattern) (guard : d8129 p = 1) : d3060 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3060, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47145 p hg
    simpa only [d8129, d3060, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3060, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47130 p hg
    simpa only [d8129, d3060, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47147 (p : Pattern) (guard : d8135 p = 1) : d3064 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3064, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47146 p hg
    simpa only [d8135, d3064, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3064, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47132 p hg
    simpa only [d8135, d3064, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47148 (p : Pattern) (guard : d8136 p = 1) : d3065 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3065, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47141 p hg
    simpa only [d8136, d3065, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3065, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47147 p hg
    simpa only [d8136, d3065, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47149 (p : Pattern) (guard : d8142 p = 1) : d3073 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3073, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47148 p hg
    simpa only [d8142, d3073, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3073, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d3073, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47150 (p : Pattern) (guard : d8143 p = 1) : d3074 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3074, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47135 p hg
    simpa only [d8143, d3074, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3074, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47149 p hg
    simpa only [d8143, d3074, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47151 (p : Pattern) (guard : d8144 p = 1) : d3075 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d3075, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47055 p hg
    simpa only [d8144, d3075, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d3075, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47150 p hg
    simpa only [d8144, d3075, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47152 (p : Pattern) (guard : d8145 p = 1) : d3076 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d3076, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46900 p hg
    simpa only [d8145, d3076, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d3076, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47151 p hg
    simpa only [d8145, d3076, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47153 (p : Pattern) (guard : d8146 p = 1) : d3077 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46765 p hg
    simpa only [d8146, d3077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47152 p hg
    simpa only [d8146, d3077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47154 (p : Pattern) (guard : d8085 p = 1) : d1771 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1771, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d8085, d1771, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1771, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8085, d1771, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47155 (p : Pattern) (guard : d8090 p = 1) : d1772 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1772, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47154 p hg
    simpa only [d8090, d1772, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1772, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38702 p hg
    simpa only [d8090, d1772, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47156 (p : Pattern) (guard : d8091 p = 1) : d2895 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2895, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35382 p hg
    simpa only [d8091, d2895, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2895, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47155 p hg
    simpa only [d8091, d2895, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47157 (p : Pattern) (guard : d8096 p = 1) : d2896 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2896, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47156 p hg
    simpa only [d8096, d2896, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2896, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39412 p hg
    simpa only [d8096, d2896, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47158 (p : Pattern) (guard : d8095 p = 1) : d2895 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35387 p hg
    simpa only [d8095, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38945 p hg
    simpa only [d8095, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47159 (p : Pattern) (guard : d8101 p = 1) : d2896 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47158 p hg
    simpa only [d8101, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39417 p hg
    simpa only [d8101, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47160 (p : Pattern) (guard : d8102 p = 1) : d2896 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47157 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47159 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47161 (p : Pattern) (guard : d8100 p = 1) : d2897 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35394 p hg
    simpa only [d8100, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46653 p hg
    simpa only [d8100, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47162 (p : Pattern) (guard : d8106 p = 1) : d2898 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47161 p hg
    simpa only [d8106, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47163 (p : Pattern) (guard : d8107 p = 1) : d2899 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46864 p hg
    simpa only [d8107, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47162 p hg
    simpa only [d8107, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47164 (p : Pattern) (guard : d8108 p = 1) : d2900 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2900, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47160 p hg
    simpa only [d8108, d2900, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2900, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47163 p hg
    simpa only [d8108, d2900, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47165 (p : Pattern) (guard : d8107 p = 1) : d2899 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2899, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46682 p hg
    simpa only [d8107, d2899, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2899, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46869 p hg
    simpa only [d8107, d2899, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47166 (p : Pattern) (guard : d8112 p = 1) : d2903 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2903, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46577 p hg
    simpa only [d8112, d2903, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2903, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2903, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47167 (p : Pattern) (guard : d8113 p = 1) : d2904 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2904, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47165 p hg
    simpa only [d8113, d2904, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2904, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47166 p hg
    simpa only [d8113, d2904, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47168 (p : Pattern) (guard : d8114 p = 1) : d2905 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2905, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47164 p hg
    simpa only [d8114, d2905, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2905, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47167 p hg
    simpa only [d8114, d2905, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47169 (p : Pattern) (guard : d8095 p = 1) : d2906 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2906, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34845 p hg
    simpa only [d8095, d2906, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2906, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38715 p hg
    simpa only [d8095, d2906, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47170 (p : Pattern) (guard : d8101 p = 1) : d2907 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2907, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47169 p hg
    simpa only [d8101, d2907, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2907, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d2907, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47171 (p : Pattern) (guard : d8100 p = 1) : d2906 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35071 p hg
    simpa only [d8100, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38955 p hg
    simpa only [d8100, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47172 (p : Pattern) (guard : d8106 p = 1) : d2908 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2908, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47171 p hg
    simpa only [d8106, d2908, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2908, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d2908, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47173 (p : Pattern) (guard : d8107 p = 1) : d2909 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2909, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47170 p hg
    simpa only [d8107, d2909, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2909, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47172 p hg
    simpa only [d8107, d2909, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47174 (p : Pattern) (guard : d8106 p = 1) : d2910 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2910, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46875 p hg
    simpa only [d8106, d2910, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2910, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d2910, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47175 (p : Pattern) (guard : d8112 p = 1) : d2913 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2913, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47174 p hg
    simpa only [d8112, d2913, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2913, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d8112, d2913, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47176 (p : Pattern) (guard : d8113 p = 1) : d2914 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2914, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47173 p hg
    simpa only [d8113, d2914, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2914, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47175 p hg
    simpa only [d8113, d2914, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47177 (p : Pattern) (guard : d8119 p = 1) : d2920 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2920, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47176 p hg
    simpa only [d8119, d2920, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2920, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46678 p hg
    simpa only [d8119, d2920, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47178 (p : Pattern) (guard : d8120 p = 1) : d2921 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2921, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47168 p hg
    simpa only [d8120, d2921, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2921, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47177 p hg
    simpa only [d8120, d2921, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47179 (p : Pattern) (guard : d8095 p = 1) : d2895 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35412 p hg
    simpa only [d8095, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39514 p hg
    simpa only [d8095, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
