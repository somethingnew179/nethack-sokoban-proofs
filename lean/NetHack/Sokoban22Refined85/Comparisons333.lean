/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons332
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46620 (p : Pattern) (guard : d8107 p = 1) : d2964 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46619 p hg
    simpa only [d8107, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46500 p hg
    simpa only [d8107, d2964, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46621 (p : Pattern) (guard : d8113 p = 1) : d2965 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46620 p hg
    simpa only [d8113, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8113, d2965, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46622 (p : Pattern) (guard : d8119 p = 1) : d2966 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46621 p hg
    simpa only [d8119, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2966, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46623 (p : Pattern) (guard : d8120 p = 1) : d2967 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46618 p hg
    simpa only [d8120, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46622 p hg
    simpa only [d8120, d2967, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46624 (p : Pattern) (guard : d8095 p = 1) : d2950 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34845 p hg
    simpa only [d8095, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46486 p hg
    simpa only [d8095, d2950, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46625 (p : Pattern) (guard : d8101 p = 1) : d2951 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46624 p hg
    simpa only [d8101, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d2951, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46626 (p : Pattern) (guard : d8100 p = 1) : d2935 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35017 p hg
    simpa only [d8100, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38741 p hg
    simpa only [d8100, d2935, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46627 (p : Pattern) (guard : d8106 p = 1) : d2961 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46626 p hg
    simpa only [d8106, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d2961, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46628 (p : Pattern) (guard : d8107 p = 1) : d2968 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46625 p hg
    simpa only [d8107, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46627 p hg
    simpa only [d8107, d2968, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46629 (p : Pattern) (guard : d8100 p = 1) : d2911 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34851 p hg
    simpa only [d8100, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38720 p hg
    simpa only [d8100, d2911, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46630 (p : Pattern) (guard : d8106 p = 1) : d2954 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46629 p hg
    simpa only [d8106, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38721 p hg
    simpa only [d8106, d2954, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46631 (p : Pattern) (guard : d8112 p = 1) : d2969 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46630 p hg
    simpa only [d8112, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46509 p hg
    simpa only [d8112, d2969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46632 (p : Pattern) (guard : d8113 p = 1) : d2970 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46628 p hg
    simpa only [d8113, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46631 p hg
    simpa only [d8113, d2970, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46633 (p : Pattern) (guard : d8119 p = 1) : d2973 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46632 p hg
    simpa only [d8119, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46516 p hg
    simpa only [d8119, d2973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46634 (p : Pattern) (guard : d8125 p = 1) : d2977 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46633 p hg
    simpa only [d8125, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46520 p hg
    simpa only [d8125, d2977, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46635 (p : Pattern) (guard : d8126 p = 1) : d2978 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46623 p hg
    simpa only [d8126, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46634 p hg
    simpa only [d8126, d2978, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46636 (p : Pattern) (guard : d8101 p = 1) : d2957 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2957, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46554 p hg
    simpa only [d8101, d2957, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2957, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38516 p hg
    simpa only [d8101, d2957, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46637 (p : Pattern) (guard : d8107 p = 1) : d2980 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2980, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46636 p hg
    simpa only [d8107, d2980, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2980, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46359 p hg
    simpa only [d8107, d2980, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46638 (p : Pattern) (guard : d8113 p = 1) : d2981 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2981, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46637 p hg
    simpa only [d8113, d2981, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2981, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8113, d2981, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46639 (p : Pattern) (guard : d8118 p = 1) : d2982 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8118, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46640 (p : Pattern) (guard : d8119 p = 1) : d2983 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2983, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46638 p hg
    simpa only [d8119, d2983, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2983, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46639 p hg
    simpa only [d8119, d2983, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46641 (p : Pattern) (guard : d8124 p = 1) : d2984 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46639 p hg
    simpa only [d8124, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46642 (p : Pattern) (guard : d8125 p = 1) : d2985 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2985, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46640 p hg
    simpa only [d8125, d2985, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2985, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46641 p hg
    simpa only [d8125, d2985, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46643 (p : Pattern) (guard : d8130 p = 1) : d2986 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46641 p hg
    simpa only [d8130, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46644 (p : Pattern) (guard : d8131 p = 1) : d2987 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2987, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46642 p hg
    simpa only [d8131, d2987, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2987, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46643 p hg
    simpa only [d8131, d2987, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46645 (p : Pattern) (guard : d8132 p = 1) : d2988 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2988, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46635 p hg
    simpa only [d8132, d2988, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2988, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d8132, d2988, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46646 (p : Pattern) (guard : d8133 p = 1) : d2989 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d2989, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46610 p hg
    simpa only [d8133, d2989, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d2989, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d8133, d2989, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46647 (p : Pattern) (guard : d8095 p = 1) : d2895 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34845 p hg
    simpa only [d8095, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38945 p hg
    simpa only [d8095, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46648 (p : Pattern) (guard : d8101 p = 1) : d2896 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d8101, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46649 (p : Pattern) (guard : d8102 p = 1) : d2896 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46547 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46650 (p : Pattern) (guard : d8095 p = 1) : d2895 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34828 p hg
    simpa only [d8095, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38945 p hg
    simpa only [d8095, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46651 (p : Pattern) (guard : d8101 p = 1) : d2896 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46650 p hg
    simpa only [d8101, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46652 (p : Pattern) (guard : d5854 p = 1) : d2011 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d5854, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17458 p hg
    simpa only [d5854, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46653 (p : Pattern) (guard : d8099 p = 1) : d2012 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46652 p hg
    simpa only [d8099, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17458 p hg
    simpa only [d8099, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46654 (p : Pattern) (guard : d8100 p = 1) : d2897 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34851 p hg
    simpa only [d8100, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46653 p hg
    simpa only [d8100, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46655 (p : Pattern) (guard : d8106 p = 1) : d2898 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46654 p hg
    simpa only [d8106, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46656 (p : Pattern) (guard : d8107 p = 1) : d2899 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46651 p hg
    simpa only [d8107, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46655 p hg
    simpa only [d8107, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46657 (p : Pattern) (guard : d8108 p = 1) : d2900 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2900, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d8108, d2900, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2900, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46656 p hg
    simpa only [d8108, d2900, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46658 (p : Pattern) (guard : d8095 p = 1) : d2895 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2895, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34811 p hg
    simpa only [d8095, d2895, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2895, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38945 p hg
    simpa only [d8095, d2895, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46659 (p : Pattern) (guard : d8101 p = 1) : d2896 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2896, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46658 p hg
    simpa only [d8101, d2896, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2896, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d2896, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46660 (p : Pattern) (guard : d8100 p = 1) : d2897 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8100, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46653 p hg
    simpa only [d8100, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46661 (p : Pattern) (guard : d8106 p = 1) : d2898 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46660 p hg
    simpa only [d8106, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46662 (p : Pattern) (guard : d8107 p = 1) : d2899 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2899, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46659 p hg
    simpa only [d8107, d2899, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2899, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46661 p hg
    simpa only [d8107, d2899, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46663 (p : Pattern) (guard : d8112 p = 1) : d2903 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46456 p hg
    simpa only [d8112, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46664 (p : Pattern) (guard : d8113 p = 1) : d2904 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2904, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46662 p hg
    simpa only [d8113, d2904, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2904, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46663 p hg
    simpa only [d8113, d2904, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46665 (p : Pattern) (guard : d8114 p = 1) : d2905 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2905, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46657 p hg
    simpa only [d8114, d2905, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2905, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d8114, d2905, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46666 (p : Pattern) (guard : d8101 p = 1) : d2907 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2907, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46561 p hg
    simpa only [d8101, d2907, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2907, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d2907, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46667 (p : Pattern) (guard : d8100 p = 1) : d2906 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8100, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38955 p hg
    simpa only [d8100, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46668 (p : Pattern) (guard : d8106 p = 1) : d2908 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46667 p hg
    simpa only [d8106, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46669 (p : Pattern) (guard : d8107 p = 1) : d2909 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2909, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d8107, d2909, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2909, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46668 p hg
    simpa only [d8107, d2909, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46670 (p : Pattern) (guard : d8106 p = 1) : d2910 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46667 p hg
    simpa only [d8106, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46671 (p : Pattern) (guard : d8105 p = 1) : d2911 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8105, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23897 p hg
    simpa only [d8105, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46672 (p : Pattern) (guard : d8111 p = 1) : d2912 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46671 p hg
    simpa only [d8111, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46673 (p : Pattern) (guard : d8112 p = 1) : d2913 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46670 p hg
    simpa only [d8112, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d8112, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46674 (p : Pattern) (guard : d8113 p = 1) : d2914 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2914, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d8113, d2914, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2914, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46673 p hg
    simpa only [d8113, d2914, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46675 (p : Pattern) (guard : d8106 p = 1) : d2915 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46667 p hg
    simpa only [d8106, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46676 (p : Pattern) (guard : d8112 p = 1) : d2916 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46675 p hg
    simpa only [d8112, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d8112, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46677 (p : Pattern) (guard : d8117 p = 1) : d2918 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46468 p hg
    simpa only [d8117, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46678 (p : Pattern) (guard : d8118 p = 1) : d2919 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46676 p hg
    simpa only [d8118, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d8118, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46679 (p : Pattern) (guard : d8119 p = 1) : d2920 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2920, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46674 p hg
    simpa only [d8119, d2920, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2920, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46678 p hg
    simpa only [d8119, d2920, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46680 (p : Pattern) (guard : d8120 p = 1) : d2921 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2921, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46665 p hg
    simpa only [d8120, d2921, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2921, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46679 p hg
    simpa only [d8120, d2921, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46681 (p : Pattern) (guard : d8095 p = 1) : d2895 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d8095, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38945 p hg
    simpa only [d8095, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46682 (p : Pattern) (guard : d8101 p = 1) : d2896 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d8101, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46683 (p : Pattern) (guard : d5854 p = 1) : d2029 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d5854, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17478 p hg
    simpa only [d5854, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46684 (p : Pattern) (guard : d8099 p = 1) : d2030 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46683 p hg
    simpa only [d8099, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17478 p hg
    simpa only [d8099, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46685 (p : Pattern) (guard : d8100 p = 1) : d2922 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2922, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34882 p hg
    simpa only [d8100, d2922, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2922, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46684 p hg
    simpa only [d8100, d2922, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46686 (p : Pattern) (guard : d8106 p = 1) : d2923 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2923, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46685 p hg
    simpa only [d8106, d2923, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2923, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38920 p hg
    simpa only [d8106, d2923, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46687 (p : Pattern) (guard : d8107 p = 1) : d2924 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2924, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46682 p hg
    simpa only [d8107, d2924, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2924, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46686 p hg
    simpa only [d8107, d2924, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46688 (p : Pattern) (guard : d8100 p = 1) : d2897 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d8100, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46653 p hg
    simpa only [d8100, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46689 (p : Pattern) (guard : d8106 p = 1) : d2898 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46688 p hg
    simpa only [d8106, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46690 (p : Pattern) (guard : d8111 p = 1) : d2902 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46467 p hg
    simpa only [d8111, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15276 p hg
    simpa only [d8111, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46691 (p : Pattern) (guard : d8112 p = 1) : d2925 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2925, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46689 p hg
    simpa only [d8112, d2925, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2925, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46690 p hg
    simpa only [d8112, d2925, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46692 (p : Pattern) (guard : d8113 p = 1) : d2926 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2926, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46687 p hg
    simpa only [d8113, d2926, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2926, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46691 p hg
    simpa only [d8113, d2926, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46693 (p : Pattern) (guard : d8112 p = 1) : d2929 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2929, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46655 p hg
    simpa only [d8112, d2929, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2929, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46512 p hg
    simpa only [d8112, d2929, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46694 (p : Pattern) (guard : d8118 p = 1) : d2933 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2933, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46693 p hg
    simpa only [d8118, d2933, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2933, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2933, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46695 (p : Pattern) (guard : d8119 p = 1) : d2934 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2934, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46692 p hg
    simpa only [d8119, d2934, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2934, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46694 p hg
    simpa only [d8119, d2934, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46696 (p : Pattern) (guard : d8105 p = 1) : d2935 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8105, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23928 p hg
    simpa only [d8105, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46697 (p : Pattern) (guard : d8111 p = 1) : d2936 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46696 p hg
    simpa only [d8111, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46698 (p : Pattern) (guard : d8112 p = 1) : d2937 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46668 p hg
    simpa only [d8112, d2937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46697 p hg
    simpa only [d8112, d2937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46699 (p : Pattern) (guard : d0 p = 1) : d2917 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46700 (p : Pattern) (guard : d8117 p = 1) : d2938 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d8117, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46699 p hg
    simpa only [d8117, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46701 (p : Pattern) (guard : d8118 p = 1) : d2939 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46698 p hg
    simpa only [d8118, d2939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46700 p hg
    simpa only [d8118, d2939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46702 (p : Pattern) (guard : d0 p = 1) : d2940 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46703 (p : Pattern) (guard : d8117 p = 1) : d2941 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d8117, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46702 p hg
    simpa only [d8117, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46704 (p : Pattern) (guard : d0 p = 1) : d2943 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46705 (p : Pattern) (guard : d8123 p = 1) : d2944 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46703 p hg
    simpa only [d8123, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46704 p hg
    simpa only [d8123, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46706 (p : Pattern) (guard : d8124 p = 1) : d2945 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46701 p hg
    simpa only [d8124, d2945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d8124, d2945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46707 (p : Pattern) (guard : d8125 p = 1) : d2946 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2946, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46695 p hg
    simpa only [d8125, d2946, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2946, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d8125, d2946, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46708 (p : Pattern) (guard : d8126 p = 1) : d2947 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2947, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46680 p hg
    simpa only [d8126, d2947, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2947, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d8126, d2947, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46709 (p : Pattern) (guard : d5854 p = 1) : d2047 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d5854, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17207 p hg
    simpa only [d5854, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46710 (p : Pattern) (guard : d8094 p = 1) : d2048 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38708 p hg
    simpa only [d8094, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d8094, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46711 (p : Pattern) (guard : d8095 p = 1) : d2948 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2948, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34811 p hg
    simpa only [d8095, d2948, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2948, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d8095, d2948, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46712 (p : Pattern) (guard : d8101 p = 1) : d2949 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2949, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46711 p hg
    simpa only [d8101, d2949, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2949, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d2949, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46713 (p : Pattern) (guard : d0 p = 1) : d2053 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46714 (p : Pattern) (guard : d8099 p = 1) : d2054 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38948 p hg
    simpa only [d8099, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46713 p hg
    simpa only [d8099, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46715 (p : Pattern) (guard : d8100 p = 1) : d2950 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8100, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46714 p hg
    simpa only [d8100, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46716 (p : Pattern) (guard : d8106 p = 1) : d2951 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46715 p hg
    simpa only [d8106, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46717 (p : Pattern) (guard : d8107 p = 1) : d2952 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2952, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46712 p hg
    simpa only [d8107, d2952, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2952, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46716 p hg
    simpa only [d8107, d2952, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46718 (p : Pattern) (guard : d8106 p = 1) : d2953 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46667 p hg
    simpa only [d8106, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46719 (p : Pattern) (guard : d8111 p = 1) : d2954 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46671 p hg
    simpa only [d8111, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15333 p hg
    simpa only [d8111, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46720 (p : Pattern) (guard : d8112 p = 1) : d2955 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46718 p hg
    simpa only [d8112, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46719 p hg
    simpa only [d8112, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46721 (p : Pattern) (guard : d8113 p = 1) : d2956 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2956, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46717 p hg
    simpa only [d8113, d2956, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2956, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46720 p hg
    simpa only [d8113, d2956, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46722 (p : Pattern) (guard : d8117 p = 1) : d2958 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46509 p hg
    simpa only [d8117, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46723 (p : Pattern) (guard : d8118 p = 1) : d2959 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46720 p hg
    simpa only [d8118, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46722 p hg
    simpa only [d8118, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46724 (p : Pattern) (guard : d8119 p = 1) : d2960 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2960, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46721 p hg
    simpa only [d8119, d2960, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2960, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46723 p hg
    simpa only [d8119, d2960, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46725 (p : Pattern) (guard : d8105 p = 1) : d2962 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34709 p hg
    simpa only [d8105, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23958 p hg
    simpa only [d8105, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46726 (p : Pattern) (guard : d8111 p = 1) : d2963 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d8111, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d8111, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46727 (p : Pattern) (guard : d8112 p = 1) : d2964 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46507 p hg
    simpa only [d8112, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46726 p hg
    simpa only [d8112, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46728 (p : Pattern) (guard : d8118 p = 1) : d2965 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46727 p hg
    simpa only [d8118, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46729 (p : Pattern) (guard : d8124 p = 1) : d2966 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46728 p hg
    simpa only [d8124, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46730 (p : Pattern) (guard : d8125 p = 1) : d2967 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2967, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46724 p hg
    simpa only [d8125, d2967, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2967, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d8125, d2967, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46731 (p : Pattern) (guard : d8100 p = 1) : d2950 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34925 p hg
    simpa only [d8100, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46714 p hg
    simpa only [d8100, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46732 (p : Pattern) (guard : d8106 p = 1) : d2951 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46731 p hg
    simpa only [d8106, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46733 (p : Pattern) (guard : d8111 p = 1) : d2961 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46696 p hg
    simpa only [d8111, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d8111, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46734 (p : Pattern) (guard : d8112 p = 1) : d2968 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2968, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46732 p hg
    simpa only [d8112, d2968, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2968, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46733 p hg
    simpa only [d8112, d2968, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46735 (p : Pattern) (guard : d0 p = 1) : d2957 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46736 (p : Pattern) (guard : d8117 p = 1) : d2969 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46719 p hg
    simpa only [d8117, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46735 p hg
    simpa only [d8117, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46737 (p : Pattern) (guard : d8118 p = 1) : d2970 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2970, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46734 p hg
    simpa only [d8118, d2970, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2970, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46736 p hg
    simpa only [d8118, d2970, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46738 (p : Pattern) (guard : d0 p = 1) : d2928 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46739 (p : Pattern) (guard : d8117 p = 1) : d2971 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46719 p hg
    simpa only [d8117, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46738 p hg
    simpa only [d8117, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46740 (p : Pattern) (guard : d0 p = 1) : d2932 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46741 (p : Pattern) (guard : d8123 p = 1) : d2972 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46739 p hg
    simpa only [d8123, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46740 p hg
    simpa only [d8123, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46742 (p : Pattern) (guard : d8124 p = 1) : d2973 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2973, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d8124, d2973, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2973, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d8124, d2973, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46743 (p : Pattern) (guard : d8117 p = 1) : d2974 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46726 p hg
    simpa only [d8117, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46744 (p : Pattern) (guard : d8123 p = 1) : d2975 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46743 p hg
    simpa only [d8123, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46745 (p : Pattern) (guard : d8129 p = 1) : d2976 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46744 p hg
    simpa only [d8129, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46746 (p : Pattern) (guard : d8130 p = 1) : d2977 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2977, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46742 p hg
    simpa only [d8130, d2977, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2977, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46745 p hg
    simpa only [d8130, d2977, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46747 (p : Pattern) (guard : d8131 p = 1) : d2978 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2978, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46730 p hg
    simpa only [d8131, d2978, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2978, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46746 p hg
    simpa only [d8131, d2978, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46748 (p : Pattern) (guard : d8132 p = 1) : d2979 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2979, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d8132, d2979, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2979, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46747 p hg
    simpa only [d8132, d2979, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46749 (p : Pattern) (guard : d8095 p = 1) : d2948 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34828 p hg
    simpa only [d8095, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d8095, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46750 (p : Pattern) (guard : d8101 p = 1) : d2949 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46749 p hg
    simpa only [d8101, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46751 (p : Pattern) (guard : d8107 p = 1) : d2952 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46750 p hg
    simpa only [d8107, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46732 p hg
    simpa only [d8107, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46752 (p : Pattern) (guard : d8113 p = 1) : d2956 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46751 p hg
    simpa only [d8113, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46720 p hg
    simpa only [d8113, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46753 (p : Pattern) (guard : d8119 p = 1) : d2960 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46752 p hg
    simpa only [d8119, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46723 p hg
    simpa only [d8119, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46754 (p : Pattern) (guard : d8125 p = 1) : d2967 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46753 p hg
    simpa only [d8125, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d8125, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46755 (p : Pattern) (guard : d8100 p = 1) : d2950 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35071 p hg
    simpa only [d8100, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46714 p hg
    simpa only [d8100, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46756 (p : Pattern) (guard : d8106 p = 1) : d2951 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46755 p hg
    simpa only [d8106, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46757 (p : Pattern) (guard : d8112 p = 1) : d2968 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46756 p hg
    simpa only [d8112, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46733 p hg
    simpa only [d8112, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46758 (p : Pattern) (guard : d8118 p = 1) : d2970 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46757 p hg
    simpa only [d8118, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46736 p hg
    simpa only [d8118, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46759 (p : Pattern) (guard : d8124 p = 1) : d2973 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46758 p hg
    simpa only [d8124, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d8124, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
