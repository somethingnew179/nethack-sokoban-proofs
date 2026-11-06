/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons165
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23240 (p : Pattern) (guard : d5503 p = 1) : d2775 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2775, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23239 p hg
    simpa only [d2775, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2775, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2775, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23241 (p : Pattern) (guard : d5503 p = 1) : d2776 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2776, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23235 p hg
    simpa only [d2776, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2776, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23240 p hg
    simpa only [d2776, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23242 (p : Pattern) (guard : d5503 p = 1) : d2777 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2777, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23236 p hg
    simpa only [d2777, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2777, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23241 p hg
    simpa only [d2777, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23243 (p : Pattern) (guard : d5503 p = 1) : d2778 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2778, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23150 p hg
    simpa only [d2778, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2778, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23161 p hg
    simpa only [d2778, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23244 (p : Pattern) (guard : d5503 p = 1) : d2779 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2779, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23243 p hg
    simpa only [d2779, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2779, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23164 p hg
    simpa only [d2779, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23245 (p : Pattern) (guard : d5503 p = 1) : d2780 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2780, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23244 p hg
    simpa only [d2780, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2780, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23181 p hg
    simpa only [d2780, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23246 (p : Pattern) (guard : d5503 p = 1) : d2781 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2781, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23150 p hg
    simpa only [d2781, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2781, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23192 p hg
    simpa only [d2781, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23247 (p : Pattern) (guard : d5503 p = 1) : d2782 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2782, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23246 p hg
    simpa only [d2782, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2782, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23194 p hg
    simpa only [d2782, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23248 (p : Pattern) (guard : d5503 p = 1) : d2783 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2783, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23247 p hg
    simpa only [d2783, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2783, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23197 p hg
    simpa only [d2783, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23249 (p : Pattern) (guard : d5503 p = 1) : d2784 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2784, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23248 p hg
    simpa only [d2784, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2784, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23205 p hg
    simpa only [d2784, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23250 (p : Pattern) (guard : d5503 p = 1) : d2785 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2785, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23245 p hg
    simpa only [d2785, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2785, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23249 p hg
    simpa only [d2785, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23251 (p : Pattern) (guard : d5503 p = 1) : d2786 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2786, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23250 p hg
    simpa only [d2786, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2786, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23235 p hg
    simpa only [d2786, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23252 (p : Pattern) (guard : d5503 p = 1) : d2787 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2787, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23235 p hg
    simpa only [d2787, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2787, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2787, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23253 (p : Pattern) (guard : d5503 p = 1) : d2788 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2788, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23251 p hg
    simpa only [d2788, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2788, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23252 p hg
    simpa only [d2788, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23254 (p : Pattern) (guard : d5503 p = 1) : d2789 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2789, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23242 p hg
    simpa only [d2789, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2789, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23253 p hg
    simpa only [d2789, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23255 (p : Pattern) (guard : d5503 p = 1) : d2790 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2790, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23116 p hg
    simpa only [d2790, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2790, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23254 p hg
    simpa only [d2790, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23256 (p : Pattern) (guard : d5503 p = 1) : d2791 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2791, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23138 p hg
    simpa only [d2791, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2791, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23255 p hg
    simpa only [d2791, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23257 (p : Pattern) (guard : d5503 p = 1) : d2792 p ≤ (0 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2792, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23027 p hg
    simpa only [d2792, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2792, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23005 p hg
    simpa only [d2792, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23258 (p : Pattern) (guard : d5503 p = 1) : d2793 p ≤ (0 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2793, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23073 p hg
    simpa only [d2793, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2793, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23257 p hg
    simpa only [d2793, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23259 (p : Pattern) (guard : d5503 p = 1) : d2794 p ≤ (0 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2794, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23027 p hg
    simpa only [d2794, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2794, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23010 p hg
    simpa only [d2794, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23260 (p : Pattern) (guard : d5503 p = 1) : d2795 p ≤ (0 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2795, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23076 p hg
    simpa only [d2795, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2795, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2795, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23261 (p : Pattern) (guard : d5503 p = 1) : d2796 p ≤ (0 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2796, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23259 p hg
    simpa only [d2796, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2796, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23260 p hg
    simpa only [d2796, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23262 (p : Pattern) (guard : d5503 p = 1) : d2797 p ≤ (0 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2797, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23258 p hg
    simpa only [d2797, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2797, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23261 p hg
    simpa only [d2797, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23263 (p : Pattern) (guard : d5503 p = 1) : d2798 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2798, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23050 p hg
    simpa only [d2798, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2798, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23260 p hg
    simpa only [d2798, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23264 (p : Pattern) (guard : d5503 p = 1) : d2799 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2799, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23263 p hg
    simpa only [d2799, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2799, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23057 p hg
    simpa only [d2799, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23265 (p : Pattern) (guard : d5503 p = 1) : d2800 p ≤ (0 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2800, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23262 p hg
    simpa only [d2800, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2800, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23264 p hg
    simpa only [d2800, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23266 (p : Pattern) (guard : d5503 p = 1) : d2801 p ≤ (0 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2801, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23072 p hg
    simpa only [d2801, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2801, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23265 p hg
    simpa only [d2801, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23267 (p : Pattern) (guard : d5503 p = 1) : d2802 p ≤ (0 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2802, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23257 p hg
    simpa only [d2802, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2802, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23012 p hg
    simpa only [d2802, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23268 (p : Pattern) (guard : d5503 p = 1) : d2803 p ≤ (0 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2803, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23260 p hg
    simpa only [d2803, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2803, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23056 p hg
    simpa only [d2803, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23269 (p : Pattern) (guard : d5503 p = 1) : d2804 p ≤ (0 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2804, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23267 p hg
    simpa only [d2804, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2804, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23268 p hg
    simpa only [d2804, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23270 (p : Pattern) (guard : d5503 p = 1) : d2805 p ≤ (0 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2805, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23260 p hg
    simpa only [d2805, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2805, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2805, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23271 (p : Pattern) (guard : d5503 p = 1) : d2806 p ≤ (0 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2806, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23270 p hg
    simpa only [d2806, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2806, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2806, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23272 (p : Pattern) (guard : d5503 p = 1) : d2807 p ≤ (0 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2807, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23269 p hg
    simpa only [d2807, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2807, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23271 p hg
    simpa only [d2807, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23273 (p : Pattern) (guard : d5503 p = 1) : d2808 p ≤ (0 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2808, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23087 p hg
    simpa only [d2808, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2808, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23272 p hg
    simpa only [d2808, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23274 (p : Pattern) (guard : d5503 p = 1) : d2809 p ≤ (0 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2809, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23266 p hg
    simpa only [d2809, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2809, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23273 p hg
    simpa only [d2809, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23275 (p : Pattern) (guard : d5503 p = 1) : d2810 p ≤ (0 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2810, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23063 p hg
    simpa only [d2810, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2810, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23078 p hg
    simpa only [d2810, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23276 (p : Pattern) (guard : d5503 p = 1) : d2811 p ≤ (0 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2811, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23275 p hg
    simpa only [d2811, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2811, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23079 p hg
    simpa only [d2811, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23277 (p : Pattern) (guard : d0 p = 1) : d2812 p ≤ (0 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23278 (p : Pattern) (guard : d5503 p = 1) : d2812 p ≤ (0 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21511 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23277 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23279 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23280 (p : Pattern) (guard : d5503 p = 1) : d2813 p ≤ (0 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21511 p hg
    simpa only [d5503, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23279 p hg
    simpa only [d5503, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23281 (p : Pattern) (guard : d5503 p = 1) : d2814 p ≤ (0 : Int) + d191 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23278 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23280 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23282 (p : Pattern) (guard : d5503 p = 1) : d2815 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2815, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23280 p hg
    simpa only [d2815, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2815, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2815, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23283 (p : Pattern) (guard : d5503 p = 1) : d2816 p ≤ (0 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2816, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23281 p hg
    simpa only [d2816, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2816, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23282 p hg
    simpa only [d2816, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23284 (p : Pattern) (guard : d5503 p = 1) : d2817 p ≤ (0 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2817, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23065 p hg
    simpa only [d2817, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2817, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d2817, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23285 (p : Pattern) (guard : d5503 p = 1) : d2818 p ≤ (0 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2818, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d2818, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2818, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2818, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23286 (p : Pattern) (guard : d5503 p = 1) : d2819 p ≤ (0 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2819, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d2819, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2819, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2819, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23287 (p : Pattern) (guard : d5503 p = 1) : d2820 p ≤ (0 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2820, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23276 p hg
    simpa only [d2820, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2820, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d2820, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23288 (p : Pattern) (guard : d5503 p = 1) : d2821 p ≤ (0 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2821, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23065 p hg
    simpa only [d2821, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2821, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23046 p hg
    simpa only [d2821, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23289 (p : Pattern) (guard : d5503 p = 1) : d2822 p ≤ (0 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2822, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23073 p hg
    simpa only [d2822, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2822, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23288 p hg
    simpa only [d2822, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23290 (p : Pattern) (guard : d5503 p = 1) : d2823 p ≤ (0 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2823, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23289 p hg
    simpa only [d2823, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2823, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23089 p hg
    simpa only [d2823, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23291 (p : Pattern) (guard : d5503 p = 1) : d2824 p ≤ (0 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2824, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d2824, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2824, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2824, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23292 (p : Pattern) (guard : d5503 p = 1) : d2825 p ≤ (0 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2825, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23291 p hg
    simpa only [d2825, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2825, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2825, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23293 (p : Pattern) (guard : d5503 p = 1) : d2826 p ≤ (0 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2826, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23292 p hg
    simpa only [d2826, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2826, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2826, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23294 (p : Pattern) (guard : d5503 p = 1) : d2827 p ≤ (0 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2827, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d2827, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2827, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23293 p hg
    simpa only [d2827, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23295 (p : Pattern) (guard : d5503 p = 1) : d2828 p ≤ (0 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2828, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d2828, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2828, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23294 p hg
    simpa only [d2828, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23296 (p : Pattern) (guard : d5503 p = 1) : d2829 p ≤ (0 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2829, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23274 p hg
    simpa only [d2829, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2829, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23295 p hg
    simpa only [d2829, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23297 (p : Pattern) (guard : d5503 p = 1) : d2830 p ≤ (0 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2830, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23295 p hg
    simpa only [d2830, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2830, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2830, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23298 (p : Pattern) (guard : d5503 p = 1) : d2831 p ≤ (0 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2831, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23296 p hg
    simpa only [d2831, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2831, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23297 p hg
    simpa only [d2831, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23299 (p : Pattern) (guard : d5503 p = 1) : d2832 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2832, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23130 p hg
    simpa only [d2832, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2832, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23298 p hg
    simpa only [d2832, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23300 (p : Pattern) (guard : d5503 p = 1) : d2833 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2833, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23116 p hg
    simpa only [d2833, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2833, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d2833, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23301 (p : Pattern) (guard : d5503 p = 1) : d2834 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2834, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23160 p hg
    simpa only [d2834, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2834, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2834, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23302 (p : Pattern) (guard : d5503 p = 1) : d2835 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2835, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23193 p hg
    simpa only [d2835, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2835, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23301 p hg
    simpa only [d2835, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23303 (p : Pattern) (guard : d5503 p = 1) : d2836 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2836, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23301 p hg
    simpa only [d2836, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2836, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2836, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23304 (p : Pattern) (guard : d5503 p = 1) : d2837 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2837, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23302 p hg
    simpa only [d2837, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2837, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d2837, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23305 (p : Pattern) (guard : d5503 p = 1) : d2838 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2838, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23176 p hg
    simpa only [d2838, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2838, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2838, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23306 (p : Pattern) (guard : d5503 p = 1) : d2839 p ≤ (0 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2839, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23200 p hg
    simpa only [d2839, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2839, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23305 p hg
    simpa only [d2839, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23307 (p : Pattern) (guard : d5503 p = 1) : d2840 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2840, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23305 p hg
    simpa only [d2840, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2840, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2840, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23308 (p : Pattern) (guard : d5503 p = 1) : d2841 p ≤ (0 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2841, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23306 p hg
    simpa only [d2841, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2841, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23307 p hg
    simpa only [d2841, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23309 (p : Pattern) (guard : d5503 p = 1) : d2842 p ≤ (0 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2842, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23304 p hg
    simpa only [d2842, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2842, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23308 p hg
    simpa only [d2842, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23310 (p : Pattern) (guard : d5503 p = 1) : d2843 p ≤ (0 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2843, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23182 p hg
    simpa only [d2843, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2843, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23309 p hg
    simpa only [d2843, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23311 (p : Pattern) (guard : d5503 p = 1) : d2844 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2844, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23211 p hg
    simpa only [d2844, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2844, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2844, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23312 (p : Pattern) (guard : d5503 p = 1) : d2845 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2845, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23225 p hg
    simpa only [d2845, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2845, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23311 p hg
    simpa only [d2845, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23313 (p : Pattern) (guard : d5503 p = 1) : d2846 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2846, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23311 p hg
    simpa only [d2846, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2846, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2846, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23314 (p : Pattern) (guard : d5503 p = 1) : d2847 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2847, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23312 p hg
    simpa only [d2847, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2847, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23313 p hg
    simpa only [d2847, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23315 (p : Pattern) (guard : d5503 p = 1) : d2848 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2848, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23314 p hg
    simpa only [d2848, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2848, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23233 p hg
    simpa only [d2848, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23316 (p : Pattern) (guard : d5503 p = 1) : d2849 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2849, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23224 p hg
    simpa only [d2849, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2849, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23315 p hg
    simpa only [d2849, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23317 (p : Pattern) (guard : d5503 p = 1) : d2850 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2850, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23310 p hg
    simpa only [d2850, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2850, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d2850, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23318 (p : Pattern) (guard : d5503 p = 1) : d2851 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2851, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d2851, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2851, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23240 p hg
    simpa only [d2851, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23319 (p : Pattern) (guard : d5503 p = 1) : d2852 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2852, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23317 p hg
    simpa only [d2852, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2852, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23318 p hg
    simpa only [d2852, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23320 (p : Pattern) (guard : d5503 p = 1) : d2853 p ≤ (0 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2853, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23188 p hg
    simpa only [d2853, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2853, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23172 p hg
    simpa only [d2853, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23321 (p : Pattern) (guard : d5503 p = 1) : d2854 p ≤ (0 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2854, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23216 p hg
    simpa only [d2854, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2854, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23320 p hg
    simpa only [d2854, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23322 (p : Pattern) (guard : d5503 p = 1) : d2855 p ≤ (0 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2855, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23321 p hg
    simpa only [d2855, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2855, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23305 p hg
    simpa only [d2855, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23323 (p : Pattern) (guard : d5503 p = 1) : d2856 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2856, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23219 p hg
    simpa only [d2856, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2856, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2856, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23324 (p : Pattern) (guard : d5503 p = 1) : d2857 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2857, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23323 p hg
    simpa only [d2857, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2857, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2857, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23325 (p : Pattern) (guard : d5503 p = 1) : d2858 p ≤ (0 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2858, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23324 p hg
    simpa only [d2858, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2858, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2858, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23326 (p : Pattern) (guard : d5503 p = 1) : d2859 p ≤ (0 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2859, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23322 p hg
    simpa only [d2859, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2859, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23325 p hg
    simpa only [d2859, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23327 (p : Pattern) (guard : d5503 p = 1) : d2860 p ≤ (0 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2860, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23215 p hg
    simpa only [d2860, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2860, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23326 p hg
    simpa only [d2860, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23328 (p : Pattern) (guard : d5503 p = 1) : d2861 p ≤ (0 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2861, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23156 p hg
    simpa only [d2861, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2861, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23172 p hg
    simpa only [d2861, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23329 (p : Pattern) (guard : d5503 p = 1) : d2862 p ≤ (0 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2862, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23328 p hg
    simpa only [d2862, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2862, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23176 p hg
    simpa only [d2862, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23330 (p : Pattern) (guard : d5503 p = 1) : d2863 p ≤ (0 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2863, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23329 p hg
    simpa only [d2863, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2863, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23324 p hg
    simpa only [d2863, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23331 (p : Pattern) (guard : d5503 p = 1) : d2864 p ≤ (0 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2864, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23018 p hg
    simpa only [d2864, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2864, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2864, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23332 (p : Pattern) (guard : d5503 p = 1) : d2865 p ≤ (0 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2865, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23330 p hg
    simpa only [d2865, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2865, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23331 p hg
    simpa only [d2865, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23333 (p : Pattern) (guard : d5503 p = 1) : d2866 p ≤ (0 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2866, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23314 p hg
    simpa only [d2866, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2866, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23332 p hg
    simpa only [d2866, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23334 (p : Pattern) (guard : d5503 p = 1) : d2867 p ≤ (0 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2867, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23327 p hg
    simpa only [d2867, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2867, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23333 p hg
    simpa only [d2867, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23335 (p : Pattern) (guard : d5503 p = 1) : d2868 p ≤ (0 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2868, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23216 p hg
    simpa only [d2868, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2868, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23046 p hg
    simpa only [d2868, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23336 (p : Pattern) (guard : d5503 p = 1) : d2869 p ≤ (0 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2869, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23209 p hg
    simpa only [d2869, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2869, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23335 p hg
    simpa only [d2869, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23337 (p : Pattern) (guard : d5503 p = 1) : d2870 p ≤ (0 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2870, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23336 p hg
    simpa only [d2870, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2870, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23229 p hg
    simpa only [d2870, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23338 (p : Pattern) (guard : d5503 p = 1) : d2871 p ≤ (0 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2871, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23337 p hg
    simpa only [d2871, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2871, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23233 p hg
    simpa only [d2871, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23339 (p : Pattern) (guard : d5503 p = 1) : d2872 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2872, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23216 p hg
    simpa only [d2872, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2872, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23311 p hg
    simpa only [d2872, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23340 (p : Pattern) (guard : d5503 p = 1) : d2873 p ≤ (0 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2873, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23339 p hg
    simpa only [d2873, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2873, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23232 p hg
    simpa only [d2873, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23341 (p : Pattern) (guard : d5503 p = 1) : d2874 p ≤ (0 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2874, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23070 p hg
    simpa only [d2874, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2874, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2874, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23342 (p : Pattern) (guard : d5503 p = 1) : d2875 p ≤ (0 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2875, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23341 p hg
    simpa only [d2875, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2875, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2875, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23343 (p : Pattern) (guard : d5503 p = 1) : d2876 p ≤ (0 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2876, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23340 p hg
    simpa only [d2876, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2876, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23342 p hg
    simpa only [d2876, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23344 (p : Pattern) (guard : d5503 p = 1) : d2877 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2877, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23338 p hg
    simpa only [d2877, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2877, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23343 p hg
    simpa only [d2877, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23345 (p : Pattern) (guard : d5503 p = 1) : d2878 p ≤ (0 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2878, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23334 p hg
    simpa only [d2878, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2878, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23344 p hg
    simpa only [d2878, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23346 (p : Pattern) (guard : d5503 p = 1) : d2879 p ≤ (0 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2879, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23216 p hg
    simpa only [d2879, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2879, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23069 p hg
    simpa only [d2879, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23347 (p : Pattern) (guard : d5503 p = 1) : d2880 p ≤ (0 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2880, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23209 p hg
    simpa only [d2880, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2880, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d2880, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23348 (p : Pattern) (guard : d5503 p = 1) : d2881 p ≤ (0 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2881, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23211 p hg
    simpa only [d2881, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2881, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23069 p hg
    simpa only [d2881, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23349 (p : Pattern) (guard : d5503 p = 1) : d2882 p ≤ (0 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2882, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23348 p hg
    simpa only [d2882, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2882, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2882, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23350 (p : Pattern) (guard : d5503 p = 1) : d2883 p ≤ (0 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2883, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23347 p hg
    simpa only [d2883, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2883, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23349 p hg
    simpa only [d2883, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23351 (p : Pattern) (guard : d5503 p = 1) : d2884 p ≤ (0 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2884, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23220 p hg
    simpa only [d2884, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2884, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23046 p hg
    simpa only [d2884, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23352 (p : Pattern) (guard : d5503 p = 1) : d2885 p ≤ (0 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2885, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23351 p hg
    simpa only [d2885, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2885, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2885, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23353 (p : Pattern) (guard : d5503 p = 1) : d2886 p ≤ (0 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2886, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23352 p hg
    simpa only [d2886, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2886, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2886, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23354 (p : Pattern) (guard : d5503 p = 1) : d2887 p ≤ (0 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2887, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d2887, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2887, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23353 p hg
    simpa only [d2887, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23355 (p : Pattern) (guard : d5503 p = 1) : d2888 p ≤ (0 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2888, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23354 p hg
    simpa only [d2888, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2888, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23343 p hg
    simpa only [d2888, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23356 (p : Pattern) (guard : d5503 p = 1) : d2889 p ≤ (0 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2889, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23355 p hg
    simpa only [d2889, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2889, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2889, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23357 (p : Pattern) (guard : d5503 p = 1) : d2890 p ≤ (0 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2890, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d2890, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2890, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23356 p hg
    simpa only [d2890, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23358 (p : Pattern) (guard : d5503 p = 1) : d2891 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2891, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d2891, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2891, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23357 p hg
    simpa only [d2891, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23359 (p : Pattern) (guard : d5503 p = 1) : d2892 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2892, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23116 p hg
    simpa only [d2892, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2892, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23358 p hg
    simpa only [d2892, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23360 (p : Pattern) (guard : d5503 p = 1) : d2893 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2893, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23300 p hg
    simpa only [d2893, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2893, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d2893, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23361 (p : Pattern) (guard : d5503 p = 1) : d2894 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2894, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23256 p hg
    simpa only [d2894, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2894, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23360 p hg
    simpa only [d2894, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23362 (p : Pattern) (guard : d0 p = 1) : d315 p ≤ (0 : Int) + d3226 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23363 (p : Pattern) (guard : d5851 p = 1) : d2503 p ≤ (0 : Int) + d3227 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2503, d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17643 p hg
    simpa only [d5851, d2503, d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2503, d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23362 p hg
    simpa only [d5851, d2503, d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23364 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare23365 (p : Pattern) (guard : d5847 p = 1) : d14 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23364 p hg
    simpa only [d5847, d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, d14, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23366 (p : Pattern) (guard : d5854 p = 1) : d2504 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23365 p hg
    simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18633 p hg
    simpa only [d5854, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23367 (p : Pattern) (guard : d5855 p = 1) : d2505 p ≤ (0 : Int) + d3228 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2505, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23363 p hg
    simpa only [d5855, d2505, d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2505, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23366 p hg
    simpa only [d5855, d2505, d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23368 (p : Pattern) (guard : d5851 p = 1) : d2504 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d5851, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18633 p hg
    simpa only [d5851, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23369 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23370 (p : Pattern) (guard : d5843 p = 1) : d1769 p ≤ (0 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23369 p hg
    simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23371 (p : Pattern) (guard : d5847 p = 1) : d1770 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1770, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23370 p hg
    simpa only [d5847, d1770, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1770, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d1770, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23372 (p : Pattern) (guard : d5854 p = 1) : d2506 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23371 p hg
    simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18633 p hg
    simpa only [d5854, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23373 (p : Pattern) (guard : d5855 p = 1) : d2507 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23368 p hg
    simpa only [d5855, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23372 p hg
    simpa only [d5855, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23374 (p : Pattern) (guard : d5855 p = 1) : d2508 p ≤ (0 : Int) + d3229 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2508, d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23367 p hg
    simpa only [d2508, d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2508, d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23373 p hg
    simpa only [d2508, d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23375 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23376 (p : Pattern) (guard : d5843 p = 1) : d1683 p ≤ (0 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23375 p hg
    simpa only [d5843, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23377 (p : Pattern) (guard : d5847 p = 1) : d1684 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1684, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23376 p hg
    simpa only [d5847, d1684, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1684, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d1684, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23378 (p : Pattern) (guard : d5854 p = 1) : d2509 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23377 p hg
    simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18633 p hg
    simpa only [d5854, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23379 (p : Pattern) (guard : d5855 p = 1) : d2510 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23368 p hg
    simpa only [d5855, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23378 p hg
    simpa only [d5855, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
