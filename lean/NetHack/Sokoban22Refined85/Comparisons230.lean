/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons229
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32200 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d1715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32199 p hg
    simpa only [d31, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24666 p hg
    simpa only [d31, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32201 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d1716 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32164 p hg
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32200 p hg
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32202 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d1717 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32198 p hg
    simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32201 p hg
    simpa only [d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32203 (p : Pattern) (guard : d0 p = 1) : d1717 p ≤ (2 : Int) + d1717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32204 (p : Pattern) (guard : d4474 p = 1) : d2935 p ≤ (2 : Int) + d1717 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32202 p hg
    simpa only [d4474, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32203 p hg
    simpa only [d4474, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32205 (p : Pattern) (guard : d4474 p = 1) : d2936 p ≤ (2 : Int) + d7039 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2936, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32204 p hg
    simpa only [d2936, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2936, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2936, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32206 (p : Pattern) (guard : d4474 p = 1) : d2937 p ≤ (2 : Int) + d7040 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2937, d7040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32141 p hg
    simpa only [d2937, d7040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2937, d7040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32205 p hg
    simpa only [d2937, d7040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32207 (p : Pattern) (guard : d4474 p = 1) : d2938 p ≤ (2 : Int) + d7041 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2938, d7041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32153 p hg
    simpa only [d2938, d7041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2938, d7041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32158 p hg
    simpa only [d2938, d7041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32208 (p : Pattern) (guard : d4474 p = 1) : d2939 p ≤ (2 : Int) + d7042 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2939, d7042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32206 p hg
    simpa only [d2939, d7042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2939, d7042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32207 p hg
    simpa only [d2939, d7042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32209 (p : Pattern) (guard : d4474 p = 1) : d2940 p ≤ (2 : Int) + d7033 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2940, d7033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32183 p hg
    simpa only [d2940, d7033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2940, d7033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2940, d7033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32210 (p : Pattern) (guard : d4474 p = 1) : d2941 p ≤ (2 : Int) + d7043 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2941, d7043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32153 p hg
    simpa only [d2941, d7043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2941, d7043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32209 p hg
    simpa only [d2941, d7043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32211 (p : Pattern) (guard : d4474 p = 1) : d2942 p ≤ (2 : Int) + d7035 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2942, d7035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32191 p hg
    simpa only [d2942, d7035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2942, d7035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2942, d7035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32212 (p : Pattern) (guard : d4474 p = 1) : d2943 p ≤ (2 : Int) + d7036 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2943, d7036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32211 p hg
    simpa only [d2943, d7036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2943, d7036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2943, d7036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32213 (p : Pattern) (guard : d4474 p = 1) : d2944 p ≤ (2 : Int) + d7044 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2944, d7044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32210 p hg
    simpa only [d2944, d7044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2944, d7044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32212 p hg
    simpa only [d2944, d7044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32214 (p : Pattern) (guard : d4474 p = 1) : d2945 p ≤ (2 : Int) + d7045 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2945, d7045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32208 p hg
    simpa only [d2945, d7045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2945, d7045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32213 p hg
    simpa only [d2945, d7045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32215 (p : Pattern) (guard : d4474 p = 1) : d2946 p ≤ (2 : Int) + d7046 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2946, d7046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32195 p hg
    simpa only [d2946, d7046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2946, d7046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32214 p hg
    simpa only [d2946, d7046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32216 (p : Pattern) (guard : d4474 p = 1) : d2947 p ≤ (2 : Int) + d7047 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2947, d7047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32162 p hg
    simpa only [d2947, d7047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2947, d7047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32215 p hg
    simpa only [d2947, d7047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32217 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d2047 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32090 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32132 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32218 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d2048 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32133 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32217 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32219 (p : Pattern) (guard : d0 p = 1) : d2048 p ≤ (2 : Int) + d2048 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32220 (p : Pattern) (guard : d4474 p = 1) : d2948 p ≤ (2 : Int) + d2048 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32218 p hg
    simpa only [d4474, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32219 p hg
    simpa only [d4474, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32221 (p : Pattern) (guard : d1 p = 1) : d1771 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15808 p hg
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15813 p hg
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32222 (p : Pattern) (guard : d1 p = 1) : d1772 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32221 p hg
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15813 p hg
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32223 (p : Pattern) (guard : d4474 p = 1) : d1773 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32222 p hg
    simpa only [d4474, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32224 (p : Pattern) (guard : d4474 p = 1) : d2949 p ≤ (2 : Int) + d7048 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2949, d7048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32220 p hg
    simpa only [d2949, d7048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2949, d7048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32223 p hg
    simpa only [d2949, d7048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32225 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) ≤ (2 : Int) + 10
  decide
theorem compare32226 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d2051 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32225 p hg
    simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32227 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d2052 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32226 p hg
    simpa only [d14, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4704 p hg
    simpa only [d14, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32228 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d2053 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32090 p hg
    simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32227 p hg
    simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32229 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d2054 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32133 p hg
    simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32228 p hg
    simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32230 (p : Pattern) (guard : d0 p = 1) : d2054 p ≤ (2 : Int) + d2054 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32231 (p : Pattern) (guard : d4474 p = 1) : d2950 p ≤ (2 : Int) + d2054 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32229 p hg
    simpa only [d4474, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32230 p hg
    simpa only [d4474, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32232 (p : Pattern) (guard : d1 p = 1) : d1778 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32233 (p : Pattern) (guard : d1 p = 1) : d1779 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32232 p hg
    simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12276 p hg
    simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32234 (p : Pattern) (guard : d1 p = 1) : d1780 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15813 p hg
    simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32233 p hg
    simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32235 (p : Pattern) (guard : d1 p = 1) : d1781 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15811 p hg
    simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32234 p hg
    simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32236 (p : Pattern) (guard : d4474 p = 1) : d1782 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32235 p hg
    simpa only [d4474, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32237 (p : Pattern) (guard : d4474 p = 1) : d2951 p ≤ (2 : Int) + d7049 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2951, d7049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32231 p hg
    simpa only [d2951, d7049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2951, d7049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32236 p hg
    simpa only [d2951, d7049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32238 (p : Pattern) (guard : d4474 p = 1) : d2952 p ≤ (2 : Int) + d7050 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2952, d7050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32224 p hg
    simpa only [d2952, d7050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2952, d7050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32237 p hg
    simpa only [d2952, d7050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32239 (p : Pattern) (guard : d4474 p = 1) : d2953 p ≤ (2 : Int) + d7022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2953, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d2953, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2953, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15818 p hg
    simpa only [d2953, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32240 (p : Pattern) (guard : d4474 p = 1) : d2954 p ≤ (2 : Int) + d7023 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2954, d7023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32152 p hg
    simpa only [d2954, d7023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2954, d7023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15801 p hg
    simpa only [d2954, d7023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32241 (p : Pattern) (guard : d4474 p = 1) : d2955 p ≤ (2 : Int) + d7024 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2955, d7024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32239 p hg
    simpa only [d2955, d7024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2955, d7024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32240 p hg
    simpa only [d2955, d7024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32242 (p : Pattern) (guard : d4474 p = 1) : d2956 p ≤ (2 : Int) + d7051 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2956, d7051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32238 p hg
    simpa only [d2956, d7051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2956, d7051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32241 p hg
    simpa only [d2956, d7051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32243 (p : Pattern) (guard : d4474 p = 1) : d2957 p ≤ (2 : Int) + d7018 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2957, d7018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32120 p hg
    simpa only [d2957, d7018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2957, d7018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15825 p hg
    simpa only [d2957, d7018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32244 (p : Pattern) (guard : d4474 p = 1) : d2958 p ≤ (2 : Int) + d7019 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2958, d7019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32243 p hg
    simpa only [d2958, d7019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2958, d7019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2958, d7019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32245 (p : Pattern) (guard : d4474 p = 1) : d2959 p ≤ (2 : Int) + d7026 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2959, d7026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32241 p hg
    simpa only [d2959, d7026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2959, d7026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32244 p hg
    simpa only [d2959, d7026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32246 (p : Pattern) (guard : d4474 p = 1) : d2960 p ≤ (2 : Int) + d7052 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2960, d7052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32242 p hg
    simpa only [d2960, d7052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2960, d7052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32245 p hg
    simpa only [d2960, d7052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32247 (p : Pattern) (guard : d4474 p = 1) : d2961 p ≤ (2 : Int) + d7039 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2961, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32204 p hg
    simpa only [d2961, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2961, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15841 p hg
    simpa only [d2961, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32248 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32249 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32248 p hg
    simpa only [d35, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d35, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32250 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d1720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12252 p hg
    simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32249 p hg
    simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32251 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d1721 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24654 p hg
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32252 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d1722 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32251 p hg
    simpa only [d35, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24656 p hg
    simpa only [d35, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32253 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d1723 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32252 p hg
    simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32249 p hg
    simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32254 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32250 p hg
    simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32253 p hg
    simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32255 (p : Pattern) (guard : d0 p = 1) : d1724 p ≤ (2 : Int) + d1724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32256 (p : Pattern) (guard : d4474 p = 1) : d2962 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32254 p hg
    simpa only [d4474, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32255 p hg
    simpa only [d4474, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32257 (p : Pattern) (guard : d4474 p = 1) : d2963 p ≤ (2 : Int) + d7053 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2963, d7053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32256 p hg
    simpa only [d2963, d7053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2963, d7053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16142 p hg
    simpa only [d2963, d7053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32258 (p : Pattern) (guard : d4474 p = 1) : d2964 p ≤ (2 : Int) + d7054 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2964, d7054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32247 p hg
    simpa only [d2964, d7054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2964, d7054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32257 p hg
    simpa only [d2964, d7054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32259 (p : Pattern) (guard : d4474 p = 1) : d2965 p ≤ (2 : Int) + d7055 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2965, d7055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32258 p hg
    simpa only [d2965, d7055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2965, d7055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32193 p hg
    simpa only [d2965, d7055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32260 (p : Pattern) (guard : d4474 p = 1) : d2966 p ≤ (2 : Int) + d7056 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2966, d7056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32259 p hg
    simpa only [d2966, d7056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2966, d7056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2966, d7056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32261 (p : Pattern) (guard : d4474 p = 1) : d2967 p ≤ (2 : Int) + d7057 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2967, d7057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32246 p hg
    simpa only [d2967, d7057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2967, d7057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32260 p hg
    simpa only [d2967, d7057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32262 (p : Pattern) (guard : d4474 p = 1) : d2968 p ≤ (2 : Int) + d7058 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2968, d7058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32237 p hg
    simpa only [d2968, d7058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2968, d7058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32247 p hg
    simpa only [d2968, d7058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32263 (p : Pattern) (guard : d4474 p = 1) : d2969 p ≤ (2 : Int) + d7041 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2969, d7041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32240 p hg
    simpa only [d2969, d7041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2969, d7041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32243 p hg
    simpa only [d2969, d7041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32264 (p : Pattern) (guard : d4474 p = 1) : d2970 p ≤ (2 : Int) + d7059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2970, d7059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32262 p hg
    simpa only [d2970, d7059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2970, d7059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32263 p hg
    simpa only [d2970, d7059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32265 (p : Pattern) (guard : d4474 p = 1) : d2971 p ≤ (2 : Int) + d7043 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2971, d7043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32240 p hg
    simpa only [d2971, d7043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2971, d7043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32184 p hg
    simpa only [d2971, d7043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32266 (p : Pattern) (guard : d4474 p = 1) : d2972 p ≤ (2 : Int) + d7044 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2972, d7044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32265 p hg
    simpa only [d2972, d7044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2972, d7044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32193 p hg
    simpa only [d2972, d7044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32267 (p : Pattern) (guard : d4474 p = 1) : d2973 p ≤ (2 : Int) + d7060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2973, d7060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32264 p hg
    simpa only [d2973, d7060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2973, d7060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32266 p hg
    simpa only [d2973, d7060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32268 (p : Pattern) (guard : d4474 p = 1) : d2974 p ≤ (2 : Int) + d7061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2974, d7061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32257 p hg
    simpa only [d2974, d7061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2974, d7061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2974, d7061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32269 (p : Pattern) (guard : d4474 p = 1) : d2975 p ≤ (2 : Int) + d7062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2975, d7062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32268 p hg
    simpa only [d2975, d7062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2975, d7062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2975, d7062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32270 (p : Pattern) (guard : d4474 p = 1) : d2976 p ≤ (2 : Int) + d7063 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2976, d7063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32269 p hg
    simpa only [d2976, d7063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2976, d7063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2976, d7063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32271 (p : Pattern) (guard : d4474 p = 1) : d2977 p ≤ (2 : Int) + d7064 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2977, d7064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32267 p hg
    simpa only [d2977, d7064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2977, d7064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32270 p hg
    simpa only [d2977, d7064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32272 (p : Pattern) (guard : d4474 p = 1) : d2978 p ≤ (2 : Int) + d7065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2978, d7065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32261 p hg
    simpa only [d2978, d7065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2978, d7065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32271 p hg
    simpa only [d2978, d7065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32273 (p : Pattern) (guard : d4474 p = 1) : d2979 p ≤ (2 : Int) + d7066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2979, d7066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32216 p hg
    simpa only [d2979, d7066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2979, d7066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32272 p hg
    simpa only [d2979, d7066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32274 (p : Pattern) (guard : d4474 p = 1) : d2980 p ≤ (2 : Int) + d7067 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2980, d7067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32243 p hg
    simpa only [d2980, d7067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2980, d7067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32192 p hg
    simpa only [d2980, d7067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32275 (p : Pattern) (guard : d4474 p = 1) : d2981 p ≤ (2 : Int) + d7068 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2981, d7068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32274 p hg
    simpa only [d2981, d7068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2981, d7068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32193 p hg
    simpa only [d2981, d7068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32276 (p : Pattern) (guard : d4474 p = 1) : d2982 p ≤ (2 : Int) + d7069 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2982, d7069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32193 p hg
    simpa only [d2982, d7069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2982, d7069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2982, d7069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32277 (p : Pattern) (guard : d4474 p = 1) : d2983 p ≤ (2 : Int) + d7070 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2983, d7070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32275 p hg
    simpa only [d2983, d7070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2983, d7070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32276 p hg
    simpa only [d2983, d7070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32278 (p : Pattern) (guard : d4474 p = 1) : d2984 p ≤ (2 : Int) + d7071 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2984, d7071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32276 p hg
    simpa only [d2984, d7071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2984, d7071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2984, d7071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32279 (p : Pattern) (guard : d4474 p = 1) : d2985 p ≤ (2 : Int) + d7072 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2985, d7072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32277 p hg
    simpa only [d2985, d7072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2985, d7072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32278 p hg
    simpa only [d2985, d7072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32280 (p : Pattern) (guard : d4474 p = 1) : d2986 p ≤ (2 : Int) + d7073 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2986, d7073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32278 p hg
    simpa only [d2986, d7073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2986, d7073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2986, d7073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32281 (p : Pattern) (guard : d4474 p = 1) : d2987 p ≤ (2 : Int) + d7074 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2987, d7074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32279 p hg
    simpa only [d2987, d7074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2987, d7074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32280 p hg
    simpa only [d2987, d7074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32282 (p : Pattern) (guard : d4474 p = 1) : d2988 p ≤ (2 : Int) + d7075 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2988, d7075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32272 p hg
    simpa only [d2988, d7075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2988, d7075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32281 p hg
    simpa only [d2988, d7075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32283 (p : Pattern) (guard : d4474 p = 1) : d2989 p ≤ (2 : Int) + d7076 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2989, d7076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32273 p hg
    simpa only [d2989, d7076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2989, d7076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32282 p hg
    simpa only [d2989, d7076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32284 (p : Pattern) (guard : d4474 p = 1) : d2990 p ≤ (2 : Int) + d7077 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2990, d7077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32272 p hg
    simpa only [d2990, d7077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2990, d7077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2990, d7077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32285 (p : Pattern) (guard : d4474 p = 1) : d2991 p ≤ (2 : Int) + d7078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2991, d7078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32273 p hg
    simpa only [d2991, d7078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2991, d7078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32284 p hg
    simpa only [d2991, d7078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32286 (p : Pattern) (guard : d4474 p = 1) : d2992 p ≤ (2 : Int) + d7079 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2992, d7079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32283 p hg
    simpa only [d2992, d7079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2992, d7079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32285 p hg
    simpa only [d2992, d7079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32287 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d1939 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4776 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32288 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32287 p hg
    simpa only [d103, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4777 p hg
    simpa only [d103, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32289 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1941 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32288 p hg
    simpa only [d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32290 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1942 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32289 p hg
    simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32288 p hg
    simpa only [d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32291 (p : Pattern) (guard : d0 p = 1) : d1942 p ≤ (2 : Int) + d1942 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32292 (p : Pattern) (guard : d4474 p = 1) : d2993 p ≤ (2 : Int) + d1942 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32290 p hg
    simpa only [d4474, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32291 p hg
    simpa only [d4474, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32293 (p : Pattern) (guard : d1 p = 1) : d1872 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15997 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32294 (p : Pattern) (guard : d1 p = 1) : d1873 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32293 p hg
    simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4894 p hg
    simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32295 (p : Pattern) (guard : d1 p = 1) : d1874 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15999 p hg
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32294 p hg
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32296 (p : Pattern) (guard : d1 p = 1) : d1875 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32295 p hg
    simpa only [d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32294 p hg
    simpa only [d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32297 (p : Pattern) (guard : d4474 p = 1) : d1876 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32296 p hg
    simpa only [d4474, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32298 (p : Pattern) (guard : d4474 p = 1) : d2994 p ≤ (2 : Int) + d7080 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2994, d7080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32292 p hg
    simpa only [d2994, d7080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2994, d7080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32297 p hg
    simpa only [d2994, d7080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32299 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d1963 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16235 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32300 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d1964 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32299 p hg
    simpa only [d107, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16236 p hg
    simpa only [d107, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32301 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d2129 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32300 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32302 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d2130 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32301 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32300 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32303 (p : Pattern) (guard : d0 p = 1) : d2130 p ≤ (2 : Int) + d2130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32304 (p : Pattern) (guard : d4474 p = 1) : d2995 p ≤ (2 : Int) + d2130 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32302 p hg
    simpa only [d4474, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32303 p hg
    simpa only [d4474, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32305 (p : Pattern) (guard : d1 p = 1) : d1880 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32306 (p : Pattern) (guard : d1 p = 1) : d1881 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32305 p hg
    simpa only [d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32307 (p : Pattern) (guard : d1 p = 1) : d1882 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4787 p hg
    simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32306 p hg
    simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32308 (p : Pattern) (guard : d1 p = 1) : d1883 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32307 p hg
    simpa only [d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32306 p hg
    simpa only [d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32309 (p : Pattern) (guard : d4474 p = 1) : d1884 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32308 p hg
    simpa only [d4474, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32310 (p : Pattern) (guard : d4474 p = 1) : d2996 p ≤ (2 : Int) + d7081 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2996, d7081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32304 p hg
    simpa only [d2996, d7081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2996, d7081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32309 p hg
    simpa only [d2996, d7081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32311 (p : Pattern) (guard : d4474 p = 1) : d2997 p ≤ (2 : Int) + d7082 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2997, d7082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32298 p hg
    simpa only [d2997, d7082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2997, d7082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32310 p hg
    simpa only [d2997, d7082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32312 (p : Pattern) (guard : d4474 p = 1) : d2998 p ≤ (2 : Int) + d7083 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2998, d7083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32298 p hg
    simpa only [d2998, d7083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2998, d7083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32311 p hg
    simpa only [d2998, d7083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32313 (p : Pattern) (guard : d4474 p = 1) : d2999 p ≤ (2 : Int) + d7084 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2999, d7084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32184 p hg
    simpa only [d2999, d7084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2999, d7084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2999, d7084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32314 (p : Pattern) (guard : d4474 p = 1) : d3000 p ≤ (2 : Int) + d7085 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3000, d7085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32311 p hg
    simpa only [d3000, d7085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3000, d7085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32313 p hg
    simpa only [d3000, d7085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32315 (p : Pattern) (guard : d4474 p = 1) : d3001 p ≤ (2 : Int) + d7086 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3001, d7086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32312 p hg
    simpa only [d3001, d7086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3001, d7086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32314 p hg
    simpa only [d3001, d7086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32316 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d1945 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32317 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1946 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32316 p hg
    simpa only [d103, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15977 p hg
    simpa only [d103, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32318 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1947 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32317 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32319 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15997 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32320 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1955 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32319 p hg
    simpa only [d103, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4782 p hg
    simpa only [d103, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32321 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1956 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32288 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32320 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32322 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1957 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32318 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32321 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32323 (p : Pattern) (guard : d0 p = 1) : d1957 p ≤ (2 : Int) + d1957 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32324 (p : Pattern) (guard : d4474 p = 1) : d3002 p ≤ (2 : Int) + d1957 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32322 p hg
    simpa only [d4474, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32323 p hg
    simpa only [d4474, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32325 (p : Pattern) (guard : d4474 p = 1) : d3003 p ≤ (2 : Int) + d7087 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3003, d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32324 p hg
    simpa only [d3003, d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3003, d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16037 p hg
    simpa only [d3003, d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32326 (p : Pattern) (guard : d4474 p = 1) : d3004 p ≤ (2 : Int) + d7087 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3004, d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32324 p hg
    simpa only [d3004, d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3004, d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16285 p hg
    simpa only [d3004, d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32327 (p : Pattern) (guard : d4474 p = 1) : d3005 p ≤ (2 : Int) + d7087 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32325 p hg
    simpa only [d3005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32326 p hg
    simpa only [d3005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32328 (p : Pattern) (guard : d4474 p = 1) : d3006 p ≤ (2 : Int) + d7087 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3006, d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32324 p hg
    simpa only [d3006, d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3006, d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3006, d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32329 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d1960 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16303 p hg
    simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32330 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d1961 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32329 p hg
    simpa only [d107, d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16305 p hg
    simpa only [d107, d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32331 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d1962 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32330 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32332 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32333 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32332 p hg
    simpa only [d107, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d107, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32334 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d1965 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32300 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32333 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32335 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d1966 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32331 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32334 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32336 (p : Pattern) (guard : d0 p = 1) : d1966 p ≤ (2 : Int) + d1966 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32337 (p : Pattern) (guard : d4474 p = 1) : d3007 p ≤ (2 : Int) + d1966 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32335 p hg
    simpa only [d4474, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32336 p hg
    simpa only [d4474, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32338 (p : Pattern) (guard : d4474 p = 1) : d3008 p ≤ (2 : Int) + d7088 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3008, d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32337 p hg
    simpa only [d3008, d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3008, d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3008, d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32339 (p : Pattern) (guard : d4474 p = 1) : d3009 p ≤ (2 : Int) + d7089 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3009, d7089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32328 p hg
    simpa only [d3009, d7089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3009, d7089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32338 p hg
    simpa only [d3009, d7089, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
