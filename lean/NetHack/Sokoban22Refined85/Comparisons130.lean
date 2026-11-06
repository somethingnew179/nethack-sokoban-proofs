/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons129
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18200 (p : Pattern) (guard : d4902 p = 1) : d2400 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2400, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18198 p hg
    simpa only [d2400, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2400, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18199 p hg
    simpa only [d2400, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18201 (p : Pattern) (guard : d4902 p = 1) : d2401 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2401, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18191 p hg
    simpa only [d2401, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2401, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18200 p hg
    simpa only [d2401, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18202 (p : Pattern) (guard : d4902 p = 1) : d2402 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2402, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18092 p hg
    simpa only [d2402, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2402, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18201 p hg
    simpa only [d2402, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18203 (p : Pattern) (guard : d4902 p = 1) : d2403 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2403, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18114 p hg
    simpa only [d2403, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2403, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18202 p hg
    simpa only [d2403, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18204 (p : Pattern) (guard : d4902 p = 1) : d2404 p ≤ (0 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2404, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18004 p hg
    simpa only [d2404, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2404, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18008 p hg
    simpa only [d2404, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18205 (p : Pattern) (guard : d4902 p = 1) : d2405 p ≤ (0 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2405, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18028 p hg
    simpa only [d2405, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2405, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18204 p hg
    simpa only [d2405, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18206 (p : Pattern) (guard : d4902 p = 1) : d2406 p ≤ (0 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2406, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18004 p hg
    simpa only [d2406, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2406, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18012 p hg
    simpa only [d2406, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18207 (p : Pattern) (guard : d4902 p = 1) : d2407 p ≤ (0 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2407, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18007 p hg
    simpa only [d2407, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2407, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2407, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18208 (p : Pattern) (guard : d4902 p = 1) : d2408 p ≤ (0 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2408, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18206 p hg
    simpa only [d2408, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2408, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18207 p hg
    simpa only [d2408, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18209 (p : Pattern) (guard : d4902 p = 1) : d2409 p ≤ (0 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2409, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18205 p hg
    simpa only [d2409, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2409, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18208 p hg
    simpa only [d2409, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18210 (p : Pattern) (guard : d4902 p = 1) : d2410 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2410, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18040 p hg
    simpa only [d2410, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2410, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18207 p hg
    simpa only [d2410, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18211 (p : Pattern) (guard : d4902 p = 1) : d2411 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2411, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18210 p hg
    simpa only [d2411, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2411, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18047 p hg
    simpa only [d2411, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18212 (p : Pattern) (guard : d4902 p = 1) : d2412 p ≤ (0 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2412, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18209 p hg
    simpa only [d2412, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2412, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18211 p hg
    simpa only [d2412, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18213 (p : Pattern) (guard : d4902 p = 1) : d2413 p ≤ (0 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2413, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18070 p hg
    simpa only [d2413, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2413, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18212 p hg
    simpa only [d2413, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18214 (p : Pattern) (guard : d4902 p = 1) : d2414 p ≤ (0 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2414, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18204 p hg
    simpa only [d2414, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2414, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18014 p hg
    simpa only [d2414, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18215 (p : Pattern) (guard : d4902 p = 1) : d2415 p ≤ (0 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2415, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18207 p hg
    simpa only [d2415, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2415, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18046 p hg
    simpa only [d2415, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18216 (p : Pattern) (guard : d4902 p = 1) : d2416 p ≤ (0 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2416, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18214 p hg
    simpa only [d2416, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2416, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18215 p hg
    simpa only [d2416, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18217 (p : Pattern) (guard : d4902 p = 1) : d2417 p ≤ (0 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2417, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18207 p hg
    simpa only [d2417, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2417, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2417, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18218 (p : Pattern) (guard : d4902 p = 1) : d2418 p ≤ (0 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2418, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18217 p hg
    simpa only [d2418, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2418, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2418, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18219 (p : Pattern) (guard : d4902 p = 1) : d2419 p ≤ (0 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2419, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18216 p hg
    simpa only [d2419, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2419, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18218 p hg
    simpa only [d2419, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18220 (p : Pattern) (guard : d4902 p = 1) : d2420 p ≤ (0 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2420, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18061 p hg
    simpa only [d2420, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2420, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18219 p hg
    simpa only [d2420, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18221 (p : Pattern) (guard : d4902 p = 1) : d2421 p ≤ (0 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2421, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18213 p hg
    simpa only [d2421, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2421, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18220 p hg
    simpa only [d2421, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18222 (p : Pattern) (guard : d4902 p = 1) : d2422 p ≤ (0 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2422, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17996 p hg
    simpa only [d2422, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2422, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18055 p hg
    simpa only [d2422, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18223 (p : Pattern) (guard : d4902 p = 1) : d2423 p ≤ (0 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2423, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18222 p hg
    simpa only [d2423, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2423, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18056 p hg
    simpa only [d2423, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18224 (p : Pattern) (guard : d4902 p = 1) : d2424 p ≤ (0 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15557 p hg
    simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18225 (p : Pattern) (guard : d4902 p = 1) : d2425 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2425, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18224 p hg
    simpa only [d2425, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2425, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2425, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18226 (p : Pattern) (guard : d4902 p = 1) : d2426 p ≤ (0 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2426, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18224 p hg
    simpa only [d2426, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2426, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18225 p hg
    simpa only [d2426, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18227 (p : Pattern) (guard : d4902 p = 1) : d2427 p ≤ (0 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2427, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17993 p hg
    simpa only [d2427, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2427, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18226 p hg
    simpa only [d2427, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18228 (p : Pattern) (guard : d4902 p = 1) : d2428 p ≤ (0 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2428, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18227 p hg
    simpa only [d2428, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2428, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2428, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18229 (p : Pattern) (guard : d4902 p = 1) : d2429 p ≤ (0 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2429, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18228 p hg
    simpa only [d2429, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2429, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2429, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18230 (p : Pattern) (guard : d4902 p = 1) : d2430 p ≤ (0 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2430, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18223 p hg
    simpa only [d2430, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2430, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18229 p hg
    simpa only [d2430, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18231 (p : Pattern) (guard : d4902 p = 1) : d2431 p ≤ (0 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2431, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17993 p hg
    simpa only [d2431, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2431, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18036 p hg
    simpa only [d2431, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18232 (p : Pattern) (guard : d4902 p = 1) : d2432 p ≤ (0 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2432, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18028 p hg
    simpa only [d2432, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2432, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18231 p hg
    simpa only [d2432, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18233 (p : Pattern) (guard : d4902 p = 1) : d2433 p ≤ (0 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2433, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18232 p hg
    simpa only [d2433, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2433, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18063 p hg
    simpa only [d2433, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18234 (p : Pattern) (guard : d4902 p = 1) : d2434 p ≤ (0 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2434, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18226 p hg
    simpa only [d2434, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2434, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2434, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18235 (p : Pattern) (guard : d4902 p = 1) : d2435 p ≤ (0 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2435, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18234 p hg
    simpa only [d2435, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2435, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2435, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18236 (p : Pattern) (guard : d4902 p = 1) : d2436 p ≤ (0 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2436, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18235 p hg
    simpa only [d2436, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2436, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2436, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18237 (p : Pattern) (guard : d4902 p = 1) : d2437 p ≤ (0 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2437, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18233 p hg
    simpa only [d2437, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2437, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18236 p hg
    simpa only [d2437, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18238 (p : Pattern) (guard : d4902 p = 1) : d2438 p ≤ (0 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2438, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18230 p hg
    simpa only [d2438, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2438, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18237 p hg
    simpa only [d2438, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18239 (p : Pattern) (guard : d4902 p = 1) : d2439 p ≤ (0 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2439, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18221 p hg
    simpa only [d2439, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2439, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18238 p hg
    simpa only [d2439, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18240 (p : Pattern) (guard : d4902 p = 1) : d2440 p ≤ (0 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2440, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18238 p hg
    simpa only [d2440, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2440, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2440, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18241 (p : Pattern) (guard : d4902 p = 1) : d2441 p ≤ (0 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2441, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18239 p hg
    simpa only [d2441, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2441, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18240 p hg
    simpa only [d2441, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18242 (p : Pattern) (guard : d4902 p = 1) : d2442 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2442, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18108 p hg
    simpa only [d2442, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2442, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18241 p hg
    simpa only [d2442, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18243 (p : Pattern) (guard : d4902 p = 1) : d2443 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2443, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18092 p hg
    simpa only [d2443, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2443, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18242 p hg
    simpa only [d2443, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18244 (p : Pattern) (guard : d4902 p = 1) : d2444 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2444, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18129 p hg
    simpa only [d2444, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2444, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2444, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18245 (p : Pattern) (guard : d4902 p = 1) : d2445 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2445, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18155 p hg
    simpa only [d2445, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2445, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18244 p hg
    simpa only [d2445, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18246 (p : Pattern) (guard : d4902 p = 1) : d2446 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2446, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18244 p hg
    simpa only [d2446, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2446, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2446, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18247 (p : Pattern) (guard : d4902 p = 1) : d2447 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2447, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18245 p hg
    simpa only [d2447, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2447, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18246 p hg
    simpa only [d2447, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18248 (p : Pattern) (guard : d4902 p = 1) : d2448 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2448, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18143 p hg
    simpa only [d2448, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2448, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2448, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18249 (p : Pattern) (guard : d4902 p = 1) : d2449 p ≤ (0 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2449, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18162 p hg
    simpa only [d2449, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2449, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18248 p hg
    simpa only [d2449, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18250 (p : Pattern) (guard : d4902 p = 1) : d2450 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2450, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18248 p hg
    simpa only [d2450, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2450, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2450, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18251 (p : Pattern) (guard : d4902 p = 1) : d2451 p ≤ (0 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2451, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18249 p hg
    simpa only [d2451, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2451, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18250 p hg
    simpa only [d2451, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18252 (p : Pattern) (guard : d4902 p = 1) : d2452 p ≤ (0 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2452, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18247 p hg
    simpa only [d2452, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2452, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18251 p hg
    simpa only [d2452, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18253 (p : Pattern) (guard : d4902 p = 1) : d2453 p ≤ (0 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2453, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18149 p hg
    simpa only [d2453, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2453, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18252 p hg
    simpa only [d2453, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18254 (p : Pattern) (guard : d4902 p = 1) : d2454 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2454, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18177 p hg
    simpa only [d2454, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2454, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18244 p hg
    simpa only [d2454, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18255 (p : Pattern) (guard : d4902 p = 1) : d2455 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2455, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18254 p hg
    simpa only [d2455, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2455, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18246 p hg
    simpa only [d2455, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18256 (p : Pattern) (guard : d4902 p = 1) : d2456 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2456, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18255 p hg
    simpa only [d2456, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2456, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18182 p hg
    simpa only [d2456, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18257 (p : Pattern) (guard : d4902 p = 1) : d2457 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2457, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18176 p hg
    simpa only [d2457, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2457, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18256 p hg
    simpa only [d2457, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18258 (p : Pattern) (guard : d4902 p = 1) : d2458 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2458, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18253 p hg
    simpa only [d2458, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2458, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18257 p hg
    simpa only [d2458, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18259 (p : Pattern) (guard : d4902 p = 1) : d2459 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2459, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18257 p hg
    simpa only [d2459, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2459, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18189 p hg
    simpa only [d2459, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18260 (p : Pattern) (guard : d4902 p = 1) : d2460 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2460, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18258 p hg
    simpa only [d2460, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2460, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18259 p hg
    simpa only [d2460, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18261 (p : Pattern) (guard : d4902 p = 1) : d2461 p ≤ (0 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2461, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18135 p hg
    simpa only [d2461, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2461, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18139 p hg
    simpa only [d2461, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18262 (p : Pattern) (guard : d4902 p = 1) : d2462 p ≤ (0 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2462, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18154 p hg
    simpa only [d2462, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2462, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18261 p hg
    simpa only [d2462, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18263 (p : Pattern) (guard : d4902 p = 1) : d2463 p ≤ (0 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2463, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18262 p hg
    simpa only [d2463, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2463, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18248 p hg
    simpa only [d2463, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18264 (p : Pattern) (guard : d4902 p = 1) : d2464 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2464, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18138 p hg
    simpa only [d2464, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2464, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2464, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18265 (p : Pattern) (guard : d4902 p = 1) : d2465 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2465, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18264 p hg
    simpa only [d2465, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2465, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2465, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18266 (p : Pattern) (guard : d4902 p = 1) : d2466 p ≤ (0 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2466, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18265 p hg
    simpa only [d2466, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2466, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2466, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18267 (p : Pattern) (guard : d4902 p = 1) : d2467 p ≤ (0 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2467, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18263 p hg
    simpa only [d2467, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2467, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18266 p hg
    simpa only [d2467, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18268 (p : Pattern) (guard : d4902 p = 1) : d2468 p ≤ (0 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2468, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18194 p hg
    simpa only [d2468, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2468, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18267 p hg
    simpa only [d2468, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18269 (p : Pattern) (guard : d4902 p = 1) : d2469 p ≤ (0 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2469, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18127 p hg
    simpa only [d2469, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2469, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18139 p hg
    simpa only [d2469, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18270 (p : Pattern) (guard : d4902 p = 1) : d2470 p ≤ (0 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2470, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18269 p hg
    simpa only [d2470, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2470, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18143 p hg
    simpa only [d2470, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18271 (p : Pattern) (guard : d4902 p = 1) : d2471 p ≤ (0 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2471, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18270 p hg
    simpa only [d2471, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2471, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18265 p hg
    simpa only [d2471, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18272 (p : Pattern) (guard : d4902 p = 1) : d2472 p ≤ (0 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2472, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18020 p hg
    simpa only [d2472, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2472, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2472, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18273 (p : Pattern) (guard : d4902 p = 1) : d2473 p ≤ (0 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2473, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18271 p hg
    simpa only [d2473, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2473, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18272 p hg
    simpa only [d2473, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18274 (p : Pattern) (guard : d4902 p = 1) : d2474 p ≤ (0 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2474, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18255 p hg
    simpa only [d2474, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2474, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18273 p hg
    simpa only [d2474, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18275 (p : Pattern) (guard : d4902 p = 1) : d2475 p ≤ (0 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2475, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18268 p hg
    simpa only [d2475, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2475, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18274 p hg
    simpa only [d2475, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18276 (p : Pattern) (guard : d4902 p = 1) : d2476 p ≤ (0 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2476, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18154 p hg
    simpa only [d2476, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2476, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18036 p hg
    simpa only [d2476, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18277 (p : Pattern) (guard : d4902 p = 1) : d2477 p ≤ (0 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2477, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18126 p hg
    simpa only [d2477, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2477, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18276 p hg
    simpa only [d2477, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18278 (p : Pattern) (guard : d4902 p = 1) : d2478 p ≤ (0 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2478, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18277 p hg
    simpa only [d2478, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2478, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18159 p hg
    simpa only [d2478, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18279 (p : Pattern) (guard : d4902 p = 1) : d2479 p ≤ (0 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2479, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18278 p hg
    simpa only [d2479, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2479, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18182 p hg
    simpa only [d2479, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18280 (p : Pattern) (guard : d4902 p = 1) : d2480 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2480, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18154 p hg
    simpa only [d2480, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2480, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18244 p hg
    simpa only [d2480, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18281 (p : Pattern) (guard : d4902 p = 1) : d2481 p ≤ (0 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2481, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18280 p hg
    simpa only [d2481, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2481, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18181 p hg
    simpa only [d2481, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18282 (p : Pattern) (guard : d4902 p = 1) : d2482 p ≤ (0 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2482, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18001 p hg
    simpa only [d2482, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2482, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2482, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18283 (p : Pattern) (guard : d4902 p = 1) : d2483 p ≤ (0 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2483, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18282 p hg
    simpa only [d2483, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2483, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2483, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18284 (p : Pattern) (guard : d4902 p = 1) : d2484 p ≤ (0 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2484, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18281 p hg
    simpa only [d2484, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2484, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18283 p hg
    simpa only [d2484, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18285 (p : Pattern) (guard : d4902 p = 1) : d2485 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2485, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18279 p hg
    simpa only [d2485, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2485, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18284 p hg
    simpa only [d2485, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18286 (p : Pattern) (guard : d4902 p = 1) : d2486 p ≤ (0 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2486, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18275 p hg
    simpa only [d2486, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2486, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18285 p hg
    simpa only [d2486, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18287 (p : Pattern) (guard : d4902 p = 1) : d2487 p ≤ (0 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2487, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18154 p hg
    simpa only [d2487, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2487, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18000 p hg
    simpa only [d2487, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18288 (p : Pattern) (guard : d4902 p = 1) : d2488 p ≤ (0 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2488, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18126 p hg
    simpa only [d2488, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2488, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18287 p hg
    simpa only [d2488, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18289 (p : Pattern) (guard : d4902 p = 1) : d2489 p ≤ (0 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2489, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18129 p hg
    simpa only [d2489, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2489, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18000 p hg
    simpa only [d2489, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18290 (p : Pattern) (guard : d4902 p = 1) : d2490 p ≤ (0 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2490, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18289 p hg
    simpa only [d2490, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2490, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2490, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18291 (p : Pattern) (guard : d4902 p = 1) : d2491 p ≤ (0 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2491, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18288 p hg
    simpa only [d2491, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2491, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18290 p hg
    simpa only [d2491, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18292 (p : Pattern) (guard : d4902 p = 1) : d2492 p ≤ (0 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2492, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18172 p hg
    simpa only [d2492, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2492, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18036 p hg
    simpa only [d2492, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18293 (p : Pattern) (guard : d4902 p = 1) : d2493 p ≤ (0 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2493, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18292 p hg
    simpa only [d2493, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2493, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2493, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18294 (p : Pattern) (guard : d4902 p = 1) : d2494 p ≤ (0 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2494, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18293 p hg
    simpa only [d2494, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2494, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2494, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18295 (p : Pattern) (guard : d4902 p = 1) : d2495 p ≤ (0 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2495, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18291 p hg
    simpa only [d2495, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2495, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18294 p hg
    simpa only [d2495, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18296 (p : Pattern) (guard : d4902 p = 1) : d2496 p ≤ (0 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2496, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18295 p hg
    simpa only [d2496, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2496, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18284 p hg
    simpa only [d2496, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18297 (p : Pattern) (guard : d4902 p = 1) : d2497 p ≤ (0 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2497, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18296 p hg
    simpa only [d2497, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2497, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d2497, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18298 (p : Pattern) (guard : d4902 p = 1) : d2498 p ≤ (0 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2498, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18286 p hg
    simpa only [d2498, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2498, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18297 p hg
    simpa only [d2498, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18299 (p : Pattern) (guard : d4902 p = 1) : d2499 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2499, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18260 p hg
    simpa only [d2499, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2499, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18298 p hg
    simpa only [d2499, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18300 (p : Pattern) (guard : d4902 p = 1) : d2500 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2500, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18092 p hg
    simpa only [d2500, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2500, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18299 p hg
    simpa only [d2500, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18301 (p : Pattern) (guard : d4902 p = 1) : d2501 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2501, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18243 p hg
    simpa only [d2501, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2501, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18300 p hg
    simpa only [d2501, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18302 (p : Pattern) (guard : d4902 p = 1) : d2502 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2502, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18203 p hg
    simpa only [d2502, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2502, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18301 p hg
    simpa only [d2502, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18303 (p : Pattern) (guard : d0 p = 1) : d318 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18304 (p : Pattern) (guard : d4902 p = 1) : d2184 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18303 p hg
    simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18305 (p : Pattern) (guard : d4902 p = 1) : d2185 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15674 p hg
    simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18306 (p : Pattern) (guard : d4902 p = 1) : d2186 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18304 p hg
    simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18307 (p : Pattern) (guard : d4902 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare18308 (p : Pattern) (guard : d4902 p = 1) : d2187 p ≤ (2 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2187, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2187, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2187, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2187, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18309 (p : Pattern) (guard : d4902 p = 1) : d2188 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2188, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18306 p hg
    simpa only [d2188, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2188, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18308 p hg
    simpa only [d2188, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18310 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18311 (p : Pattern) (guard : d4902 p = 1) : d2189 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18310 p hg
    simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18312 (p : Pattern) (guard : d4902 p = 1) : d2190 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18311 p hg
    simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18313 (p : Pattern) (guard : d4902 p = 1) : d2191 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2191, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18312 p hg
    simpa only [d2191, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2191, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18308 p hg
    simpa only [d2191, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18314 (p : Pattern) (guard : d4902 p = 1) : d2192 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18309 p hg
    simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18313 p hg
    simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18315 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18316 (p : Pattern) (guard : d4902 p = 1) : d2193 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18315 p hg
    simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18317 (p : Pattern) (guard : d4902 p = 1) : d2194 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18316 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18318 (p : Pattern) (guard : d4902 p = 1) : d2195 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2195, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18317 p hg
    simpa only [d2195, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2195, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18308 p hg
    simpa only [d2195, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18319 (p : Pattern) (guard : d4902 p = 1) : d2196 p ≤ (2 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15688 p hg
    simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18320 (p : Pattern) (guard : d4902 p = 1) : d2197 p ≤ (2 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2197, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18319 p hg
    simpa only [d2197, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2197, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2197, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18321 (p : Pattern) (guard : d4902 p = 1) : d2198 p ≤ (2 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2198, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18319 p hg
    simpa only [d2198, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2198, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18320 p hg
    simpa only [d2198, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18322 (p : Pattern) (guard : d4902 p = 1) : d2199 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2199, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18318 p hg
    simpa only [d2199, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2199, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18321 p hg
    simpa only [d2199, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18323 (p : Pattern) (guard : d4902 p = 1) : d2200 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2200, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18314 p hg
    simpa only [d2200, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2200, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18322 p hg
    simpa only [d2200, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18324 (p : Pattern) (guard : d4902 p = 1) : d2201 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2201, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2201, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2201, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18308 p hg
    simpa only [d2201, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18325 (p : Pattern) (guard : d4902 p = 1) : d2202 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2202, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18324 p hg
    simpa only [d2202, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2202, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18321 p hg
    simpa only [d2202, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18326 (p : Pattern) (guard : d4902 p = 1) : d2203 p ≤ (2 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12098 p hg
    simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15699 p hg
    simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18327 (p : Pattern) (guard : d4902 p = 1) : d2204 p ≤ (2 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2204, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18326 p hg
    simpa only [d2204, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2204, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2204, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18328 (p : Pattern) (guard : d4902 p = 1) : d2205 p ≤ (2 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2205, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18326 p hg
    simpa only [d2205, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2205, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18327 p hg
    simpa only [d2205, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18329 (p : Pattern) (guard : d4902 p = 1) : d2206 p ≤ (2 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2206, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18328 p hg
    simpa only [d2206, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2206, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2206, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18330 (p : Pattern) (guard : d4902 p = 1) : d2207 p ≤ (2 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2207, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18325 p hg
    simpa only [d2207, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2207, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18329 p hg
    simpa only [d2207, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18331 (p : Pattern) (guard : d4902 p = 1) : d2208 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2208, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18323 p hg
    simpa only [d2208, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2208, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18330 p hg
    simpa only [d2208, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18332 (p : Pattern) (guard : d4902 p = 1) : d2209 p ≤ (2 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15716 p hg
    simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18333 (p : Pattern) (guard : d4902 p = 1) : d2210 p ≤ (2 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2210, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18332 p hg
    simpa only [d2210, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2210, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2210, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18334 (p : Pattern) (guard : d4902 p = 1) : d2211 p ≤ (2 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2211, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2211, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2211, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18333 p hg
    simpa only [d2211, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18335 (p : Pattern) (guard : d4902 p = 1) : d2212 p ≤ (2 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12252 p hg
    simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15771 p hg
    simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18336 (p : Pattern) (guard : d4902 p = 1) : d2213 p ≤ (2 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2213, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18335 p hg
    simpa only [d2213, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2213, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2213, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18337 (p : Pattern) (guard : d4902 p = 1) : d2214 p ≤ (2 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2214, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2214, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2214, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18336 p hg
    simpa only [d2214, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18338 (p : Pattern) (guard : d4902 p = 1) : d2215 p ≤ (2 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2215, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18334 p hg
    simpa only [d2215, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2215, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18337 p hg
    simpa only [d2215, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18339 (p : Pattern) (guard : d4902 p = 1) : d2216 p ≤ (2 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12115 p hg
    simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15738 p hg
    simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
