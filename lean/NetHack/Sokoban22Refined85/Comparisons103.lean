/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons102
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14420 (p : Pattern) (guard : d4902 p = 1) : d131 p ≤ (0 : Int) + d2395 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d131, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14419 p hg
    simpa only [d131, d2395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d131, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14373 p hg
    simpa only [d131, d2395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14421 (p : Pattern) (guard : d4902 p = 1) : d146 p ≤ (0 : Int) + d2396 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d146, d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14404 p hg
    simpa only [d146, d2396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d146, d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14392 p hg
    simpa only [d146, d2396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14422 (p : Pattern) (guard : d4902 p = 1) : d147 p ≤ (0 : Int) + d2397 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d147, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14420 p hg
    simpa only [d147, d2397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d147, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14421 p hg
    simpa only [d147, d2397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14423 (p : Pattern) (guard : d4902 p = 1) : d158 p ≤ (0 : Int) + d2398 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d158, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14422 p hg
    simpa only [d158, d2398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d158, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14409 p hg
    simpa only [d158, d2398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14424 (p : Pattern) (guard : d4902 p = 1) : d165 p ≤ (0 : Int) + d2399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d165, d2399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14409 p hg
    simpa only [d165, d2399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d165, d2399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d165, d2399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14425 (p : Pattern) (guard : d4902 p = 1) : d166 p ≤ (0 : Int) + d2400 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d166, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14423 p hg
    simpa only [d166, d2400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d166, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14424 p hg
    simpa only [d166, d2400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14426 (p : Pattern) (guard : d4902 p = 1) : d167 p ≤ (0 : Int) + d2401 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d167, d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14416 p hg
    simpa only [d167, d2401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d167, d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14425 p hg
    simpa only [d167, d2401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14427 (p : Pattern) (guard : d4902 p = 1) : d168 p ≤ (0 : Int) + d2402 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d168, d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14317 p hg
    simpa only [d168, d2402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d168, d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14426 p hg
    simpa only [d168, d2402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14428 (p : Pattern) (guard : d4902 p = 1) : d169 p ≤ (0 : Int) + d2403 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d169, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14339 p hg
    simpa only [d169, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d169, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14427 p hg
    simpa only [d169, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14429 (p : Pattern) (guard : d4902 p = 1) : d170 p ≤ (0 : Int) + d2404 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d170, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14229 p hg
    simpa only [d170, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d170, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14233 p hg
    simpa only [d170, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14430 (p : Pattern) (guard : d4902 p = 1) : d171 p ≤ (0 : Int) + d2405 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d171, d2405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14253 p hg
    simpa only [d171, d2405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d171, d2405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14429 p hg
    simpa only [d171, d2405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14431 (p : Pattern) (guard : d4902 p = 1) : d172 p ≤ (0 : Int) + d2406 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d172, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14229 p hg
    simpa only [d172, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d172, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14237 p hg
    simpa only [d172, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14432 (p : Pattern) (guard : d4902 p = 1) : d173 p ≤ (0 : Int) + d2407 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d173, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14232 p hg
    simpa only [d173, d2407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d173, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d173, d2407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14433 (p : Pattern) (guard : d4902 p = 1) : d174 p ≤ (0 : Int) + d2408 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d174, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14431 p hg
    simpa only [d174, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d174, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14432 p hg
    simpa only [d174, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14434 (p : Pattern) (guard : d4902 p = 1) : d175 p ≤ (0 : Int) + d2409 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d175, d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14430 p hg
    simpa only [d175, d2409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d175, d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14433 p hg
    simpa only [d175, d2409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14435 (p : Pattern) (guard : d4902 p = 1) : d176 p ≤ (0 : Int) + d2410 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d176, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14265 p hg
    simpa only [d176, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d176, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14432 p hg
    simpa only [d176, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14436 (p : Pattern) (guard : d4902 p = 1) : d177 p ≤ (0 : Int) + d2411 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d177, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14435 p hg
    simpa only [d177, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d177, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14272 p hg
    simpa only [d177, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14437 (p : Pattern) (guard : d4902 p = 1) : d178 p ≤ (0 : Int) + d2412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d178, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14434 p hg
    simpa only [d178, d2412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d178, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14436 p hg
    simpa only [d178, d2412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14438 (p : Pattern) (guard : d4902 p = 1) : d179 p ≤ (0 : Int) + d2413 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d179, d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14295 p hg
    simpa only [d179, d2413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d179, d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14437 p hg
    simpa only [d179, d2413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14439 (p : Pattern) (guard : d4902 p = 1) : d180 p ≤ (0 : Int) + d2414 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d180, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14429 p hg
    simpa only [d180, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d180, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14239 p hg
    simpa only [d180, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14440 (p : Pattern) (guard : d4902 p = 1) : d181 p ≤ (0 : Int) + d2415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d181, d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14432 p hg
    simpa only [d181, d2415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d181, d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14271 p hg
    simpa only [d181, d2415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14441 (p : Pattern) (guard : d4902 p = 1) : d182 p ≤ (0 : Int) + d2416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d182, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14439 p hg
    simpa only [d182, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d182, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14440 p hg
    simpa only [d182, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14442 (p : Pattern) (guard : d4902 p = 1) : d183 p ≤ (0 : Int) + d2417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d183, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14432 p hg
    simpa only [d183, d2417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d183, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d183, d2417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14443 (p : Pattern) (guard : d4902 p = 1) : d184 p ≤ (0 : Int) + d2418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d184, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14442 p hg
    simpa only [d184, d2418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d184, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d184, d2418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14444 (p : Pattern) (guard : d4902 p = 1) : d185 p ≤ (0 : Int) + d2419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d185, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14441 p hg
    simpa only [d185, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d185, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14443 p hg
    simpa only [d185, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14445 (p : Pattern) (guard : d4902 p = 1) : d186 p ≤ (0 : Int) + d2420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d186, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14286 p hg
    simpa only [d186, d2420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d186, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14444 p hg
    simpa only [d186, d2420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14446 (p : Pattern) (guard : d4902 p = 1) : d187 p ≤ (0 : Int) + d2421 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d187, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14438 p hg
    simpa only [d187, d2421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d187, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14445 p hg
    simpa only [d187, d2421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14447 (p : Pattern) (guard : d4902 p = 1) : d188 p ≤ (0 : Int) + d2422 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d188, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14221 p hg
    simpa only [d188, d2422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d188, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14280 p hg
    simpa only [d188, d2422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14448 (p : Pattern) (guard : d4902 p = 1) : d189 p ≤ (0 : Int) + d2423 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d189, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14447 p hg
    simpa only [d189, d2423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d189, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14281 p hg
    simpa only [d189, d2423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14449 (p : Pattern) (guard : d4902 p = 1) : d191 p ≤ (0 : Int) + d2424 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11750 p hg
    simpa only [d4902, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14450 (p : Pattern) (guard : d4902 p = 1) : d192 p ≤ (0 : Int) + d2425 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d192, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14449 p hg
    simpa only [d192, d2425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d192, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d192, d2425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14451 (p : Pattern) (guard : d4902 p = 1) : d193 p ≤ (0 : Int) + d2426 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d193, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14449 p hg
    simpa only [d193, d2426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d193, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14450 p hg
    simpa only [d193, d2426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14452 (p : Pattern) (guard : d4902 p = 1) : d194 p ≤ (0 : Int) + d2427 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d194, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14218 p hg
    simpa only [d194, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d194, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14451 p hg
    simpa only [d194, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14453 (p : Pattern) (guard : d4902 p = 1) : d195 p ≤ (0 : Int) + d2428 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d195, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14452 p hg
    simpa only [d195, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d195, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d195, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14454 (p : Pattern) (guard : d4902 p = 1) : d196 p ≤ (0 : Int) + d2429 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d196, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14453 p hg
    simpa only [d196, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d196, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d196, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14455 (p : Pattern) (guard : d4902 p = 1) : d197 p ≤ (0 : Int) + d2430 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d197, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14448 p hg
    simpa only [d197, d2430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d197, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14454 p hg
    simpa only [d197, d2430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14456 (p : Pattern) (guard : d4902 p = 1) : d198 p ≤ (0 : Int) + d2431 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d198, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14218 p hg
    simpa only [d198, d2431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d198, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14261 p hg
    simpa only [d198, d2431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14457 (p : Pattern) (guard : d4902 p = 1) : d199 p ≤ (0 : Int) + d2432 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d199, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14253 p hg
    simpa only [d199, d2432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d199, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14456 p hg
    simpa only [d199, d2432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14458 (p : Pattern) (guard : d4902 p = 1) : d200 p ≤ (0 : Int) + d2433 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d200, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14457 p hg
    simpa only [d200, d2433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d200, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14288 p hg
    simpa only [d200, d2433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14459 (p : Pattern) (guard : d4902 p = 1) : d201 p ≤ (0 : Int) + d2434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d201, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14451 p hg
    simpa only [d201, d2434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d201, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d201, d2434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14460 (p : Pattern) (guard : d4902 p = 1) : d202 p ≤ (0 : Int) + d2435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d202, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14459 p hg
    simpa only [d202, d2435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d202, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d202, d2435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14461 (p : Pattern) (guard : d4902 p = 1) : d203 p ≤ (0 : Int) + d2436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d203, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14460 p hg
    simpa only [d203, d2436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d203, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d203, d2436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14462 (p : Pattern) (guard : d4902 p = 1) : d204 p ≤ (0 : Int) + d2437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d204, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14458 p hg
    simpa only [d204, d2437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d204, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14461 p hg
    simpa only [d204, d2437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14463 (p : Pattern) (guard : d4902 p = 1) : d205 p ≤ (0 : Int) + d2438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d205, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14455 p hg
    simpa only [d205, d2438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d205, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14462 p hg
    simpa only [d205, d2438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14464 (p : Pattern) (guard : d4902 p = 1) : d206 p ≤ (0 : Int) + d2439 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d206, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14446 p hg
    simpa only [d206, d2439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d206, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14463 p hg
    simpa only [d206, d2439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14465 (p : Pattern) (guard : d4902 p = 1) : d207 p ≤ (0 : Int) + d2440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d207, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14463 p hg
    simpa only [d207, d2440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d207, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d207, d2440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14466 (p : Pattern) (guard : d4902 p = 1) : d208 p ≤ (0 : Int) + d2441 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d208, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14464 p hg
    simpa only [d208, d2441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d208, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14465 p hg
    simpa only [d208, d2441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14467 (p : Pattern) (guard : d4902 p = 1) : d209 p ≤ (0 : Int) + d2442 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d209, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14333 p hg
    simpa only [d209, d2442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d209, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14466 p hg
    simpa only [d209, d2442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14468 (p : Pattern) (guard : d4902 p = 1) : d210 p ≤ (0 : Int) + d2443 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d210, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14317 p hg
    simpa only [d210, d2443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d210, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14467 p hg
    simpa only [d210, d2443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14469 (p : Pattern) (guard : d4902 p = 1) : d211 p ≤ (0 : Int) + d2444 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d211, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14354 p hg
    simpa only [d211, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d211, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d211, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14470 (p : Pattern) (guard : d4902 p = 1) : d212 p ≤ (0 : Int) + d2445 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d212, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14380 p hg
    simpa only [d212, d2445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d212, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14469 p hg
    simpa only [d212, d2445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14471 (p : Pattern) (guard : d4902 p = 1) : d213 p ≤ (0 : Int) + d2446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d213, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14469 p hg
    simpa only [d213, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d213, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d213, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14472 (p : Pattern) (guard : d4902 p = 1) : d214 p ≤ (0 : Int) + d2447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d214, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14470 p hg
    simpa only [d214, d2447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d214, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14471 p hg
    simpa only [d214, d2447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14473 (p : Pattern) (guard : d4902 p = 1) : d215 p ≤ (0 : Int) + d2448 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d215, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14368 p hg
    simpa only [d215, d2448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d215, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d215, d2448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14474 (p : Pattern) (guard : d4902 p = 1) : d216 p ≤ (0 : Int) + d2449 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d216, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14387 p hg
    simpa only [d216, d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d216, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14473 p hg
    simpa only [d216, d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14475 (p : Pattern) (guard : d4902 p = 1) : d217 p ≤ (0 : Int) + d2450 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d217, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14473 p hg
    simpa only [d217, d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d217, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d217, d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14476 (p : Pattern) (guard : d4902 p = 1) : d218 p ≤ (0 : Int) + d2451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d218, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14474 p hg
    simpa only [d218, d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d218, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14475 p hg
    simpa only [d218, d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14477 (p : Pattern) (guard : d4902 p = 1) : d219 p ≤ (0 : Int) + d2452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d219, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14472 p hg
    simpa only [d219, d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d219, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14476 p hg
    simpa only [d219, d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14478 (p : Pattern) (guard : d4902 p = 1) : d220 p ≤ (0 : Int) + d2453 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d220, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14374 p hg
    simpa only [d220, d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d220, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14477 p hg
    simpa only [d220, d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14479 (p : Pattern) (guard : d4902 p = 1) : d212 p ≤ (0 : Int) + d2454 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d212, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14402 p hg
    simpa only [d212, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d212, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14469 p hg
    simpa only [d212, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14480 (p : Pattern) (guard : d4902 p = 1) : d214 p ≤ (0 : Int) + d2455 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d214, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14479 p hg
    simpa only [d214, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d214, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14471 p hg
    simpa only [d214, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14481 (p : Pattern) (guard : d4902 p = 1) : d221 p ≤ (0 : Int) + d2456 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d221, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14480 p hg
    simpa only [d221, d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d221, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14407 p hg
    simpa only [d221, d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14482 (p : Pattern) (guard : d4902 p = 1) : d222 p ≤ (0 : Int) + d2457 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d222, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14401 p hg
    simpa only [d222, d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d222, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14481 p hg
    simpa only [d222, d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14483 (p : Pattern) (guard : d4902 p = 1) : d223 p ≤ (0 : Int) + d2458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d223, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14478 p hg
    simpa only [d223, d2458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d223, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14482 p hg
    simpa only [d223, d2458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14484 (p : Pattern) (guard : d4902 p = 1) : d224 p ≤ (0 : Int) + d2459 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d224, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14482 p hg
    simpa only [d224, d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d224, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14414 p hg
    simpa only [d224, d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14485 (p : Pattern) (guard : d4902 p = 1) : d225 p ≤ (0 : Int) + d2460 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d225, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14483 p hg
    simpa only [d225, d2460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d225, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14484 p hg
    simpa only [d225, d2460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14486 (p : Pattern) (guard : d4902 p = 1) : d226 p ≤ (0 : Int) + d2461 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d226, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14360 p hg
    simpa only [d226, d2461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d226, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14364 p hg
    simpa only [d226, d2461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14487 (p : Pattern) (guard : d4902 p = 1) : d227 p ≤ (0 : Int) + d2462 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d227, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14379 p hg
    simpa only [d227, d2462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d227, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14486 p hg
    simpa only [d227, d2462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14488 (p : Pattern) (guard : d4902 p = 1) : d228 p ≤ (0 : Int) + d2463 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d228, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14487 p hg
    simpa only [d228, d2463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d228, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14473 p hg
    simpa only [d228, d2463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14489 (p : Pattern) (guard : d4902 p = 1) : d229 p ≤ (0 : Int) + d2464 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d229, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14363 p hg
    simpa only [d229, d2464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d229, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d229, d2464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14490 (p : Pattern) (guard : d4902 p = 1) : d230 p ≤ (0 : Int) + d2465 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d230, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14489 p hg
    simpa only [d230, d2465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d230, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d230, d2465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14491 (p : Pattern) (guard : d4902 p = 1) : d231 p ≤ (0 : Int) + d2466 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d231, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14490 p hg
    simpa only [d231, d2466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d231, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d231, d2466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14492 (p : Pattern) (guard : d4902 p = 1) : d232 p ≤ (0 : Int) + d2467 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d232, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14488 p hg
    simpa only [d232, d2467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d232, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14491 p hg
    simpa only [d232, d2467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14493 (p : Pattern) (guard : d4902 p = 1) : d233 p ≤ (0 : Int) + d2468 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d233, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14419 p hg
    simpa only [d233, d2468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d233, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14492 p hg
    simpa only [d233, d2468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14494 (p : Pattern) (guard : d4902 p = 1) : d234 p ≤ (0 : Int) + d2469 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d234, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14352 p hg
    simpa only [d234, d2469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d234, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14364 p hg
    simpa only [d234, d2469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14495 (p : Pattern) (guard : d4902 p = 1) : d235 p ≤ (0 : Int) + d2470 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d235, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14494 p hg
    simpa only [d235, d2470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d235, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14368 p hg
    simpa only [d235, d2470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14496 (p : Pattern) (guard : d4902 p = 1) : d236 p ≤ (0 : Int) + d2471 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d236, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14495 p hg
    simpa only [d236, d2471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d236, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14490 p hg
    simpa only [d236, d2471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14497 (p : Pattern) (guard : d4902 p = 1) : d237 p ≤ (0 : Int) + d2472 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d237, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14245 p hg
    simpa only [d237, d2472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d237, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d237, d2472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14498 (p : Pattern) (guard : d4902 p = 1) : d238 p ≤ (0 : Int) + d2473 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d238, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14496 p hg
    simpa only [d238, d2473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d238, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14497 p hg
    simpa only [d238, d2473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14499 (p : Pattern) (guard : d4902 p = 1) : d239 p ≤ (0 : Int) + d2474 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d239, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14480 p hg
    simpa only [d239, d2474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d239, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14498 p hg
    simpa only [d239, d2474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14500 (p : Pattern) (guard : d4902 p = 1) : d240 p ≤ (0 : Int) + d2475 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d240, d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14493 p hg
    simpa only [d240, d2475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d240, d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14499 p hg
    simpa only [d240, d2475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14501 (p : Pattern) (guard : d4902 p = 1) : d241 p ≤ (0 : Int) + d2476 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d241, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14379 p hg
    simpa only [d241, d2476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d241, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14261 p hg
    simpa only [d241, d2476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14502 (p : Pattern) (guard : d4902 p = 1) : d242 p ≤ (0 : Int) + d2477 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d242, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14351 p hg
    simpa only [d242, d2477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d242, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14501 p hg
    simpa only [d242, d2477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14503 (p : Pattern) (guard : d4902 p = 1) : d243 p ≤ (0 : Int) + d2478 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d243, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14502 p hg
    simpa only [d243, d2478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d243, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14384 p hg
    simpa only [d243, d2478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14504 (p : Pattern) (guard : d4902 p = 1) : d244 p ≤ (0 : Int) + d2479 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d244, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14503 p hg
    simpa only [d244, d2479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d244, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14407 p hg
    simpa only [d244, d2479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14505 (p : Pattern) (guard : d4902 p = 1) : d245 p ≤ (0 : Int) + d2480 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d245, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14379 p hg
    simpa only [d245, d2480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d245, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14469 p hg
    simpa only [d245, d2480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14506 (p : Pattern) (guard : d4902 p = 1) : d246 p ≤ (0 : Int) + d2481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d246, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14505 p hg
    simpa only [d246, d2481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d246, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14406 p hg
    simpa only [d246, d2481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14507 (p : Pattern) (guard : d4902 p = 1) : d247 p ≤ (0 : Int) + d2482 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d247, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14226 p hg
    simpa only [d247, d2482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d247, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d247, d2482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14508 (p : Pattern) (guard : d4902 p = 1) : d248 p ≤ (0 : Int) + d2483 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d248, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14507 p hg
    simpa only [d248, d2483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d248, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d248, d2483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14509 (p : Pattern) (guard : d4902 p = 1) : d249 p ≤ (0 : Int) + d2484 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d249, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14506 p hg
    simpa only [d249, d2484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d249, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14508 p hg
    simpa only [d249, d2484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14510 (p : Pattern) (guard : d4902 p = 1) : d250 p ≤ (0 : Int) + d2485 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d250, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14504 p hg
    simpa only [d250, d2485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d250, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14509 p hg
    simpa only [d250, d2485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14511 (p : Pattern) (guard : d4902 p = 1) : d251 p ≤ (0 : Int) + d2486 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d251, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14500 p hg
    simpa only [d251, d2486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d251, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14510 p hg
    simpa only [d251, d2486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14512 (p : Pattern) (guard : d4902 p = 1) : d252 p ≤ (0 : Int) + d2487 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d252, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14379 p hg
    simpa only [d252, d2487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d252, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14225 p hg
    simpa only [d252, d2487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14513 (p : Pattern) (guard : d4902 p = 1) : d253 p ≤ (0 : Int) + d2488 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d253, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14351 p hg
    simpa only [d253, d2488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d253, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14512 p hg
    simpa only [d253, d2488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14514 (p : Pattern) (guard : d4902 p = 1) : d254 p ≤ (0 : Int) + d2489 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d254, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14354 p hg
    simpa only [d254, d2489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d254, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14225 p hg
    simpa only [d254, d2489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14515 (p : Pattern) (guard : d4902 p = 1) : d255 p ≤ (0 : Int) + d2490 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d255, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14514 p hg
    simpa only [d255, d2490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d255, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d255, d2490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14516 (p : Pattern) (guard : d4902 p = 1) : d256 p ≤ (0 : Int) + d2491 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d256, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14513 p hg
    simpa only [d256, d2491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d256, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14515 p hg
    simpa only [d256, d2491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14517 (p : Pattern) (guard : d4902 p = 1) : d257 p ≤ (0 : Int) + d2492 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d257, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14397 p hg
    simpa only [d257, d2492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d257, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14261 p hg
    simpa only [d257, d2492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14518 (p : Pattern) (guard : d4902 p = 1) : d258 p ≤ (0 : Int) + d2493 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d258, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14517 p hg
    simpa only [d258, d2493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d258, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d258, d2493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14519 (p : Pattern) (guard : d4902 p = 1) : d259 p ≤ (0 : Int) + d2494 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d259, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14518 p hg
    simpa only [d259, d2494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d259, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d259, d2494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14520 (p : Pattern) (guard : d4902 p = 1) : d260 p ≤ (0 : Int) + d2495 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d260, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14516 p hg
    simpa only [d260, d2495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d260, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14519 p hg
    simpa only [d260, d2495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14521 (p : Pattern) (guard : d4902 p = 1) : d261 p ≤ (0 : Int) + d2496 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d261, d2496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14520 p hg
    simpa only [d261, d2496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d261, d2496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14509 p hg
    simpa only [d261, d2496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14522 (p : Pattern) (guard : d4902 p = 1) : d262 p ≤ (0 : Int) + d2497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d262, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14521 p hg
    simpa only [d262, d2497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d262, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d262, d2497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14523 (p : Pattern) (guard : d4902 p = 1) : d263 p ≤ (0 : Int) + d2498 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d263, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14511 p hg
    simpa only [d263, d2498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d263, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14522 p hg
    simpa only [d263, d2498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14524 (p : Pattern) (guard : d4902 p = 1) : d264 p ≤ (0 : Int) + d2499 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d264, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14485 p hg
    simpa only [d264, d2499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d264, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14523 p hg
    simpa only [d264, d2499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14525 (p : Pattern) (guard : d4902 p = 1) : d265 p ≤ (0 : Int) + d2500 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d265, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14317 p hg
    simpa only [d265, d2500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d265, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14524 p hg
    simpa only [d265, d2500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14526 (p : Pattern) (guard : d4902 p = 1) : d266 p ≤ (0 : Int) + d2501 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d266, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14468 p hg
    simpa only [d266, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d266, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14525 p hg
    simpa only [d266, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14527 (p : Pattern) (guard : d4902 p = 1) : d267 p ≤ (0 : Int) + d2502 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d267, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14428 p hg
    simpa only [d267, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d267, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14526 p hg
    simpa only [d267, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14528 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14529 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14530 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14531 (p : Pattern) (guard : d5268 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14529 p hg
    simpa only [d5268, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14530 p hg
    simpa only [d5268, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14532 (p : Pattern) (guard : d5269 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14528 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14531 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14533 (p : Pattern) (guard : d5269 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare14534 (p : Pattern) (guard : d5269 p = 1) : d15 p ≤ (0 : Int) + d5270 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d15, d5270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14532 p hg
    simpa only [d15, d5270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d15, d5270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d15, d5270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14535 (p : Pattern) (guard : d5269 p = 1) : d16 p ≤ (0 : Int) + d5271 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d16, d5271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14532 p hg
    simpa only [d16, d5271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d16, d5271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14534 p hg
    simpa only [d16, d5271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14536 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14537 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  omega
theorem compare14538 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14539 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14540 (p : Pattern) (guard : d5268 p = 1) : d18 p ≤ (0 : Int) + d17 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14538 p hg
    simpa only [d5268, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14539 p hg
    simpa only [d5268, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14541 (p : Pattern) (guard : d5269 p = 1) : d18 p ≤ (0 : Int) + d17 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14536 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14540 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14542 (p : Pattern) (guard : d5269 p = 1) : d19 p ≤ (0 : Int) + d5272 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d19, d5272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14541 p hg
    simpa only [d19, d5272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d19, d5272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d19, d5272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14543 (p : Pattern) (guard : d5269 p = 1) : d20 p ≤ (0 : Int) + d5273 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d20, d5273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14541 p hg
    simpa only [d20, d5273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d20, d5273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14542 p hg
    simpa only [d20, d5273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14544 (p : Pattern) (guard : d5269 p = 1) : d21 p ≤ (0 : Int) + d5274 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d21, d5274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14535 p hg
    simpa only [d21, d5274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d21, d5274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14543 p hg
    simpa only [d21, d5274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14545 (p : Pattern) (guard : d5269 p = 1) : d22 p ≤ (0 : Int) + d5275 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d22, d5275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14535 p hg
    simpa only [d22, d5275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d22, d5275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14544 p hg
    simpa only [d22, d5275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14546 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14547 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  omega
theorem compare14548 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14549 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14550 (p : Pattern) (guard : d5268 p = 1) : d24 p ≤ (0 : Int) + d23 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14548 p hg
    simpa only [d5268, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14549 p hg
    simpa only [d5268, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14551 (p : Pattern) (guard : d5269 p = 1) : d24 p ≤ (0 : Int) + d23 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14546 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14550 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14552 (p : Pattern) (guard : d5269 p = 1) : d25 p ≤ (0 : Int) + d5276 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d25, d5276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14551 p hg
    simpa only [d25, d5276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d25, d5276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d25, d5276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14553 (p : Pattern) (guard : d5269 p = 1) : d26 p ≤ (0 : Int) + d5277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d26, d5277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14551 p hg
    simpa only [d26, d5277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d26, d5277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14552 p hg
    simpa only [d26, d5277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14554 (p : Pattern) (guard : d5269 p = 1) : d27 p ≤ (0 : Int) + d5278 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d27, d5278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14553 p hg
    simpa only [d27, d5278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d27, d5278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d27, d5278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14555 (p : Pattern) (guard : d5269 p = 1) : d28 p ≤ (0 : Int) + d5279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d28, d5279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14544 p hg
    simpa only [d28, d5279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d28, d5279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14554 p hg
    simpa only [d28, d5279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14556 (p : Pattern) (guard : d5269 p = 1) : d29 p ≤ (0 : Int) + d5280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d29, d5280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14545 p hg
    simpa only [d29, d5280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d29, d5280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14555 p hg
    simpa only [d29, d5280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14557 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14558 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare14559 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
