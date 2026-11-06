/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons191
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26880 (p : Pattern) (guard : d5539 p = 1) : d3450 p ≤ (0 : Int) + d2413 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3450, d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26720 p hg
    simpa only [d3450, d2413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3450, d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26879 p hg
    simpa only [d3450, d2413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26881 (p : Pattern) (guard : d5539 p = 1) : d3451 p ≤ (0 : Int) + d2414 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3451, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26871 p hg
    simpa only [d3451, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3451, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26659 p hg
    simpa only [d3451, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26882 (p : Pattern) (guard : d5539 p = 1) : d3452 p ≤ (0 : Int) + d2415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3452, d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26874 p hg
    simpa only [d3452, d2415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3452, d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26696 p hg
    simpa only [d3452, d2415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26883 (p : Pattern) (guard : d5539 p = 1) : d3453 p ≤ (0 : Int) + d2416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3453, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26881 p hg
    simpa only [d3453, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3453, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26882 p hg
    simpa only [d3453, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26884 (p : Pattern) (guard : d5539 p = 1) : d3454 p ≤ (0 : Int) + d2417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3454, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26874 p hg
    simpa only [d3454, d2417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3454, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3454, d2417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26885 (p : Pattern) (guard : d5539 p = 1) : d3455 p ≤ (0 : Int) + d2418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3455, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26884 p hg
    simpa only [d3455, d2418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3455, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3455, d2418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26886 (p : Pattern) (guard : d5539 p = 1) : d3456 p ≤ (0 : Int) + d2419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3456, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26883 p hg
    simpa only [d3456, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3456, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26885 p hg
    simpa only [d3456, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26887 (p : Pattern) (guard : d5539 p = 1) : d3457 p ≤ (0 : Int) + d2420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3457, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26711 p hg
    simpa only [d3457, d2420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3457, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26886 p hg
    simpa only [d3457, d2420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26888 (p : Pattern) (guard : d5539 p = 1) : d3458 p ≤ (0 : Int) + d2421 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3458, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26880 p hg
    simpa only [d3458, d2421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3458, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26887 p hg
    simpa only [d3458, d2421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26889 (p : Pattern) (guard : d5539 p = 1) : d3459 p ≤ (0 : Int) + d2422 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3459, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26633 p hg
    simpa only [d3459, d2422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3459, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26705 p hg
    simpa only [d3459, d2422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26890 (p : Pattern) (guard : d5539 p = 1) : d3460 p ≤ (0 : Int) + d2423 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3460, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26889 p hg
    simpa only [d3460, d2423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3460, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26706 p hg
    simpa only [d3460, d2423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26891 (p : Pattern) (guard : d5268 p = 1) : d3461 p ≤ (0 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14750 p hg
    simpa only [d5268, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5268, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26892 (p : Pattern) (guard : d0 p = 1) : d3461 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26893 (p : Pattern) (guard : d5539 p = 1) : d3461 p ≤ (0 : Int) + d2424 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5539, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26891 p hg
    simpa only [d5539, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5539, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26892 p hg
    simpa only [d5539, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26894 (p : Pattern) (guard : d5539 p = 1) : d3462 p ≤ (0 : Int) + d2425 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3462, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26893 p hg
    simpa only [d3462, d2425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3462, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3462, d2425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26895 (p : Pattern) (guard : d5539 p = 1) : d3463 p ≤ (0 : Int) + d2426 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3463, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26893 p hg
    simpa only [d3463, d2426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3463, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26894 p hg
    simpa only [d3463, d2426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26896 (p : Pattern) (guard : d5539 p = 1) : d3464 p ≤ (0 : Int) + d2427 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3464, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26630 p hg
    simpa only [d3464, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3464, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26895 p hg
    simpa only [d3464, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26897 (p : Pattern) (guard : d5539 p = 1) : d3465 p ≤ (0 : Int) + d2428 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3465, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26896 p hg
    simpa only [d3465, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3465, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3465, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26898 (p : Pattern) (guard : d5539 p = 1) : d3466 p ≤ (0 : Int) + d2429 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3466, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26897 p hg
    simpa only [d3466, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3466, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3466, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26899 (p : Pattern) (guard : d5539 p = 1) : d3467 p ≤ (0 : Int) + d2430 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3467, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26890 p hg
    simpa only [d3467, d2430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3467, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26898 p hg
    simpa only [d3467, d2430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26900 (p : Pattern) (guard : d5539 p = 1) : d3468 p ≤ (0 : Int) + d2431 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3468, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26630 p hg
    simpa only [d3468, d2431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3468, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26686 p hg
    simpa only [d3468, d2431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26901 (p : Pattern) (guard : d5539 p = 1) : d3469 p ≤ (0 : Int) + d2432 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3469, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26676 p hg
    simpa only [d3469, d2432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3469, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26900 p hg
    simpa only [d3469, d2432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26902 (p : Pattern) (guard : d5539 p = 1) : d3470 p ≤ (0 : Int) + d2433 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3470, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26901 p hg
    simpa only [d3470, d2433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3470, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26713 p hg
    simpa only [d3470, d2433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26903 (p : Pattern) (guard : d5539 p = 1) : d3471 p ≤ (0 : Int) + d2434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3471, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26895 p hg
    simpa only [d3471, d2434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3471, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3471, d2434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26904 (p : Pattern) (guard : d5539 p = 1) : d3472 p ≤ (0 : Int) + d2435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3472, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26903 p hg
    simpa only [d3472, d2435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3472, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3472, d2435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26905 (p : Pattern) (guard : d5539 p = 1) : d3473 p ≤ (0 : Int) + d2436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3473, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26904 p hg
    simpa only [d3473, d2436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3473, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3473, d2436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26906 (p : Pattern) (guard : d5539 p = 1) : d3474 p ≤ (0 : Int) + d2437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3474, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26902 p hg
    simpa only [d3474, d2437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3474, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26905 p hg
    simpa only [d3474, d2437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26907 (p : Pattern) (guard : d5539 p = 1) : d3475 p ≤ (0 : Int) + d2438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3475, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26899 p hg
    simpa only [d3475, d2438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3475, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26906 p hg
    simpa only [d3475, d2438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26908 (p : Pattern) (guard : d5539 p = 1) : d3476 p ≤ (0 : Int) + d2439 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3476, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26888 p hg
    simpa only [d3476, d2439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3476, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26907 p hg
    simpa only [d3476, d2439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26909 (p : Pattern) (guard : d5539 p = 1) : d3477 p ≤ (0 : Int) + d2440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3477, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26907 p hg
    simpa only [d3477, d2440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3477, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3477, d2440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26910 (p : Pattern) (guard : d5539 p = 1) : d3478 p ≤ (0 : Int) + d2441 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3478, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26908 p hg
    simpa only [d3478, d2441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3478, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26909 p hg
    simpa only [d3478, d2441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26911 (p : Pattern) (guard : d5539 p = 1) : d3479 p ≤ (0 : Int) + d2442 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3479, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26761 p hg
    simpa only [d3479, d2442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3479, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26910 p hg
    simpa only [d3479, d2442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26912 (p : Pattern) (guard : d5539 p = 1) : d3480 p ≤ (0 : Int) + d2443 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3480, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26742 p hg
    simpa only [d3480, d2443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3480, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26911 p hg
    simpa only [d3480, d2443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26913 (p : Pattern) (guard : d5539 p = 1) : d3481 p ≤ (0 : Int) + d2444 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3481, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26789 p hg
    simpa only [d3481, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3481, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3481, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26914 (p : Pattern) (guard : d5539 p = 1) : d3482 p ≤ (0 : Int) + d2445 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3482, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26822 p hg
    simpa only [d3482, d2445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3482, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26913 p hg
    simpa only [d3482, d2445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26915 (p : Pattern) (guard : d5539 p = 1) : d3483 p ≤ (0 : Int) + d2446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3483, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26913 p hg
    simpa only [d3483, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3483, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3483, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26916 (p : Pattern) (guard : d5539 p = 1) : d3484 p ≤ (0 : Int) + d2447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3484, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26914 p hg
    simpa only [d3484, d2447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3484, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26915 p hg
    simpa only [d3484, d2447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26917 (p : Pattern) (guard : d5539 p = 1) : d3485 p ≤ (0 : Int) + d2448 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3485, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26807 p hg
    simpa only [d3485, d2448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3485, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3485, d2448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26918 (p : Pattern) (guard : d5539 p = 1) : d3486 p ≤ (0 : Int) + d2449 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3486, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26829 p hg
    simpa only [d3486, d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3486, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26917 p hg
    simpa only [d3486, d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26919 (p : Pattern) (guard : d5539 p = 1) : d3487 p ≤ (0 : Int) + d2450 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3487, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26917 p hg
    simpa only [d3487, d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3487, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3487, d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26920 (p : Pattern) (guard : d5539 p = 1) : d3488 p ≤ (0 : Int) + d2451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3488, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26918 p hg
    simpa only [d3488, d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3488, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26919 p hg
    simpa only [d3488, d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26921 (p : Pattern) (guard : d5539 p = 1) : d3489 p ≤ (0 : Int) + d2452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3489, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26916 p hg
    simpa only [d3489, d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3489, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26920 p hg
    simpa only [d3489, d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26922 (p : Pattern) (guard : d5539 p = 1) : d3490 p ≤ (0 : Int) + d2453 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3490, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26813 p hg
    simpa only [d3490, d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3490, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26921 p hg
    simpa only [d3490, d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26923 (p : Pattern) (guard : d5539 p = 1) : d3491 p ≤ (0 : Int) + d2454 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3491, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26844 p hg
    simpa only [d3491, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3491, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26913 p hg
    simpa only [d3491, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26924 (p : Pattern) (guard : d5539 p = 1) : d3492 p ≤ (0 : Int) + d2455 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3492, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26923 p hg
    simpa only [d3492, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3492, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26915 p hg
    simpa only [d3492, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26925 (p : Pattern) (guard : d5539 p = 1) : d3493 p ≤ (0 : Int) + d2456 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3493, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26924 p hg
    simpa only [d3493, d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3493, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26849 p hg
    simpa only [d3493, d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26926 (p : Pattern) (guard : d5539 p = 1) : d3494 p ≤ (0 : Int) + d2457 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3494, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26843 p hg
    simpa only [d3494, d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3494, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26925 p hg
    simpa only [d3494, d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26927 (p : Pattern) (guard : d5539 p = 1) : d3495 p ≤ (0 : Int) + d2458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3495, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26922 p hg
    simpa only [d3495, d2458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3495, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26926 p hg
    simpa only [d3495, d2458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26928 (p : Pattern) (guard : d5539 p = 1) : d3496 p ≤ (0 : Int) + d2459 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3496, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26926 p hg
    simpa only [d3496, d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3496, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26856 p hg
    simpa only [d3496, d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26929 (p : Pattern) (guard : d5539 p = 1) : d3497 p ≤ (0 : Int) + d2460 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3497, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26927 p hg
    simpa only [d3497, d2460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3497, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26928 p hg
    simpa only [d3497, d2460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26930 (p : Pattern) (guard : d5539 p = 1) : d3498 p ≤ (0 : Int) + d2461 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3498, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26797 p hg
    simpa only [d3498, d2461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3498, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26803 p hg
    simpa only [d3498, d2461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26931 (p : Pattern) (guard : d5539 p = 1) : d3499 p ≤ (0 : Int) + d2462 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3499, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26821 p hg
    simpa only [d3499, d2462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3499, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26930 p hg
    simpa only [d3499, d2462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26932 (p : Pattern) (guard : d5539 p = 1) : d3500 p ≤ (0 : Int) + d2463 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3500, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26931 p hg
    simpa only [d3500, d2463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3500, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26917 p hg
    simpa only [d3500, d2463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26933 (p : Pattern) (guard : d5539 p = 1) : d3501 p ≤ (0 : Int) + d2464 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3501, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26802 p hg
    simpa only [d3501, d2464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3501, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3501, d2464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26934 (p : Pattern) (guard : d5539 p = 1) : d3502 p ≤ (0 : Int) + d2465 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3502, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26933 p hg
    simpa only [d3502, d2465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3502, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3502, d2465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26935 (p : Pattern) (guard : d5539 p = 1) : d3503 p ≤ (0 : Int) + d2466 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3503, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26934 p hg
    simpa only [d3503, d2466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3503, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3503, d2466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26936 (p : Pattern) (guard : d5539 p = 1) : d3504 p ≤ (0 : Int) + d2467 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3504, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26932 p hg
    simpa only [d3504, d2467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3504, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26935 p hg
    simpa only [d3504, d2467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26937 (p : Pattern) (guard : d5539 p = 1) : d3505 p ≤ (0 : Int) + d2468 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3505, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26861 p hg
    simpa only [d3505, d2468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3505, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26936 p hg
    simpa only [d3505, d2468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26938 (p : Pattern) (guard : d5539 p = 1) : d3506 p ≤ (0 : Int) + d2469 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3506, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26787 p hg
    simpa only [d3506, d2469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3506, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26803 p hg
    simpa only [d3506, d2469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26939 (p : Pattern) (guard : d5539 p = 1) : d3507 p ≤ (0 : Int) + d2470 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3507, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26938 p hg
    simpa only [d3507, d2470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3507, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26807 p hg
    simpa only [d3507, d2470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26940 (p : Pattern) (guard : d5539 p = 1) : d3508 p ≤ (0 : Int) + d2471 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3508, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26939 p hg
    simpa only [d3508, d2471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3508, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26934 p hg
    simpa only [d3508, d2471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26941 (p : Pattern) (guard : d5539 p = 1) : d3509 p ≤ (0 : Int) + d2472 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3509, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26665 p hg
    simpa only [d3509, d2472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3509, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3509, d2472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26942 (p : Pattern) (guard : d5539 p = 1) : d3510 p ≤ (0 : Int) + d2473 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3510, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26940 p hg
    simpa only [d3510, d2473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3510, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26941 p hg
    simpa only [d3510, d2473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26943 (p : Pattern) (guard : d5539 p = 1) : d3511 p ≤ (0 : Int) + d2474 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3511, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26924 p hg
    simpa only [d3511, d2474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3511, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26942 p hg
    simpa only [d3511, d2474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26944 (p : Pattern) (guard : d5539 p = 1) : d3512 p ≤ (0 : Int) + d2475 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3512, d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26937 p hg
    simpa only [d3512, d2475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3512, d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26943 p hg
    simpa only [d3512, d2475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26945 (p : Pattern) (guard : d5539 p = 1) : d3513 p ≤ (0 : Int) + d2476 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3513, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26821 p hg
    simpa only [d3513, d2476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3513, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26686 p hg
    simpa only [d3513, d2476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26946 (p : Pattern) (guard : d5539 p = 1) : d3514 p ≤ (0 : Int) + d2477 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3514, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26784 p hg
    simpa only [d3514, d2477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3514, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26945 p hg
    simpa only [d3514, d2477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26947 (p : Pattern) (guard : d5539 p = 1) : d3515 p ≤ (0 : Int) + d2478 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3515, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26946 p hg
    simpa only [d3515, d2478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3515, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26826 p hg
    simpa only [d3515, d2478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26948 (p : Pattern) (guard : d5539 p = 1) : d3516 p ≤ (0 : Int) + d2479 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3516, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26947 p hg
    simpa only [d3516, d2479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3516, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26849 p hg
    simpa only [d3516, d2479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26949 (p : Pattern) (guard : d5539 p = 1) : d3517 p ≤ (0 : Int) + d2480 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3517, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26821 p hg
    simpa only [d3517, d2480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3517, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26913 p hg
    simpa only [d3517, d2480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26950 (p : Pattern) (guard : d5539 p = 1) : d3518 p ≤ (0 : Int) + d2481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3518, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26949 p hg
    simpa only [d3518, d2481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3518, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26848 p hg
    simpa only [d3518, d2481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26951 (p : Pattern) (guard : d5539 p = 1) : d3519 p ≤ (0 : Int) + d2482 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3519, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26640 p hg
    simpa only [d3519, d2482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3519, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3519, d2482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26952 (p : Pattern) (guard : d5539 p = 1) : d3520 p ≤ (0 : Int) + d2483 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3520, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26951 p hg
    simpa only [d3520, d2483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3520, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3520, d2483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26953 (p : Pattern) (guard : d5539 p = 1) : d3521 p ≤ (0 : Int) + d2484 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3521, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26950 p hg
    simpa only [d3521, d2484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3521, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26952 p hg
    simpa only [d3521, d2484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26954 (p : Pattern) (guard : d5539 p = 1) : d3522 p ≤ (0 : Int) + d2485 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3522, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26948 p hg
    simpa only [d3522, d2485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3522, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26953 p hg
    simpa only [d3522, d2485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26955 (p : Pattern) (guard : d5539 p = 1) : d3523 p ≤ (0 : Int) + d2486 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3523, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26944 p hg
    simpa only [d3523, d2486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3523, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26954 p hg
    simpa only [d3523, d2486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26956 (p : Pattern) (guard : d5539 p = 1) : d3524 p ≤ (0 : Int) + d2487 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3524, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26821 p hg
    simpa only [d3524, d2487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3524, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26639 p hg
    simpa only [d3524, d2487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26957 (p : Pattern) (guard : d5539 p = 1) : d3525 p ≤ (0 : Int) + d2488 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3525, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26784 p hg
    simpa only [d3525, d2488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3525, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26956 p hg
    simpa only [d3525, d2488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26958 (p : Pattern) (guard : d5539 p = 1) : d3526 p ≤ (0 : Int) + d2489 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3526, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26789 p hg
    simpa only [d3526, d2489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3526, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26639 p hg
    simpa only [d3526, d2489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26959 (p : Pattern) (guard : d5539 p = 1) : d3527 p ≤ (0 : Int) + d2490 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3527, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26958 p hg
    simpa only [d3527, d2490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3527, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3527, d2490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26960 (p : Pattern) (guard : d5539 p = 1) : d3528 p ≤ (0 : Int) + d2491 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3528, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26957 p hg
    simpa only [d3528, d2491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3528, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26959 p hg
    simpa only [d3528, d2491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26961 (p : Pattern) (guard : d5539 p = 1) : d3529 p ≤ (0 : Int) + d2492 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3529, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26839 p hg
    simpa only [d3529, d2492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3529, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26686 p hg
    simpa only [d3529, d2492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26962 (p : Pattern) (guard : d5539 p = 1) : d3530 p ≤ (0 : Int) + d2493 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3530, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26961 p hg
    simpa only [d3530, d2493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3530, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3530, d2493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26963 (p : Pattern) (guard : d5539 p = 1) : d3531 p ≤ (0 : Int) + d2494 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3531, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26962 p hg
    simpa only [d3531, d2494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3531, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3531, d2494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26964 (p : Pattern) (guard : d5539 p = 1) : d3532 p ≤ (0 : Int) + d2495 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3532, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26960 p hg
    simpa only [d3532, d2495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3532, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26963 p hg
    simpa only [d3532, d2495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26965 (p : Pattern) (guard : d5539 p = 1) : d3533 p ≤ (0 : Int) + d2496 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3533, d2496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26964 p hg
    simpa only [d3533, d2496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3533, d2496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26953 p hg
    simpa only [d3533, d2496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26966 (p : Pattern) (guard : d5539 p = 1) : d3534 p ≤ (0 : Int) + d2497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3534, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26965 p hg
    simpa only [d3534, d2497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3534, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d3534, d2497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26967 (p : Pattern) (guard : d5539 p = 1) : d3535 p ≤ (0 : Int) + d2498 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3535, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26955 p hg
    simpa only [d3535, d2498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3535, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26966 p hg
    simpa only [d3535, d2498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26968 (p : Pattern) (guard : d5539 p = 1) : d3536 p ≤ (0 : Int) + d2499 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3536, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26929 p hg
    simpa only [d3536, d2499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3536, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26967 p hg
    simpa only [d3536, d2499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26969 (p : Pattern) (guard : d5539 p = 1) : d3537 p ≤ (0 : Int) + d2500 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3537, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26742 p hg
    simpa only [d3537, d2500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3537, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26968 p hg
    simpa only [d3537, d2500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26970 (p : Pattern) (guard : d5539 p = 1) : d3538 p ≤ (0 : Int) + d2501 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3538, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26912 p hg
    simpa only [d3538, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3538, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26969 p hg
    simpa only [d3538, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26971 (p : Pattern) (guard : d5539 p = 1) : d3539 p ≤ (0 : Int) + d2502 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5539 p = 1 := by simpa only [d3539, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26870 p hg
    simpa only [d3539, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5539 p = 1 := by simpa only [d3539, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26970 p hg
    simpa only [d3539, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26972 (p : Pattern) (guard : d0 p = 1) : d3227 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26973 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26974 (p : Pattern) (guard : d5268 p = 1) : d3226 p ≤ (2 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d5268, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26973 p hg
    simpa only [d5268, d3226, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26975 (p : Pattern) (guard : d5269 p = 1) : d3228 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26972 p hg
    simpa only [d5269, d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26974 p hg
    simpa only [d5269, d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26976 (p : Pattern) (guard : d0 p = 1) : d3226 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26977 (p : Pattern) (guard : d5269 p = 1) : d3226 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26976 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26974 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26978 (p : Pattern) (guard : d5269 p = 1) : d3229 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26975 p hg
    simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26979 (p : Pattern) (guard : d5269 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare26980 (p : Pattern) (guard : d5269 p = 1) : d3230 p ≤ (2 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3230, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3230, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3230, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3230, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26981 (p : Pattern) (guard : d5269 p = 1) : d3231 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3231, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26978 p hg
    simpa only [d3231, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3231, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26980 p hg
    simpa only [d3231, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26982 (p : Pattern) (guard : d0 p = 1) : d3233 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26983 (p : Pattern) (guard : d5269 p = 1) : d3234 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26982 p hg
    simpa only [d5269, d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26974 p hg
    simpa only [d5269, d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26984 (p : Pattern) (guard : d5269 p = 1) : d3235 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26983 p hg
    simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26985 (p : Pattern) (guard : d5269 p = 1) : d3236 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3236, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26984 p hg
    simpa only [d3236, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3236, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26980 p hg
    simpa only [d3236, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26986 (p : Pattern) (guard : d5269 p = 1) : d3237 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26981 p hg
    simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26985 p hg
    simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26987 (p : Pattern) (guard : d5269 p = 1) : d3238 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3238, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3238, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3238, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26980 p hg
    simpa only [d3238, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26988 (p : Pattern) (guard : d0 p = 1) : d3239 p ≤ (2 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26989 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26990 (p : Pattern) (guard : d5268 p = 1) : d3239 p ≤ (2 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d5268, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26989 p hg
    simpa only [d5268, d3239, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26991 (p : Pattern) (guard : d5269 p = 1) : d3239 p ≤ (2 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26988 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26990 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26992 (p : Pattern) (guard : d5269 p = 1) : d3240 p ≤ (2 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3240, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26991 p hg
    simpa only [d3240, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3240, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3240, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26993 (p : Pattern) (guard : d5269 p = 1) : d3241 p ≤ (2 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3241, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26991 p hg
    simpa only [d3241, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3241, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26992 p hg
    simpa only [d3241, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26994 (p : Pattern) (guard : d5269 p = 1) : d3242 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3242, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26987 p hg
    simpa only [d3242, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3242, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26993 p hg
    simpa only [d3242, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26995 (p : Pattern) (guard : d5269 p = 1) : d3243 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3243, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26986 p hg
    simpa only [d3243, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3243, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26994 p hg
    simpa only [d3243, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26996 (p : Pattern) (guard : d0 p = 1) : d3244 p ≤ (2 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26997 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26998 (p : Pattern) (guard : d5268 p = 1) : d3244 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d5268, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26997 p hg
    simpa only [d5268, d3244, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26999 (p : Pattern) (guard : d5269 p = 1) : d3244 p ≤ (2 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26996 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26998 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27000 (p : Pattern) (guard : d5269 p = 1) : d3245 p ≤ (2 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3245, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26999 p hg
    simpa only [d3245, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3245, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3245, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27001 (p : Pattern) (guard : d5269 p = 1) : d3246 p ≤ (2 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3246, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26999 p hg
    simpa only [d3246, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3246, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27000 p hg
    simpa only [d3246, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27002 (p : Pattern) (guard : d5269 p = 1) : d3247 p ≤ (2 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3247, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27001 p hg
    simpa only [d3247, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3247, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3247, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27003 (p : Pattern) (guard : d5269 p = 1) : d3248 p ≤ (2 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3248, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26994 p hg
    simpa only [d3248, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3248, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27002 p hg
    simpa only [d3248, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27004 (p : Pattern) (guard : d5269 p = 1) : d3249 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3249, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26995 p hg
    simpa only [d3249, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3249, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27003 p hg
    simpa only [d3249, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27005 (p : Pattern) (guard : d0 p = 1) : d3250 p ≤ (2 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27006 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27007 (p : Pattern) (guard : d5268 p = 1) : d3250 p ≤ (2 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d5268, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27006 p hg
    simpa only [d5268, d3250, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27008 (p : Pattern) (guard : d5269 p = 1) : d3250 p ≤ (2 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27005 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27007 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27009 (p : Pattern) (guard : d5269 p = 1) : d3251 p ≤ (2 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3251, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27008 p hg
    simpa only [d3251, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3251, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3251, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27010 (p : Pattern) (guard : d5269 p = 1) : d3252 p ≤ (2 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3252, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3252, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3252, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27009 p hg
    simpa only [d3252, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27011 (p : Pattern) (guard : d0 p = 1) : d3253 p ≤ (2 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27012 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27013 (p : Pattern) (guard : d5268 p = 1) : d3253 p ≤ (2 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d5268, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27012 p hg
    simpa only [d5268, d3253, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27014 (p : Pattern) (guard : d5269 p = 1) : d3253 p ≤ (2 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27011 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27013 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27015 (p : Pattern) (guard : d5269 p = 1) : d3254 p ≤ (2 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3254, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27014 p hg
    simpa only [d3254, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3254, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3254, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27016 (p : Pattern) (guard : d5269 p = 1) : d3255 p ≤ (2 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3255, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3255, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3255, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27015 p hg
    simpa only [d3255, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27017 (p : Pattern) (guard : d5269 p = 1) : d3256 p ≤ (2 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3256, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27010 p hg
    simpa only [d3256, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3256, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27016 p hg
    simpa only [d3256, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27018 (p : Pattern) (guard : d0 p = 1) : d3257 p ≤ (2 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27019 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d39 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
