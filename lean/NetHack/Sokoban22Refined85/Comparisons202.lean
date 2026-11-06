/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons201
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28280 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6867 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27927 p hg
    simpa only [d6867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27925 p hg
    simpa only [d6867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28281 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6868 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27926 p hg
    simpa only [d6868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28280 p hg
    simpa only [d6868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28282 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6869 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27924 p hg
    simpa only [d6869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28281 p hg
    simpa only [d6869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28283 (p : Pattern) (guard : d6558 p = 1) : d3251 p ≤ (0 : Int) + d6870 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3251, d6870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27973 p hg
    simpa only [d3251, d6870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3251, d6870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3251, d6870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28284 (p : Pattern) (guard : d6558 p = 1) : d3275 p ≤ (0 : Int) + d6871 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3275, d6871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28282 p hg
    simpa only [d3275, d6871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3275, d6871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28283 p hg
    simpa only [d3275, d6871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28285 (p : Pattern) (guard : d6558 p = 1) : d3306 p ≤ (0 : Int) + d6872 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3306, d6872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28014 p hg
    simpa only [d3306, d6872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3306, d6872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28284 p hg
    simpa only [d3306, d6872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28286 (p : Pattern) (guard : d6558 p = 1) : d3277 p ≤ (0 : Int) + d6873 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3277, d6873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28265 p hg
    simpa only [d3277, d6873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3277, d6873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28028 p hg
    simpa only [d3277, d6873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28287 (p : Pattern) (guard : d6558 p = 1) : d3307 p ≤ (0 : Int) + d6874 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3307, d6874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28285 p hg
    simpa only [d3307, d6874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3307, d6874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28286 p hg
    simpa only [d3307, d6874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28288 (p : Pattern) (guard : d6558 p = 1) : d3282 p ≤ (0 : Int) + d6875 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3282, d6875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28265 p hg
    simpa only [d3282, d6875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3282, d6875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27990 p hg
    simpa only [d3282, d6875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28289 (p : Pattern) (guard : d6558 p = 1) : d3285 p ≤ (0 : Int) + d6876 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3285, d6876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28288 p hg
    simpa only [d3285, d6876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3285, d6876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27994 p hg
    simpa only [d3285, d6876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28290 (p : Pattern) (guard : d6558 p = 1) : d3308 p ≤ (0 : Int) + d6877 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3308, d6877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28287 p hg
    simpa only [d3308, d6877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3308, d6877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28289 p hg
    simpa only [d3308, d6877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28291 (p : Pattern) (guard : d6558 p = 1) : d3451 p ≤ (0 : Int) + d6878 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3451, d6878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28270 p hg
    simpa only [d3451, d6878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3451, d6878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27956 p hg
    simpa only [d3451, d6878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28292 (p : Pattern) (guard : d6558 p = 1) : d3452 p ≤ (0 : Int) + d6879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3452, d6879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28273 p hg
    simpa only [d3452, d6879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3452, d6879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28004 p hg
    simpa only [d3452, d6879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28293 (p : Pattern) (guard : d6558 p = 1) : d3453 p ≤ (0 : Int) + d6880 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3453, d6880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28291 p hg
    simpa only [d3453, d6880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3453, d6880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28292 p hg
    simpa only [d3453, d6880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28294 (p : Pattern) (guard : d6558 p = 1) : d3454 p ≤ (0 : Int) + d6881 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3454, d6881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28273 p hg
    simpa only [d3454, d6881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3454, d6881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3454, d6881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28295 (p : Pattern) (guard : d6558 p = 1) : d3455 p ≤ (0 : Int) + d6882 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3455, d6882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28294 p hg
    simpa only [d3455, d6882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3455, d6882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3455, d6882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28296 (p : Pattern) (guard : d6558 p = 1) : d3456 p ≤ (0 : Int) + d6883 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3456, d6883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28293 p hg
    simpa only [d3456, d6883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3456, d6883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28295 p hg
    simpa only [d3456, d6883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28297 (p : Pattern) (guard : d6558 p = 1) : d3457 p ≤ (0 : Int) + d6884 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3457, d6884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28290 p hg
    simpa only [d3457, d6884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3457, d6884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28296 p hg
    simpa only [d3457, d6884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28298 (p : Pattern) (guard : d6558 p = 1) : d3458 p ≤ (0 : Int) + d6885 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3458, d6885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28279 p hg
    simpa only [d3458, d6885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3458, d6885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28297 p hg
    simpa only [d3458, d6885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28299 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6886 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28017 p hg
    simpa only [d6886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28300 (p : Pattern) (guard : d6558 p = 1) : d3230 p ≤ (0 : Int) + d6887 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28011 p hg
    simpa only [d3230, d6887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3230, d6887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28301 (p : Pattern) (guard : d6558 p = 1) : d3238 p ≤ (0 : Int) + d6888 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28299 p hg
    simpa only [d3238, d6888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28300 p hg
    simpa only [d3238, d6888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28302 (p : Pattern) (guard : d6558 p = 1) : d3238 p ≤ (0 : Int) + d6889 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28301 p hg
    simpa only [d6889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28022 p hg
    simpa only [d6889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28303 (p : Pattern) (guard : d6558 p = 1) : d3459 p ≤ (0 : Int) + d6890 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3459, d6890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28302 p hg
    simpa only [d3459, d6890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3459, d6890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28035 p hg
    simpa only [d3459, d6890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28304 (p : Pattern) (guard : d6558 p = 1) : d3460 p ≤ (0 : Int) + d6891 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3460, d6891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28303 p hg
    simpa only [d3460, d6891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3460, d6891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28036 p hg
    simpa only [d3460, d6891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28305 (p : Pattern) (guard : d5842 p = 1) : d8 p ≤ (0 : Int) + d8 p := by
  omega
theorem compare28306 (p : Pattern) (guard : d6558 p = 1) : d3461 p ≤ (0 : Int) + d8 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28305 p hg
    simpa only [d6558, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23784 p hg
    simpa only [d6558, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28307 (p : Pattern) (guard : d6558 p = 1) : d3461 p ≤ (0 : Int) + d3461 p := by
  omega
theorem compare28308 (p : Pattern) (guard : d6558 p = 1) : d3461 p ≤ (0 : Int) + d6892 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28306 p hg
    simpa only [d6892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28307 p hg
    simpa only [d6892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28309 (p : Pattern) (guard : d6558 p = 1) : d3461 p ≤ (0 : Int) + d6893 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28308 p hg
    simpa only [d6893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28307 p hg
    simpa only [d6893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28310 (p : Pattern) (guard : d6558 p = 1) : d3461 p ≤ (0 : Int) + d6894 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28306 p hg
    simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28309 p hg
    simpa only [d6894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28311 (p : Pattern) (guard : d6558 p = 1) : d3462 p ≤ (0 : Int) + d6895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3462, d6895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28309 p hg
    simpa only [d3462, d6895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3462, d6895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3462, d6895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28312 (p : Pattern) (guard : d6558 p = 1) : d3463 p ≤ (0 : Int) + d6896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3463, d6896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28310 p hg
    simpa only [d3463, d6896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3463, d6896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28311 p hg
    simpa only [d3463, d6896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28313 (p : Pattern) (guard : d6558 p = 1) : d3464 p ≤ (0 : Int) + d6897 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3464, d6897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28024 p hg
    simpa only [d3464, d6897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3464, d6897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28312 p hg
    simpa only [d3464, d6897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28314 (p : Pattern) (guard : d6558 p = 1) : d3465 p ≤ (0 : Int) + d6898 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3465, d6898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28313 p hg
    simpa only [d3465, d6898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3465, d6898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3465, d6898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28315 (p : Pattern) (guard : d6558 p = 1) : d3466 p ≤ (0 : Int) + d6899 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3466, d6899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28314 p hg
    simpa only [d3466, d6899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3466, d6899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3466, d6899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28316 (p : Pattern) (guard : d6558 p = 1) : d3467 p ≤ (0 : Int) + d6900 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3467, d6900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28304 p hg
    simpa only [d3467, d6900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3467, d6900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28315 p hg
    simpa only [d3467, d6900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28317 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6901 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3250, d6901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27923 p hg
    simpa only [d6558, d3250, d6901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3250, d6901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d6558, d3250, d6901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28318 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6902 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27927 p hg
    simpa only [d6902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28317 p hg
    simpa only [d6902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28319 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6903 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27926 p hg
    simpa only [d6903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28318 p hg
    simpa only [d6903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28320 (p : Pattern) (guard : d6558 p = 1) : d3251 p ≤ (0 : Int) + d6904 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3251, d6904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28319 p hg
    simpa only [d3251, d6904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3251, d6904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3251, d6904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28321 (p : Pattern) (guard : d6558 p = 1) : d3275 p ≤ (0 : Int) + d6905 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3275, d6905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27997 p hg
    simpa only [d3275, d6905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3275, d6905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28320 p hg
    simpa only [d3275, d6905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28322 (p : Pattern) (guard : d6558 p = 1) : d3275 p ≤ (0 : Int) + d6906 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28321 p hg
    simpa only [d6906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28032 p hg
    simpa only [d6906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28323 (p : Pattern) (guard : d6558 p = 1) : d3468 p ≤ (0 : Int) + d6907 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3468, d6907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28024 p hg
    simpa only [d3468, d6907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3468, d6907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27993 p hg
    simpa only [d3468, d6907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28324 (p : Pattern) (guard : d6558 p = 1) : d3469 p ≤ (0 : Int) + d6908 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3469, d6908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28322 p hg
    simpa only [d3469, d6908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3469, d6908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28323 p hg
    simpa only [d3469, d6908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28325 (p : Pattern) (guard : d6558 p = 1) : d3470 p ≤ (0 : Int) + d6909 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3470, d6909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28324 p hg
    simpa only [d3470, d6909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3470, d6909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28046 p hg
    simpa only [d3470, d6909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28326 (p : Pattern) (guard : d6558 p = 1) : d3471 p ≤ (0 : Int) + d6910 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3471, d6910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28312 p hg
    simpa only [d3471, d6910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3471, d6910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3471, d6910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28327 (p : Pattern) (guard : d6558 p = 1) : d3472 p ≤ (0 : Int) + d6911 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3472, d6911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28326 p hg
    simpa only [d3472, d6911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3472, d6911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3472, d6911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28328 (p : Pattern) (guard : d6558 p = 1) : d3473 p ≤ (0 : Int) + d6912 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3473, d6912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28327 p hg
    simpa only [d3473, d6912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3473, d6912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3473, d6912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28329 (p : Pattern) (guard : d6558 p = 1) : d3474 p ≤ (0 : Int) + d6913 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3474, d6913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28325 p hg
    simpa only [d3474, d6913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3474, d6913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28328 p hg
    simpa only [d3474, d6913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28330 (p : Pattern) (guard : d6558 p = 1) : d3475 p ≤ (0 : Int) + d6914 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3475, d6914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28316 p hg
    simpa only [d3475, d6914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3475, d6914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28329 p hg
    simpa only [d3475, d6914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28331 (p : Pattern) (guard : d6558 p = 1) : d3476 p ≤ (0 : Int) + d6915 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3476, d6915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28298 p hg
    simpa only [d3476, d6915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3476, d6915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28330 p hg
    simpa only [d3476, d6915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28332 (p : Pattern) (guard : d6558 p = 1) : d3477 p ≤ (0 : Int) + d6916 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3477, d6916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28330 p hg
    simpa only [d3477, d6916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3477, d6916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3477, d6916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28333 (p : Pattern) (guard : d6558 p = 1) : d3478 p ≤ (0 : Int) + d6917 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3478, d6917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28331 p hg
    simpa only [d3478, d6917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3478, d6917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28332 p hg
    simpa only [d3478, d6917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28334 (p : Pattern) (guard : d6558 p = 1) : d3479 p ≤ (0 : Int) + d6918 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3479, d6918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28090 p hg
    simpa only [d3479, d6918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3479, d6918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28333 p hg
    simpa only [d3479, d6918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28335 (p : Pattern) (guard : d6558 p = 1) : d3480 p ≤ (0 : Int) + d6919 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3480, d6919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28073 p hg
    simpa only [d3480, d6919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3480, d6919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28334 p hg
    simpa only [d3480, d6919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28336 (p : Pattern) (guard : d6558 p = 1) : d3481 p ≤ (0 : Int) + d6920 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3481, d6920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28127 p hg
    simpa only [d3481, d6920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3481, d6920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3481, d6920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28337 (p : Pattern) (guard : d6558 p = 1) : d3482 p ≤ (0 : Int) + d6921 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3482, d6921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28187 p hg
    simpa only [d3482, d6921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3482, d6921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28336 p hg
    simpa only [d3482, d6921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28338 (p : Pattern) (guard : d6558 p = 1) : d3483 p ≤ (0 : Int) + d6922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3483, d6922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28336 p hg
    simpa only [d3483, d6922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3483, d6922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3483, d6922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28339 (p : Pattern) (guard : d6558 p = 1) : d3484 p ≤ (0 : Int) + d6923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3484, d6923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28337 p hg
    simpa only [d3484, d6923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3484, d6923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28338 p hg
    simpa only [d3484, d6923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28340 (p : Pattern) (guard : d6558 p = 1) : d3485 p ≤ (0 : Int) + d6924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3485, d6924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28166 p hg
    simpa only [d3485, d6924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3485, d6924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3485, d6924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28341 (p : Pattern) (guard : d6558 p = 1) : d3486 p ≤ (0 : Int) + d6925 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3486, d6925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28195 p hg
    simpa only [d3486, d6925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3486, d6925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28340 p hg
    simpa only [d3486, d6925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28342 (p : Pattern) (guard : d6558 p = 1) : d3487 p ≤ (0 : Int) + d6926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3487, d6926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28340 p hg
    simpa only [d3487, d6926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3487, d6926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3487, d6926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28343 (p : Pattern) (guard : d6558 p = 1) : d3488 p ≤ (0 : Int) + d6927 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3488, d6927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28341 p hg
    simpa only [d3488, d6927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3488, d6927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28342 p hg
    simpa only [d3488, d6927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28344 (p : Pattern) (guard : d6558 p = 1) : d3489 p ≤ (0 : Int) + d6928 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3489, d6928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28339 p hg
    simpa only [d3489, d6928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3489, d6928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28343 p hg
    simpa only [d3489, d6928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28345 (p : Pattern) (guard : d6558 p = 1) : d3490 p ≤ (0 : Int) + d6929 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3490, d6929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28172 p hg
    simpa only [d3490, d6929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3490, d6929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28344 p hg
    simpa only [d3490, d6929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28346 (p : Pattern) (guard : d6558 p = 1) : d3481 p ≤ (0 : Int) + d6930 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3481, d6930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28217 p hg
    simpa only [d3481, d6930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3481, d6930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3481, d6930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28347 (p : Pattern) (guard : d6558 p = 1) : d3491 p ≤ (0 : Int) + d6931 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3491, d6931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28229 p hg
    simpa only [d3491, d6931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3491, d6931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28346 p hg
    simpa only [d3491, d6931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28348 (p : Pattern) (guard : d6558 p = 1) : d3483 p ≤ (0 : Int) + d6932 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3483, d6932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28346 p hg
    simpa only [d3483, d6932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3483, d6932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3483, d6932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28349 (p : Pattern) (guard : d6558 p = 1) : d3492 p ≤ (0 : Int) + d6933 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3492, d6933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28347 p hg
    simpa only [d3492, d6933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3492, d6933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28348 p hg
    simpa only [d3492, d6933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28350 (p : Pattern) (guard : d6558 p = 1) : d3493 p ≤ (0 : Int) + d6934 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3493, d6934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28349 p hg
    simpa only [d3493, d6934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3493, d6934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28237 p hg
    simpa only [d3493, d6934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28351 (p : Pattern) (guard : d6558 p = 1) : d3494 p ≤ (0 : Int) + d6935 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3494, d6935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28228 p hg
    simpa only [d3494, d6935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3494, d6935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28350 p hg
    simpa only [d3494, d6935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28352 (p : Pattern) (guard : d6558 p = 1) : d3495 p ≤ (0 : Int) + d6936 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3495, d6936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28345 p hg
    simpa only [d3495, d6936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3495, d6936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28351 p hg
    simpa only [d3495, d6936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28353 (p : Pattern) (guard : d6558 p = 1) : d3496 p ≤ (0 : Int) + d6937 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3496, d6937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28351 p hg
    simpa only [d3496, d6937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3496, d6937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28244 p hg
    simpa only [d3496, d6937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28354 (p : Pattern) (guard : d6558 p = 1) : d3497 p ≤ (0 : Int) + d6938 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3497, d6938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28352 p hg
    simpa only [d3497, d6938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3497, d6938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28353 p hg
    simpa only [d3497, d6938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28355 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6939 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d6939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28210 p hg
    simpa only [d6939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28356 (p : Pattern) (guard : d6558 p = 1) : d3362 p ≤ (0 : Int) + d6940 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28204 p hg
    simpa only [d3362, d6940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3362, d6940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28357 (p : Pattern) (guard : d6558 p = 1) : d3364 p ≤ (0 : Int) + d6941 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28355 p hg
    simpa only [d3364, d6941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28356 p hg
    simpa only [d3364, d6941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28358 (p : Pattern) (guard : d6558 p = 1) : d3369 p ≤ (0 : Int) + d6942 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3369, d6942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28357 p hg
    simpa only [d3369, d6942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3369, d6942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28217 p hg
    simpa only [d3369, d6942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28359 (p : Pattern) (guard : d6558 p = 1) : d3410 p ≤ (0 : Int) + d6943 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3410, d6943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28207 p hg
    simpa only [d3410, d6943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3410, d6943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28358 p hg
    simpa only [d3410, d6943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28360 (p : Pattern) (guard : d6558 p = 1) : d3369 p ≤ (0 : Int) + d6944 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3369, d6944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28212 p hg
    simpa only [d3369, d6944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3369, d6944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28217 p hg
    simpa only [d3369, d6944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28361 (p : Pattern) (guard : d6558 p = 1) : d3372 p ≤ (0 : Int) + d6945 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3372, d6945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28360 p hg
    simpa only [d3372, d6945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3372, d6945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28130 p hg
    simpa only [d3372, d6945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28362 (p : Pattern) (guard : d6558 p = 1) : d3411 p ≤ (0 : Int) + d6946 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3411, d6946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28359 p hg
    simpa only [d3411, d6946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3411, d6946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28361 p hg
    simpa only [d3411, d6946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28363 (p : Pattern) (guard : d6558 p = 1) : d3498 p ≤ (0 : Int) + d6947 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3498, d6947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28193 p hg
    simpa only [d3498, d6947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3498, d6947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28156 p hg
    simpa only [d3498, d6947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28364 (p : Pattern) (guard : d6558 p = 1) : d3499 p ≤ (0 : Int) + d6948 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3499, d6948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28222 p hg
    simpa only [d3499, d6948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3499, d6948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28363 p hg
    simpa only [d3499, d6948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28365 (p : Pattern) (guard : d6558 p = 1) : d3500 p ≤ (0 : Int) + d6949 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3500, d6949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28364 p hg
    simpa only [d3500, d6949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3500, d6949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28340 p hg
    simpa only [d3500, d6949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28366 (p : Pattern) (guard : d6558 p = 1) : d3501 p ≤ (0 : Int) + d6950 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3501, d6950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28223 p hg
    simpa only [d3501, d6950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3501, d6950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3501, d6950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28367 (p : Pattern) (guard : d6558 p = 1) : d3502 p ≤ (0 : Int) + d6951 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3502, d6951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28366 p hg
    simpa only [d3502, d6951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3502, d6951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3502, d6951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28368 (p : Pattern) (guard : d6558 p = 1) : d3503 p ≤ (0 : Int) + d6952 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3503, d6952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28367 p hg
    simpa only [d3503, d6952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3503, d6952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3503, d6952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28369 (p : Pattern) (guard : d6558 p = 1) : d3504 p ≤ (0 : Int) + d6953 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3504, d6953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28365 p hg
    simpa only [d3504, d6953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3504, d6953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28368 p hg
    simpa only [d3504, d6953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28370 (p : Pattern) (guard : d6558 p = 1) : d3505 p ≤ (0 : Int) + d6954 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3505, d6954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28362 p hg
    simpa only [d3505, d6954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3505, d6954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28369 p hg
    simpa only [d3505, d6954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28371 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6955 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28143 p hg
    simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28141 p hg
    simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28372 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6956 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28142 p hg
    simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28371 p hg
    simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28373 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6957 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28140 p hg
    simpa only [d6957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28372 p hg
    simpa only [d6957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28374 (p : Pattern) (guard : d6558 p = 1) : d3375 p ≤ (0 : Int) + d6958 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3375, d6958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28180 p hg
    simpa only [d3375, d6958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3375, d6958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3375, d6958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28375 (p : Pattern) (guard : d6558 p = 1) : d3394 p ≤ (0 : Int) + d6959 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3394, d6959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28373 p hg
    simpa only [d3394, d6959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3394, d6959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28374 p hg
    simpa only [d3394, d6959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28376 (p : Pattern) (guard : d6558 p = 1) : d3417 p ≤ (0 : Int) + d6960 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3417, d6960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28357 p hg
    simpa only [d3417, d6960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3417, d6960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28375 p hg
    simpa only [d3417, d6960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28377 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6961 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28119 p hg
    simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28160 p hg
    simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28378 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6962 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28161 p hg
    simpa only [d6962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28377 p hg
    simpa only [d6962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28379 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6963 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28118 p hg
    simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28378 p hg
    simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28380 (p : Pattern) (guard : d6558 p = 1) : d3367 p ≤ (0 : Int) + d6964 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3367, d6964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28121 p hg
    simpa only [d3367, d6964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3367, d6964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3367, d6964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28381 (p : Pattern) (guard : d6558 p = 1) : d3368 p ≤ (0 : Int) + d6965 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3368, d6965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28379 p hg
    simpa only [d3368, d6965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3368, d6965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28380 p hg
    simpa only [d3368, d6965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28382 (p : Pattern) (guard : d6558 p = 1) : d3481 p ≤ (0 : Int) + d6966 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3481, d6966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28381 p hg
    simpa only [d3481, d6966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3481, d6966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3481, d6966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28383 (p : Pattern) (guard : d6558 p = 1) : d3491 p ≤ (0 : Int) + d6967 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3491, d6967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28376 p hg
    simpa only [d3491, d6967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3491, d6967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28382 p hg
    simpa only [d3491, d6967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28384 (p : Pattern) (guard : d6558 p = 1) : d3367 p ≤ (0 : Int) + d6968 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3367, d6968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28378 p hg
    simpa only [d3367, d6968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3367, d6968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3367, d6968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28385 (p : Pattern) (guard : d6558 p = 1) : d3368 p ≤ (0 : Int) + d6969 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3368, d6969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28165 p hg
    simpa only [d3368, d6969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3368, d6969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28384 p hg
    simpa only [d3368, d6969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28386 (p : Pattern) (guard : d6558 p = 1) : d3481 p ≤ (0 : Int) + d6970 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3481, d6970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28385 p hg
    simpa only [d3481, d6970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3481, d6970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3481, d6970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28387 (p : Pattern) (guard : d6558 p = 1) : d3483 p ≤ (0 : Int) + d6971 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3483, d6971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28386 p hg
    simpa only [d3483, d6971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3483, d6971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3483, d6971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28388 (p : Pattern) (guard : d6558 p = 1) : d3492 p ≤ (0 : Int) + d6972 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3492, d6972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28383 p hg
    simpa only [d3492, d6972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3492, d6972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28387 p hg
    simpa only [d3492, d6972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28389 (p : Pattern) (guard : d6558 p = 1) : d3506 p ≤ (0 : Int) + d6973 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3506, d6973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28165 p hg
    simpa only [d3506, d6973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3506, d6973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28156 p hg
    simpa only [d3506, d6973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28390 (p : Pattern) (guard : d6558 p = 1) : d3507 p ≤ (0 : Int) + d6974 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3507, d6974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28389 p hg
    simpa only [d3507, d6974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3507, d6974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28166 p hg
    simpa only [d3507, d6974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28391 (p : Pattern) (guard : d6558 p = 1) : d3508 p ≤ (0 : Int) + d6975 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3508, d6975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28390 p hg
    simpa only [d3508, d6975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3508, d6975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28367 p hg
    simpa only [d3508, d6975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28392 (p : Pattern) (guard : d6558 p = 1) : d3509 p ≤ (0 : Int) + d6976 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3509, d6976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27962 p hg
    simpa only [d3509, d6976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3509, d6976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3509, d6976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28393 (p : Pattern) (guard : d6558 p = 1) : d3510 p ≤ (0 : Int) + d6977 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3510, d6977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28391 p hg
    simpa only [d3510, d6977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3510, d6977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28392 p hg
    simpa only [d3510, d6977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28394 (p : Pattern) (guard : d6558 p = 1) : d3511 p ≤ (0 : Int) + d6978 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3511, d6978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28388 p hg
    simpa only [d3511, d6978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3511, d6978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28393 p hg
    simpa only [d3511, d6978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28395 (p : Pattern) (guard : d6558 p = 1) : d3512 p ≤ (0 : Int) + d6979 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3512, d6979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28370 p hg
    simpa only [d3512, d6979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3512, d6979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28394 p hg
    simpa only [d3512, d6979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28396 (p : Pattern) (guard : d6558 p = 1) : d3364 p ≤ (0 : Int) + d6980 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28212 p hg
    simpa only [d6980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28215 p hg
    simpa only [d6980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28397 (p : Pattern) (guard : d6558 p = 1) : d3513 p ≤ (0 : Int) + d6981 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3513, d6981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28222 p hg
    simpa only [d3513, d6981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3513, d6981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27993 p hg
    simpa only [d3513, d6981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28398 (p : Pattern) (guard : d6558 p = 1) : d3514 p ≤ (0 : Int) + d6982 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3514, d6982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28396 p hg
    simpa only [d3514, d6982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3514, d6982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28397 p hg
    simpa only [d3514, d6982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28399 (p : Pattern) (guard : d6558 p = 1) : d3515 p ≤ (0 : Int) + d6983 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3515, d6983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28398 p hg
    simpa only [d3515, d6983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3515, d6983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28233 p hg
    simpa only [d3515, d6983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28400 (p : Pattern) (guard : d6558 p = 1) : d3516 p ≤ (0 : Int) + d6984 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3516, d6984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28399 p hg
    simpa only [d3516, d6984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3516, d6984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28237 p hg
    simpa only [d3516, d6984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28401 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6985 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3374, d6985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28139 p hg
    simpa only [d6558, d3374, d6985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3374, d6985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d6558, d3374, d6985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28402 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6986 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28143 p hg
    simpa only [d6986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28401 p hg
    simpa only [d6986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28403 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6987 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28142 p hg
    simpa only [d6987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28402 p hg
    simpa only [d6987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28404 (p : Pattern) (guard : d6558 p = 1) : d3375 p ≤ (0 : Int) + d6988 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3375, d6988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28403 p hg
    simpa only [d3375, d6988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3375, d6988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3375, d6988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28405 (p : Pattern) (guard : d6558 p = 1) : d3394 p ≤ (0 : Int) + d6989 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3394, d6989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28193 p hg
    simpa only [d3394, d6989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3394, d6989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28404 p hg
    simpa only [d3394, d6989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28406 (p : Pattern) (guard : d6558 p = 1) : d3394 p ≤ (0 : Int) + d6990 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28405 p hg
    simpa only [d6990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28222 p hg
    simpa only [d6990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28407 (p : Pattern) (guard : d6558 p = 1) : d3517 p ≤ (0 : Int) + d6991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3517, d6991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28406 p hg
    simpa only [d3517, d6991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3517, d6991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28346 p hg
    simpa only [d3517, d6991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28408 (p : Pattern) (guard : d6558 p = 1) : d3518 p ≤ (0 : Int) + d6992 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3518, d6992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28407 p hg
    simpa only [d3518, d6992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3518, d6992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28236 p hg
    simpa only [d3518, d6992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28409 (p : Pattern) (guard : d6558 p = 1) : d3519 p ≤ (0 : Int) + d6993 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3519, d6993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28029 p hg
    simpa only [d3519, d6993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3519, d6993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3519, d6993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28410 (p : Pattern) (guard : d6558 p = 1) : d3520 p ≤ (0 : Int) + d6994 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3520, d6994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28409 p hg
    simpa only [d3520, d6994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3520, d6994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3520, d6994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28411 (p : Pattern) (guard : d6558 p = 1) : d3521 p ≤ (0 : Int) + d6995 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3521, d6995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28408 p hg
    simpa only [d3521, d6995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3521, d6995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28410 p hg
    simpa only [d3521, d6995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28412 (p : Pattern) (guard : d6558 p = 1) : d3522 p ≤ (0 : Int) + d6996 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3522, d6996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28400 p hg
    simpa only [d3522, d6996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3522, d6996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28411 p hg
    simpa only [d3522, d6996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28413 (p : Pattern) (guard : d6558 p = 1) : d3523 p ≤ (0 : Int) + d6997 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3523, d6997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28395 p hg
    simpa only [d3523, d6997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3523, d6997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28412 p hg
    simpa only [d3523, d6997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28414 (p : Pattern) (guard : d6558 p = 1) : d3524 p ≤ (0 : Int) + d6998 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3524, d6998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28222 p hg
    simpa only [d3524, d6998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3524, d6998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28028 p hg
    simpa only [d3524, d6998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28415 (p : Pattern) (guard : d6558 p = 1) : d3525 p ≤ (0 : Int) + d6999 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3525, d6999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28396 p hg
    simpa only [d3525, d6999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3525, d6999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28414 p hg
    simpa only [d3525, d6999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28416 (p : Pattern) (guard : d6558 p = 1) : d3526 p ≤ (0 : Int) + d7000 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3526, d7000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28217 p hg
    simpa only [d3526, d7000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3526, d7000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28028 p hg
    simpa only [d3526, d7000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28417 (p : Pattern) (guard : d6558 p = 1) : d3527 p ≤ (0 : Int) + d7001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3527, d7001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28416 p hg
    simpa only [d3527, d7001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3527, d7001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3527, d7001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28418 (p : Pattern) (guard : d6558 p = 1) : d3528 p ≤ (0 : Int) + d7002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3528, d7002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28415 p hg
    simpa only [d3528, d7002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3528, d7002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28417 p hg
    simpa only [d3528, d7002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28419 (p : Pattern) (guard : d6558 p = 1) : d3529 p ≤ (0 : Int) + d7003 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3529, d7003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28224 p hg
    simpa only [d3529, d7003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3529, d7003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27993 p hg
    simpa only [d3529, d7003, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
