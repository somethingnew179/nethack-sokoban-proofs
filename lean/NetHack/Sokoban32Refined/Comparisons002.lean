/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare280 (p : Pattern) (guard : d835 p = 1) : d131 p ≤ (0 : Int) + d83 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare278 p hg
    simpa only [d835, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare279 p hg
    simpa only [d835, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare281 (p : Pattern) (guard : d835 p = 1) : d132 p ≤ (0 : Int) + d837 p := by
  cases selected : p 106 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d132, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare276 p hg
    simpa only [d132, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d132, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare280 p hg
    simpa only [d132, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare282 (p : Pattern) (guard : d836 p = 1) : d133 p ≤ (0 : Int) + d837 p := by
  cases selected : p 86 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare268 p hg
    simpa only [d836, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare281 p hg
    simpa only [d836, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare283 (p : Pattern) (guard : d836 p = 1) : d134 p ≤ (0 : Int) + d837 p := by
  cases selected : p 80 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare267 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d836 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare284 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (0 : Int) + d67 p := by
  omega
theorem compare285 (p : Pattern) (guard : d0 p = 1) : d84 p ≤ (0 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare286 (p : Pattern) (guard : d829 p = 1) : d85 p ≤ (0 : Int) + d177 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d85, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d829, d85, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d85, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare285 p hg
    simpa only [d829, d85, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare287 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d103 p := by
  omega
theorem compare288 (p : Pattern) (guard : d0 p = 1) : d114 p ≤ (0 : Int) + d165 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare289 (p : Pattern) (guard : d829 p = 1) : d115 p ≤ (0 : Int) + d178 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d115, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare287 p hg
    simpa only [d829, d115, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d115, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare288 p hg
    simpa only [d829, d115, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare290 (p : Pattern) (guard : d829 p = 1) : d116 p ≤ (0 : Int) + d179 p := by
  cases selected : p 86 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d116, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d116, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d116, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare289 p hg
    simpa only [d116, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare291 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (0 : Int) + d165 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare292 (p : Pattern) (guard : d829 p = 1) : d118 p ≤ (0 : Int) + d180 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d118, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d829, d118, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d118, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare291 p hg
    simpa only [d829, d118, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare293 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (0 : Int) + d128 p := by
  omega
theorem compare294 (p : Pattern) (guard : d0 p = 1) : d131 p ≤ (0 : Int) + d170 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare295 (p : Pattern) (guard : d829 p = 1) : d132 p ≤ (0 : Int) + d181 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d132, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare293 p hg
    simpa only [d829, d132, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d132, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d829, d132, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare296 (p : Pattern) (guard : d829 p = 1) : d133 p ≤ (0 : Int) + d182 p := by
  cases selected : p 86 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d133, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare292 p hg
    simpa only [d133, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d133, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d133, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare297 (p : Pattern) (guard : d829 p = 1) : d134 p ≤ (0 : Int) + d183 p := by
  cases selected : p 80 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d134, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare290 p hg
    simpa only [d134, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d134, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare296 p hg
    simpa only [d134, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare298 (p : Pattern) (guard : d0 p = 1) : d172 p ≤ (0 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare299 (p : Pattern) (guard : d827 p = 1) : d173 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d827, d173, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare105 p hg
    simpa only [d827, d173, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d827, d173, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare298 p hg
    simpa only [d827, d173, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare300 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (1 : Int) + d116 p := by
  omega
theorem compare301 (p : Pattern) (guard : d0 p = 1) : d172 p ≤ (1 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare302 (p : Pattern) (guard : d827 p = 1) : d173 p ≤ (1 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d827, d173, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare300 p hg
    simpa only [d827, d173, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d827, d173, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d827, d173, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare303 (p : Pattern) (guard : d0 p = 1) : d172 p ≤ (0 : Int) + d182 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare304 (p : Pattern) (guard : d838 p = 1) : d173 p ≤ (0 : Int) + d183 p := by
  cases selected : p 80 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d838, d173, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare290 p hg
    simpa only [d838, d173, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d838, d173, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare303 p hg
    simpa only [d838, d173, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare305 (p : Pattern) (guard : d0 p = 1) : d67 p ≤ (1 : Int) + d845 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare306 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare307 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (1 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare306 p hg
    simpa only [d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare308 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (1 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36 p hg
    simpa only [d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare307 p hg
    simpa only [d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare309 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare306 p hg
    simpa only [d4, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d4, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare310 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (1 : Int) + d32 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare309 p hg
    simpa only [d7, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d7, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare311 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (1 : Int) + d33 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare308 p hg
    simpa only [d8, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare310 p hg
    simpa only [d8, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare312 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (1 : Int) + d10 p := by
  omega
theorem compare313 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (1 : Int) + d1 p := by
  omega
theorem compare314 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (1 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare313 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare315 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (1 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare314 p hg
    simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare316 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare312 p hg
    simpa only [d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare315 p hg
    simpa only [d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare317 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (1 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare314 p hg
    simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7 p hg
    simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare318 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (1 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare317 p hg
    simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare319 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare316 p hg
    simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare320 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (1 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare311 p hg
    simpa only [d15, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare319 p hg
    simpa only [d15, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare321 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (1 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare311 p hg
    simpa only [d16, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d16, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare322 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (1 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare109 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare323 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (1 : Int) + d6 p := by
  omega
theorem compare324 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare325 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (1 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare326 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (1 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d8, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare325 p hg
    simpa only [d8, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare327 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d12 p := by
  omega
theorem compare328 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (1 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare313 p hg
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7 p hg
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare329 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (1 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare328 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare330 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare329 p hg
    simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare331 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (1 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare326 p hg
    simpa only [d15, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare330 p hg
    simpa only [d15, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare332 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (1 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare326 p hg
    simpa only [d16, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare331 p hg
    simpa only [d16, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare333 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (1 : Int) + d26 p := by
  omega
theorem compare334 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (1 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare332 p hg
    simpa only [d27, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare333 p hg
    simpa only [d27, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare335 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (1 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare322 p hg
    simpa only [d28, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare334 p hg
    simpa only [d28, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare336 (p : Pattern) (guard : d0 p = 1) : d73 p ≤ (1 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare337 (p : Pattern) (guard : d841 p = 1) : d74 p ≤ (1 : Int) + d44 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare335 p hg
    simpa only [d841, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare336 p hg
    simpa only [d841, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare338 (p : Pattern) (guard : d0 p = 1) : d76 p ≤ (1 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare339 (p : Pattern) (guard : d841 p = 1) : d77 p ≤ (1 : Int) + d44 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare335 p hg
    simpa only [d841, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare338 p hg
    simpa only [d841, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare340 (p : Pattern) (guard : d841 p = 1) : d78 p ≤ (1 : Int) + d44 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare337 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare339 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare341 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (1 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare142 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare342 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (1 : Int) + d25 p := by
  omega
theorem compare343 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (1 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare331 p hg
    simpa only [d46, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare342 p hg
    simpa only [d46, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare344 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (1 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare341 p hg
    simpa only [d47, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare343 p hg
    simpa only [d47, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare345 (p : Pattern) (guard : d0 p = 1) : d79 p ≤ (1 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare346 (p : Pattern) (guard : d841 p = 1) : d80 p ≤ (1 : Int) + d50 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare344 p hg
    simpa only [d841, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare345 p hg
    simpa only [d841, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare347 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (1 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare311 p hg
    simpa only [d52, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d52, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare348 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d53, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare347 p hg
    simpa only [d53, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare349 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare148 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare348 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare350 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (1 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare326 p hg
    simpa only [d52, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d52, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare351 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare331 p hg
    simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare350 p hg
    simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare352 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (1 : Int) + d55 p := by
  omega
theorem compare353 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (1 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare351 p hg
    simpa only [d56, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare352 p hg
    simpa only [d56, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare354 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (1 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare349 p hg
    simpa only [d57, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare353 p hg
    simpa only [d57, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare355 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (1 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare356 (p : Pattern) (guard : d841 p = 1) : d82 p ≤ (1 : Int) + d64 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare354 p hg
    simpa only [d841, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare355 p hg
    simpa only [d841, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare357 (p : Pattern) (guard : d841 p = 1) : d83 p ≤ (1 : Int) + d844 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d83, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d83, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d83, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare356 p hg
    simpa only [d83, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare358 (p : Pattern) (guard : d841 p = 1) : d84 p ≤ (1 : Int) + d845 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d84, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare340 p hg
    simpa only [d84, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d84, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d84, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare359 (p : Pattern) (guard : d842 p = 1) : d85 p ≤ (1 : Int) + d845 p := by
  cases selected : p 106 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d842, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare305 p hg
    simpa only [d842, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d842, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare358 p hg
    simpa only [d842, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare360 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (1 : Int) + d847 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare361 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (1 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare311 p hg
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare347 p hg
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare362 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (1 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare361 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare363 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (1 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare326 p hg
    simpa only [d86, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare350 p hg
    simpa only [d86, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare364 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (1 : Int) + d87 p := by
  omega
theorem compare365 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (1 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare363 p hg
    simpa only [d88, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare364 p hg
    simpa only [d88, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare366 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (1 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare362 p hg
    simpa only [d89, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare365 p hg
    simpa only [d89, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare367 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (1 : Int) + d94 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare368 (p : Pattern) (guard : d841 p = 1) : d105 p ≤ (1 : Int) + d94 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare366 p hg
    simpa only [d841, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare367 p hg
    simpa only [d841, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare369 (p : Pattern) (guard : d841 p = 1) : d106 p ≤ (1 : Int) + d846 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d106, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare339 p hg
    simpa only [d106, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d106, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare368 p hg
    simpa only [d106, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare370 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (1 : Int) + d98 p := by
  omega
theorem compare371 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare319 p hg
    simpa only [d97, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d97, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare372 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (1 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare319 p hg
    simpa only [d98, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare371 p hg
    simpa only [d98, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare373 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (1 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare370 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare372 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare374 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare330 p hg
    simpa only [d97, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d97, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare375 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (1 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare330 p hg
    simpa only [d98, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare374 p hg
    simpa only [d98, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare376 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (1 : Int) + d71 p := by
  omega
theorem compare377 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (1 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare375 p hg
    simpa only [d99, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare376 p hg
    simpa only [d99, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare378 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (1 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d100, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare373 p hg
    simpa only [d100, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d100, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare377 p hg
    simpa only [d100, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare379 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (1 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare380 (p : Pattern) (guard : d841 p = 1) : d108 p ≤ (1 : Int) + d101 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare378 p hg
    simpa only [d841, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare379 p hg
    simpa only [d841, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare381 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d1 p := by
  change (2 : Int) ≤ (1 : Int) + 1
  decide
theorem compare382 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare383 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare382 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare384 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare385 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare383 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare384 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare386 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare383 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare387 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare385 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare386 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare388 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d14 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare52 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare387 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare389 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare388 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare56 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare390 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare382 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare391 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare383 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare390 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare392 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare390 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare393 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare391 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare392 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare394 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare319 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare393 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare395 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare394 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare371 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare396 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare389 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare395 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare397 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare384 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare398 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare385 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare397 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare399 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d40 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare330 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare398 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare400 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare399 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare374 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare401 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (1 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare393 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare402 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (1 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare401 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare403 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare400 p hg
    simpa only [d109, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare402 p hg
    simpa only [d109, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare404 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (1 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare396 p hg
    simpa only [d110, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare403 p hg
    simpa only [d110, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare405 (p : Pattern) (guard : d0 p = 1) : d111 p ≤ (1 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare406 (p : Pattern) (guard : d841 p = 1) : d112 p ≤ (1 : Int) + d101 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare404 p hg
    simpa only [d841, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare405 p hg
    simpa only [d841, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare407 (p : Pattern) (guard : d841 p = 1) : d113 p ≤ (1 : Int) + d101 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare380 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare406 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare408 (p : Pattern) (guard : d841 p = 1) : d114 p ≤ (1 : Int) + d847 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d114, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare369 p hg
    simpa only [d114, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d114, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare407 p hg
    simpa only [d114, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare409 (p : Pattern) (guard : d842 p = 1) : d115 p ≤ (1 : Int) + d847 p := by
  cases selected : p 106 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d842, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare360 p hg
    simpa only [d842, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d842, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare408 p hg
    simpa only [d842, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare410 (p : Pattern) (guard : d842 p = 1) : d116 p ≤ (1 : Int) + d848 p := by
  cases selected : p 86 with
  | false =>
    have hg : d842 p = 1 := by simpa only [d116, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare359 p hg
    simpa only [d116, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d842 p = 1 := by simpa only [d116, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare409 p hg
    simpa only [d116, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare411 (p : Pattern) (guard : d0 p = 1) : d172 p ≤ (1 : Int) + d852 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare412 (p : Pattern) (guard : d843 p = 1) : d173 p ≤ (1 : Int) + d853 p := by
  cases selected : p 80 with
  | false =>
    have hg : d842 p = 1 := by simpa only [d843, d173, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare410 p hg
    simpa only [d843, d173, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d843, d173, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare411 p hg
    simpa only [d843, d173, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare413 (p : Pattern) (guard : d0 p = 1) : d166 p ≤ (0 : Int) + d115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare414 (p : Pattern) (guard : d833 p = 1) : d174 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d833, d174, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare191 p hg
    simpa only [d833, d174, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d833, d174, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare413 p hg
    simpa only [d833, d174, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare415 (p : Pattern) (guard : d0 p = 1) : d171 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare416 (p : Pattern) (guard : d833 p = 1) : d175 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d833, d175, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare194 p hg
    simpa only [d833, d175, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d833, d175, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare415 p hg
    simpa only [d833, d175, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare417 (p : Pattern) (guard : d833 p = 1) : d176 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d176, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare414 p hg
    simpa only [d176, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d833 p = 1 := by simpa only [d176, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare416 p hg
    simpa only [d176, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare418 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (0 : Int) + d45 p := by
  omega
theorem compare419 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban32Refined
