/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9240 (p : Pattern) (guard : d1088 p = 1) : d122 p ≤ (0 : Int) + d520 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d122, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9239 p hg
    simpa only [d122, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d122, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9210 p hg
    simpa only [d122, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9241 (p : Pattern) (guard : d1088 p = 1) : d123 p ≤ (0 : Int) + d529 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d123, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9218 p hg
    simpa only [d123, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d123, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9240 p hg
    simpa only [d123, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9242 (p : Pattern) (guard : d1088 p = 1) : d124 p ≤ (0 : Int) + d530 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d124, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1716 p hg
    simpa only [d124, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d124, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9241 p hg
    simpa only [d124, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9243 (p : Pattern) (guard : d1088 p = 1) : d127 p ≤ (0 : Int) + d531 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d127, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1856 p hg
    simpa only [d127, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d127, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5883 p hg
    simpa only [d127, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9244 (p : Pattern) (guard : d1088 p = 1) : d128 p ≤ (0 : Int) + d532 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d128, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9242 p hg
    simpa only [d128, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d128, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9243 p hg
    simpa only [d128, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9245 (p : Pattern) (guard : d1088 p = 1) : d129 p ≤ (0 : Int) + d533 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d129, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d129, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d129, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9234 p hg
    simpa only [d129, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9246 (p : Pattern) (guard : d1088 p = 1) : d131 p ≤ (0 : Int) + d534 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d131, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9245 p hg
    simpa only [d131, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d131, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5887 p hg
    simpa only [d131, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9247 (p : Pattern) (guard : d1088 p = 1) : d132 p ≤ (0 : Int) + d535 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d132, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9244 p hg
    simpa only [d132, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d132, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9246 p hg
    simpa only [d132, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9248 (p : Pattern) (guard : d1088 p = 1) : d133 p ≤ (0 : Int) + d536 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d133, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9237 p hg
    simpa only [d133, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d133, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9247 p hg
    simpa only [d133, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9249 (p : Pattern) (guard : d1088 p = 1) : d134 p ≤ (0 : Int) + d537 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d134, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9225 p hg
    simpa only [d134, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d134, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9248 p hg
    simpa only [d134, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9250 (p : Pattern) (guard : d0 p = 1) : d45 p ≤ (1 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9251 (p : Pattern) (guard : d1096 p = 1) : d45 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1888 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9250 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9252 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (1 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9253 (p : Pattern) (guard : d1096 p = 1) : d66 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d1096, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9252 p hg
    simpa only [d1096, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9254 (p : Pattern) (guard : d1096 p = 1) : d67 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9251 p hg
    simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9253 p hg
    simpa only [d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9255 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (1 : Int) + d1105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9256 (p : Pattern) (guard : d1096 p = 1) : d78 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1910 p hg
    simpa only [d1096, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9255 p hg
    simpa only [d1096, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9257 (p : Pattern) (guard : d0 p = 1) : d82 p ≤ (1 : Int) + d1105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9258 (p : Pattern) (guard : d1096 p = 1) : d83 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1915 p hg
    simpa only [d1096, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9257 p hg
    simpa only [d1096, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9259 (p : Pattern) (guard : d1096 p = 1) : d84 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9256 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9258 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9260 (p : Pattern) (guard : d1096 p = 1) : d85 p ≤ (1 : Int) + d1106 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d85, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9254 p hg
    simpa only [d85, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d85, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9259 p hg
    simpa only [d85, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9261 (p : Pattern) (guard : d0 p = 1) : d95 p ≤ (1 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9262 (p : Pattern) (guard : d1096 p = 1) : d96 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1888 p hg
    simpa only [d1096, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9261 p hg
    simpa only [d1096, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9263 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (1 : Int) + d1110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9264 (p : Pattern) (guard : d1096 p = 1) : d102 p ≤ (1 : Int) + d1110 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1929 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9263 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9265 (p : Pattern) (guard : d1096 p = 1) : d103 p ≤ (1 : Int) + d1111 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d103, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9262 p hg
    simpa only [d103, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d103, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9264 p hg
    simpa only [d103, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9266 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (1 : Int) + d1105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9267 (p : Pattern) (guard : d1096 p = 1) : d106 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1934 p hg
    simpa only [d1096, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9266 p hg
    simpa only [d1096, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9268 (p : Pattern) (guard : d0 p = 1) : d112 p ≤ (1 : Int) + d1113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9269 (p : Pattern) (guard : d1096 p = 1) : d113 p ≤ (1 : Int) + d1113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1939 p hg
    simpa only [d1096, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9268 p hg
    simpa only [d1096, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9270 (p : Pattern) (guard : d1096 p = 1) : d114 p ≤ (1 : Int) + d1114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d114, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9267 p hg
    simpa only [d114, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d114, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9269 p hg
    simpa only [d114, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9271 (p : Pattern) (guard : d1096 p = 1) : d115 p ≤ (1 : Int) + d1115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d115, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9265 p hg
    simpa only [d115, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d115, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9270 p hg
    simpa only [d115, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9272 (p : Pattern) (guard : d1096 p = 1) : d116 p ≤ (1 : Int) + d1116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d116, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9260 p hg
    simpa only [d116, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d116, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9271 p hg
    simpa only [d116, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9273 (p : Pattern) (guard : d1096 p = 1) : d77 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1934 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9255 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9274 (p : Pattern) (guard : d1096 p = 1) : d117 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9273 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9258 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9275 (p : Pattern) (guard : d1096 p = 1) : d118 p ≤ (1 : Int) + d1106 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d118, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9254 p hg
    simpa only [d118, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d118, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9274 p hg
    simpa only [d118, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9276 (p : Pattern) (guard : d0 p = 1) : d123 p ≤ (1 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9277 (p : Pattern) (guard : d1096 p = 1) : d124 p ≤ (1 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1888 p hg
    simpa only [d1096, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9276 p hg
    simpa only [d1096, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9278 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (1 : Int) + d1110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9279 (p : Pattern) (guard : d1096 p = 1) : d127 p ≤ (1 : Int) + d1110 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1929 p hg
    simpa only [d1096, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9278 p hg
    simpa only [d1096, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9280 (p : Pattern) (guard : d1096 p = 1) : d128 p ≤ (1 : Int) + d1111 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d128, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9277 p hg
    simpa only [d128, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d128, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9279 p hg
    simpa only [d128, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9281 (p : Pattern) (guard : d1096 p = 1) : d129 p ≤ (1 : Int) + d1105 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1934 p hg
    simpa only [d1096, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9257 p hg
    simpa only [d1096, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9282 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (1 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9283 (p : Pattern) (guard : d1087 p = 1) : d97 p ≤ (1 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9282 p hg
    simpa only [d1087, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1087, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d1087, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9284 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (1 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9285 (p : Pattern) (guard : d1087 p = 1) : d70 p ≤ (1 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9284 p hg
    simpa only [d1087, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1087, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d1087, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9286 (p : Pattern) (guard : d1087 p = 1) : d109 p ≤ (1 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9283 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9285 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9287 (p : Pattern) (guard : d1087 p = 1) : d110 p ≤ (1 : Int) + d2 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9283 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9286 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9288 (p : Pattern) (guard : d1087 p = 1) : d111 p ≤ (1 : Int) + d2 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9286 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1937 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9289 (p : Pattern) (guard : d1087 p = 1) : d112 p ≤ (1 : Int) + d2 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9287 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9288 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9290 (p : Pattern) (guard : d1096 p = 1) : d130 p ≤ (1 : Int) + d2 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1087 p = 1 := by simpa only [d1096, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9289 p hg
    simpa only [d1096, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1096, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1963 p hg
    simpa only [d1096, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9291 (p : Pattern) (guard : d1096 p = 1) : d131 p ≤ (1 : Int) + d1939 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d131, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9281 p hg
    simpa only [d131, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d131, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9290 p hg
    simpa only [d131, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9292 (p : Pattern) (guard : d1096 p = 1) : d132 p ≤ (1 : Int) + d1940 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d132, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9280 p hg
    simpa only [d132, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d132, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9291 p hg
    simpa only [d132, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9293 (p : Pattern) (guard : d1096 p = 1) : d133 p ≤ (1 : Int) + d1941 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d133, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9275 p hg
    simpa only [d133, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d133, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9292 p hg
    simpa only [d133, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9294 (p : Pattern) (guard : d1096 p = 1) : d134 p ≤ (1 : Int) + d1942 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d134, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9272 p hg
    simpa only [d134, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1096 p = 1 := by simpa only [d134, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9293 p hg
    simpa only [d134, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9295 (p : Pattern) (guard : d1092 p = 1) : d16 p ≤ (0 : Int) + d389 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d16, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5613 p hg
    simpa only [d1092, d16, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d16, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d1092, d16, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9296 (p : Pattern) (guard : d1092 p = 1) : d26 p ≤ (0 : Int) + d390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d26, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5615 p hg
    simpa only [d1092, d26, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d26, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d1092, d26, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9297 (p : Pattern) (guard : d1092 p = 1) : d27 p ≤ (0 : Int) + d391 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d27, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9295 p hg
    simpa only [d27, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d27, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9296 p hg
    simpa only [d27, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9298 (p : Pattern) (guard : d1092 p = 1) : d28 p ≤ (0 : Int) + d392 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d28, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9295 p hg
    simpa only [d28, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d28, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9297 p hg
    simpa only [d28, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9299 (p : Pattern) (guard : d1092 p = 1) : d35 p ≤ (0 : Int) + d393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d35, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5619 p hg
    simpa only [d1092, d35, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d35, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d1092, d35, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9300 (p : Pattern) (guard : d1092 p = 1) : d36 p ≤ (0 : Int) + d394 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d36, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9295 p hg
    simpa only [d36, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d36, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9299 p hg
    simpa only [d36, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9301 (p : Pattern) (guard : d1092 p = 1) : d42 p ≤ (0 : Int) + d395 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d42, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5622 p hg
    simpa only [d1092, d42, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d42, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d1092, d42, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9302 (p : Pattern) (guard : d1092 p = 1) : d43 p ≤ (0 : Int) + d396 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d43, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9301 p hg
    simpa only [d43, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d43, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9296 p hg
    simpa only [d43, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9303 (p : Pattern) (guard : d1092 p = 1) : d44 p ≤ (0 : Int) + d397 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d44, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9300 p hg
    simpa only [d44, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d44, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9302 p hg
    simpa only [d44, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9304 (p : Pattern) (guard : d1092 p = 1) : d45 p ≤ (0 : Int) + d398 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d45, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9298 p hg
    simpa only [d45, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d45, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9303 p hg
    simpa only [d45, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9305 (p : Pattern) (guard : d1092 p = 1) : d53 p ≤ (0 : Int) + d399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d53, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d1092, d53, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d53, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1092, d53, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9306 (p : Pattern) (guard : d1092 p = 1) : d55 p ≤ (0 : Int) + d400 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d55, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d1092, d55, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d55, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1092, d55, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9307 (p : Pattern) (guard : d1092 p = 1) : d56 p ≤ (0 : Int) + d401 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d56, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9305 p hg
    simpa only [d56, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d56, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9306 p hg
    simpa only [d56, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9308 (p : Pattern) (guard : d1092 p = 1) : d57 p ≤ (0 : Int) + d402 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d57, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9305 p hg
    simpa only [d57, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d57, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9307 p hg
    simpa only [d57, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9309 (p : Pattern) (guard : d1092 p = 1) : d59 p ≤ (0 : Int) + d403 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d59, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2066 p hg
    simpa only [d1092, d59, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d59, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1092, d59, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9310 (p : Pattern) (guard : d1092 p = 1) : d60 p ≤ (0 : Int) + d404 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d60, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9305 p hg
    simpa only [d60, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d60, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9309 p hg
    simpa only [d60, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9311 (p : Pattern) (guard : d1092 p = 1) : d62 p ≤ (0 : Int) + d405 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d62, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2069 p hg
    simpa only [d1092, d62, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d62, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d1092, d62, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9312 (p : Pattern) (guard : d1092 p = 1) : d63 p ≤ (0 : Int) + d406 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d63, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9311 p hg
    simpa only [d63, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d63, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9306 p hg
    simpa only [d63, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9313 (p : Pattern) (guard : d1092 p = 1) : d64 p ≤ (0 : Int) + d407 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d64, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9310 p hg
    simpa only [d64, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d64, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9312 p hg
    simpa only [d64, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9314 (p : Pattern) (guard : d1092 p = 1) : d65 p ≤ (0 : Int) + d408 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d65, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9308 p hg
    simpa only [d65, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d65, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9313 p hg
    simpa only [d65, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9315 (p : Pattern) (guard : d1092 p = 1) : d66 p ≤ (0 : Int) + d408 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2073 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9314 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9316 (p : Pattern) (guard : d1092 p = 1) : d67 p ≤ (0 : Int) + d409 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d67, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9304 p hg
    simpa only [d67, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d67, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9315 p hg
    simpa only [d67, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9317 (p : Pattern) (guard : d1092 p = 1) : d73 p ≤ (0 : Int) + d413 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d73, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9297 p hg
    simpa only [d73, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d73, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2097 p hg
    simpa only [d73, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9318 (p : Pattern) (guard : d1092 p = 1) : d74 p ≤ (0 : Int) + d414 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d74, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9298 p hg
    simpa only [d74, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d74, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9317 p hg
    simpa only [d74, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9319 (p : Pattern) (guard : d1092 p = 1) : d76 p ≤ (0 : Int) + d415 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d76, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9297 p hg
    simpa only [d76, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d76, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d76, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9320 (p : Pattern) (guard : d1092 p = 1) : d77 p ≤ (0 : Int) + d416 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d77, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9298 p hg
    simpa only [d77, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d77, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9319 p hg
    simpa only [d77, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9321 (p : Pattern) (guard : d1092 p = 1) : d78 p ≤ (0 : Int) + d417 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d78, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9318 p hg
    simpa only [d78, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d78, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9320 p hg
    simpa only [d78, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9322 (p : Pattern) (guard : d1092 p = 1) : d81 p ≤ (0 : Int) + d418 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d81, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9307 p hg
    simpa only [d81, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d81, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d81, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9323 (p : Pattern) (guard : d1092 p = 1) : d82 p ≤ (0 : Int) + d419 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d82, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9308 p hg
    simpa only [d82, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d82, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9322 p hg
    simpa only [d82, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9324 (p : Pattern) (guard : d1092 p = 1) : d83 p ≤ (0 : Int) + d419 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2082 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9323 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9325 (p : Pattern) (guard : d1092 p = 1) : d84 p ≤ (0 : Int) + d420 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d84, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9321 p hg
    simpa only [d84, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d84, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9324 p hg
    simpa only [d84, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9326 (p : Pattern) (guard : d1092 p = 1) : d85 p ≤ (0 : Int) + d421 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d85, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9316 p hg
    simpa only [d85, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d85, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9325 p hg
    simpa only [d85, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9327 (p : Pattern) (guard : d1092 p = 1) : d86 p ≤ (0 : Int) + d389 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d86, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5613 p hg
    simpa only [d1092, d86, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d86, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1092, d86, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9328 (p : Pattern) (guard : d1092 p = 1) : d87 p ≤ (0 : Int) + d390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d87, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5615 p hg
    simpa only [d1092, d87, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d87, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1092, d87, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9329 (p : Pattern) (guard : d1092 p = 1) : d88 p ≤ (0 : Int) + d391 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d88, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9327 p hg
    simpa only [d88, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d88, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9328 p hg
    simpa only [d88, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9330 (p : Pattern) (guard : d1092 p = 1) : d89 p ≤ (0 : Int) + d392 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d89, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9327 p hg
    simpa only [d89, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d89, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9329 p hg
    simpa only [d89, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9331 (p : Pattern) (guard : d1092 p = 1) : d90 p ≤ (0 : Int) + d393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d90, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5619 p hg
    simpa only [d1092, d90, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d90, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1092, d90, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9332 (p : Pattern) (guard : d1092 p = 1) : d91 p ≤ (0 : Int) + d394 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d91, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9327 p hg
    simpa only [d91, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d91, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9331 p hg
    simpa only [d91, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9333 (p : Pattern) (guard : d1092 p = 1) : d92 p ≤ (0 : Int) + d395 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d92, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5622 p hg
    simpa only [d1092, d92, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d92, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d1092, d92, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9334 (p : Pattern) (guard : d1092 p = 1) : d93 p ≤ (0 : Int) + d396 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9328 p hg
    simpa only [d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9335 (p : Pattern) (guard : d1092 p = 1) : d94 p ≤ (0 : Int) + d397 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d94, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9332 p hg
    simpa only [d94, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d94, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9334 p hg
    simpa only [d94, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9336 (p : Pattern) (guard : d1092 p = 1) : d95 p ≤ (0 : Int) + d398 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d95, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d95, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d95, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9335 p hg
    simpa only [d95, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9337 (p : Pattern) (guard : d1092 p = 1) : d96 p ≤ (0 : Int) + d398 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9304 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9336 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9338 (p : Pattern) (guard : d1092 p = 1) : d103 p ≤ (0 : Int) + d427 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d103, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9337 p hg
    simpa only [d103, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d103, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2099 p hg
    simpa only [d103, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9339 (p : Pattern) (guard : d1092 p = 1) : d104 p ≤ (0 : Int) + d415 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d104, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9329 p hg
    simpa only [d104, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d104, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d104, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9340 (p : Pattern) (guard : d1092 p = 1) : d105 p ≤ (0 : Int) + d416 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d105, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d105, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d105, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9339 p hg
    simpa only [d105, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9341 (p : Pattern) (guard : d1092 p = 1) : d106 p ≤ (0 : Int) + d416 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9320 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9340 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9342 (p : Pattern) (guard : d1092 p = 1) : d113 p ≤ (0 : Int) + d435 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d113, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2107 p hg
    simpa only [d113, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d113, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2131 p hg
    simpa only [d113, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9343 (p : Pattern) (guard : d1092 p = 1) : d114 p ≤ (0 : Int) + d436 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9341 p hg
    simpa only [d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9342 p hg
    simpa only [d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9344 (p : Pattern) (guard : d1092 p = 1) : d115 p ≤ (0 : Int) + d437 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d115, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9338 p hg
    simpa only [d115, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d115, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9343 p hg
    simpa only [d115, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9345 (p : Pattern) (guard : d1092 p = 1) : d116 p ≤ (0 : Int) + d438 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d116, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9326 p hg
    simpa only [d116, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d116, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9344 p hg
    simpa only [d116, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9346 (p : Pattern) (guard : d1092 p = 1) : d117 p ≤ (0 : Int) + d439 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d117, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9320 p hg
    simpa only [d117, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d117, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9324 p hg
    simpa only [d117, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9347 (p : Pattern) (guard : d1092 p = 1) : d118 p ≤ (0 : Int) + d440 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d118, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9316 p hg
    simpa only [d118, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d118, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9346 p hg
    simpa only [d118, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9348 (p : Pattern) (guard : d1092 p = 1) : d120 p ≤ (0 : Int) + d441 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d120, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d1092, d120, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d120, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1092, d120, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9349 (p : Pattern) (guard : d1092 p = 1) : d121 p ≤ (0 : Int) + d442 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d121, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9327 p hg
    simpa only [d121, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d121, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9348 p hg
    simpa only [d121, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9350 (p : Pattern) (guard : d1092 p = 1) : d122 p ≤ (0 : Int) + d443 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d122, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9349 p hg
    simpa only [d122, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d122, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9334 p hg
    simpa only [d122, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9351 (p : Pattern) (guard : d1092 p = 1) : d123 p ≤ (0 : Int) + d444 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d123, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d123, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d123, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9350 p hg
    simpa only [d123, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9352 (p : Pattern) (guard : d1092 p = 1) : d124 p ≤ (0 : Int) + d445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d124, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9304 p hg
    simpa only [d124, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d124, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9351 p hg
    simpa only [d124, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9353 (p : Pattern) (guard : d1092 p = 1) : d127 p ≤ (0 : Int) + d448 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d127, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2099 p hg
    simpa only [d127, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d127, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5985 p hg
    simpa only [d127, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9354 (p : Pattern) (guard : d1092 p = 1) : d128 p ≤ (0 : Int) + d449 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d128, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9352 p hg
    simpa only [d128, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d128, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9353 p hg
    simpa only [d128, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9355 (p : Pattern) (guard : d1092 p = 1) : d129 p ≤ (0 : Int) + d450 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d129, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9320 p hg
    simpa only [d129, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d129, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9323 p hg
    simpa only [d129, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9356 (p : Pattern) (guard : d1092 p = 1) : d131 p ≤ (0 : Int) + d452 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d131, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9355 p hg
    simpa only [d131, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d131, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5989 p hg
    simpa only [d131, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9357 (p : Pattern) (guard : d1092 p = 1) : d132 p ≤ (0 : Int) + d453 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d132, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9354 p hg
    simpa only [d132, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d132, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9356 p hg
    simpa only [d132, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9358 (p : Pattern) (guard : d1092 p = 1) : d133 p ≤ (0 : Int) + d454 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d133, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9347 p hg
    simpa only [d133, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d133, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9357 p hg
    simpa only [d133, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9359 (p : Pattern) (guard : d1092 p = 1) : d134 p ≤ (0 : Int) + d455 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d134, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9345 p hg
    simpa only [d134, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d134, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9358 p hg
    simpa only [d134, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9360 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (4 : Int) + d134 p := by
  omega
theorem compare9361 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (9 : Int) + d134 p := by
  omega
theorem compare9362 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (15 : Int) + d134 p := by
  omega
theorem compare9363 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (17 : Int) + d134 p := by
  omega
theorem compare9364 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (6 : Int) + d134 p := by
  omega
theorem compare9365 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (10 : Int) + d134 p := by
  omega
theorem compare9366 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (11 : Int) + d134 p := by
  omega
theorem compare9367 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (14 : Int) + d134 p := by
  omega
theorem compare9368 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (18 : Int) + d134 p := by
  omega
theorem compare9369 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (19 : Int) + d134 p := by
  omega
theorem compare9370 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (7 : Int) + d134 p := by
  omega
theorem compare9371 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9372 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9371 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9373 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9374 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9373 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9375 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9374 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9376 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9372 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9375 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9377 (p : Pattern) (guard : d1943 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare9378 (p : Pattern) (guard : d1944 p = 1) : d0 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9374 p hg
    simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9377 p hg
    simpa only [d1944, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9379 (p : Pattern) (guard : d1945 p = 1) : d0 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9372 p hg
    simpa only [d1945, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9378 p hg
    simpa only [d1945, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
