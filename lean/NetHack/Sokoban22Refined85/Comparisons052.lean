/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7280 (p : Pattern) (guard : d4432 p = 1) : d929 p ≤ (2 : Int) + d4751 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d929, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7275 p hg
    simpa only [d929, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d929, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7279 p hg
    simpa only [d929, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7281 (p : Pattern) (guard : d0 p = 1) : d930 p ≤ (2 : Int) + d243 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7282 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (2 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d211, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d211, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d211, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d211, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7283 (p : Pattern) (guard : d1 p = 1) : d245 p ≤ (2 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d245, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d245, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d245, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7282 p hg
    simpa only [d245, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7284 (p : Pattern) (guard : d4299 p = 1) : d931 p ≤ (2 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d931, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7283 p hg
    simpa only [d4299, d931, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d931, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4816 p hg
    simpa only [d4299, d931, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7285 (p : Pattern) (guard : d4432 p = 1) : d932 p ≤ (2 : Int) + d243 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7281 p hg
    simpa only [d4432, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7284 p hg
    simpa only [d4432, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7286 (p : Pattern) (guard : d0 p = 1) : d931 p ≤ (2 : Int) + d246 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7287 (p : Pattern) (guard : d1 p = 1) : d933 p ≤ (2 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d933, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d933, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d933, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d933, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7288 (p : Pattern) (guard : d4299 p = 1) : d934 p ≤ (2 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d934, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7287 p hg
    simpa only [d4299, d934, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d934, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4949 p hg
    simpa only [d4299, d934, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7289 (p : Pattern) (guard : d4432 p = 1) : d935 p ≤ (2 : Int) + d246 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7286 p hg
    simpa only [d4432, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7288 p hg
    simpa only [d4432, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7290 (p : Pattern) (guard : d4432 p = 1) : d936 p ≤ (2 : Int) + d4754 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d936, d4754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7285 p hg
    simpa only [d936, d4754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d936, d4754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7289 p hg
    simpa only [d936, d4754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7291 (p : Pattern) (guard : d4432 p = 1) : d937 p ≤ (2 : Int) + d4755 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d937, d4755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7280 p hg
    simpa only [d937, d4755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d937, d4755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7290 p hg
    simpa only [d937, d4755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7292 (p : Pattern) (guard : d0 p = 1) : d938 p ≤ (2 : Int) + d256 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7293 (p : Pattern) (guard : d1 p = 1) : d136 p ≤ (2 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d136, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d136, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d136, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d136, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7294 (p : Pattern) (guard : d1 p = 1) : d939 p ≤ (2 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d939, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d939, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d939, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7293 p hg
    simpa only [d939, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7295 (p : Pattern) (guard : d4299 p = 1) : d940 p ≤ (2 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d940, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7294 p hg
    simpa only [d4299, d940, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d940, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4957 p hg
    simpa only [d4299, d940, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7296 (p : Pattern) (guard : d4432 p = 1) : d941 p ≤ (2 : Int) + d256 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7292 p hg
    simpa only [d4432, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7295 p hg
    simpa only [d4432, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7297 (p : Pattern) (guard : d4432 p = 1) : d942 p ≤ (2 : Int) + d4756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d942, d4756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7296 p hg
    simpa only [d942, d4756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d942, d4756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7289 p hg
    simpa only [d942, d4756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7298 (p : Pattern) (guard : d4432 p = 1) : d943 p ≤ (2 : Int) + d4757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d943, d4757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7297 p hg
    simpa only [d943, d4757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d943, d4757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d943, d4757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7299 (p : Pattern) (guard : d4432 p = 1) : d944 p ≤ (2 : Int) + d4758 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d944, d4758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7291 p hg
    simpa only [d944, d4758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d944, d4758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7298 p hg
    simpa only [d944, d4758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7300 (p : Pattern) (guard : d4432 p = 1) : d945 p ≤ (2 : Int) + d4759 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d945, d4759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7272 p hg
    simpa only [d945, d4759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d945, d4759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7299 p hg
    simpa only [d945, d4759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7301 (p : Pattern) (guard : d4432 p = 1) : d946 p ≤ (2 : Int) + d4760 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d946, d4760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7177 p hg
    simpa only [d946, d4760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d946, d4760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7300 p hg
    simpa only [d946, d4760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7302 (p : Pattern) (guard : d4432 p = 1) : d947 p ≤ (2 : Int) + d4761 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d947, d4761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7257 p hg
    simpa only [d947, d4761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d947, d4761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7301 p hg
    simpa only [d947, d4761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7303 (p : Pattern) (guard : d4432 p = 1) : d948 p ≤ (2 : Int) + d4762 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d948, d4762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7243 p hg
    simpa only [d948, d4762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d948, d4762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7302 p hg
    simpa only [d948, d4762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7304 (p : Pattern) (guard : d0 p = 1) : d792 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7305 (p : Pattern) (guard : d4301 p = 1) : d793 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d793, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6950 p hg
    simpa only [d4301, d793, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d793, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7304 p hg
    simpa only [d4301, d793, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7306 (p : Pattern) (guard : d0 p = 1) : d800 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7307 (p : Pattern) (guard : d4301 p = 1) : d801 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d801, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6954 p hg
    simpa only [d4301, d801, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d801, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7306 p hg
    simpa only [d4301, d801, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7308 (p : Pattern) (guard : d4301 p = 1) : d802 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d802, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7305 p hg
    simpa only [d802, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d802, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7307 p hg
    simpa only [d802, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7309 (p : Pattern) (guard : d0 p = 1) : d813 p ≤ (0 : Int) + d400 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7310 (p : Pattern) (guard : d4302 p = 1) : d814 p ≤ (0 : Int) + d517 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d814, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7308 p hg
    simpa only [d4302, d814, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d814, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7309 p hg
    simpa only [d4302, d814, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7311 (p : Pattern) (guard : d0 p = 1) : d805 p ≤ (0 : Int) + d530 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7312 (p : Pattern) (guard : d4301 p = 1) : d816 p ≤ (0 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d816, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6969 p hg
    simpa only [d4301, d816, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d816, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7311 p hg
    simpa only [d4301, d816, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7313 (p : Pattern) (guard : d0 p = 1) : d811 p ≤ (0 : Int) + d541 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7314 (p : Pattern) (guard : d4301 p = 1) : d818 p ≤ (0 : Int) + d542 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d818, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6973 p hg
    simpa only [d4301, d818, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d818, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7313 p hg
    simpa only [d4301, d818, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7315 (p : Pattern) (guard : d4301 p = 1) : d819 p ≤ (0 : Int) + d543 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d819, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7312 p hg
    simpa only [d819, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d819, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7314 p hg
    simpa only [d819, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7316 (p : Pattern) (guard : d0 p = 1) : d822 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7317 (p : Pattern) (guard : d4302 p = 1) : d823 p ≤ (0 : Int) + d544 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d823, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7315 p hg
    simpa only [d4302, d823, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d823, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d4302, d823, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7318 (p : Pattern) (guard : d4302 p = 1) : d824 p ≤ (0 : Int) + d545 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d824, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7310 p hg
    simpa only [d824, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d824, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7317 p hg
    simpa only [d824, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7319 (p : Pattern) (guard : d0 p = 1) : d826 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7320 (p : Pattern) (guard : d4301 p = 1) : d827 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d827, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6982 p hg
    simpa only [d4301, d827, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d827, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7319 p hg
    simpa only [d4301, d827, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7321 (p : Pattern) (guard : d4301 p = 1) : d829 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d829, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6986 p hg
    simpa only [d4301, d829, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d829, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7306 p hg
    simpa only [d4301, d829, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7322 (p : Pattern) (guard : d4301 p = 1) : d830 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d830, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7320 p hg
    simpa only [d830, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d830, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7321 p hg
    simpa only [d830, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7323 (p : Pattern) (guard : d0 p = 1) : d833 p ≤ (0 : Int) + d422 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7324 (p : Pattern) (guard : d4302 p = 1) : d834 p ≤ (0 : Int) + d546 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d834, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7322 p hg
    simpa only [d4302, d834, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d834, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7323 p hg
    simpa only [d4302, d834, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7325 (p : Pattern) (guard : d4301 p = 1) : d832 p ≤ (0 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d832, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6991 p hg
    simpa only [d4301, d832, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d832, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7311 p hg
    simpa only [d4301, d832, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7326 (p : Pattern) (guard : d4301 p = 1) : d812 p ≤ (0 : Int) + d542 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d812, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d4301, d812, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d812, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7313 p hg
    simpa only [d4301, d812, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7327 (p : Pattern) (guard : d4301 p = 1) : d833 p ≤ (0 : Int) + d543 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d833, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7325 p hg
    simpa only [d833, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d833, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7326 p hg
    simpa only [d833, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7328 (p : Pattern) (guard : d4302 p = 1) : d835 p ≤ (0 : Int) + d547 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d835, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7327 p hg
    simpa only [d4302, d835, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d835, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4302, d835, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7329 (p : Pattern) (guard : d4302 p = 1) : d836 p ≤ (0 : Int) + d548 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d836, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7324 p hg
    simpa only [d836, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d836, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7328 p hg
    simpa only [d836, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7330 (p : Pattern) (guard : d4302 p = 1) : d837 p ≤ (0 : Int) + d549 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d837, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7318 p hg
    simpa only [d837, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d837, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7329 p hg
    simpa only [d837, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7331 (p : Pattern) (guard : d4301 p = 1) : d839 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d839, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7000 p hg
    simpa only [d4301, d839, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d839, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7319 p hg
    simpa only [d4301, d839, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7332 (p : Pattern) (guard : d4301 p = 1) : d841 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d841, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7004 p hg
    simpa only [d4301, d841, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d841, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7306 p hg
    simpa only [d4301, d841, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7333 (p : Pattern) (guard : d4301 p = 1) : d842 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d842, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7331 p hg
    simpa only [d842, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d842, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7332 p hg
    simpa only [d842, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7334 (p : Pattern) (guard : d0 p = 1) : d845 p ≤ (0 : Int) + d439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7335 (p : Pattern) (guard : d4302 p = 1) : d846 p ≤ (0 : Int) + d550 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d846, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7333 p hg
    simpa only [d4302, d846, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d846, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7334 p hg
    simpa only [d4302, d846, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7336 (p : Pattern) (guard : d4301 p = 1) : d806 p ≤ (0 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d806, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6959 p hg
    simpa only [d4301, d806, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d806, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7311 p hg
    simpa only [d4301, d806, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7337 (p : Pattern) (guard : d4301 p = 1) : d813 p ≤ (0 : Int) + d543 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d813, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7336 p hg
    simpa only [d813, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d813, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7326 p hg
    simpa only [d813, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7338 (p : Pattern) (guard : d0 p = 1) : d822 p ≤ (0 : Int) + d441 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7339 (p : Pattern) (guard : d4302 p = 1) : d847 p ≤ (0 : Int) + d551 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d847, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7337 p hg
    simpa only [d4302, d847, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d847, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7338 p hg
    simpa only [d4302, d847, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7340 (p : Pattern) (guard : d4302 p = 1) : d848 p ≤ (0 : Int) + d552 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d848, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7335 p hg
    simpa only [d848, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d848, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7339 p hg
    simpa only [d848, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7341 (p : Pattern) (guard : d4301 p = 1) : d849 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d849, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6969 p hg
    simpa only [d4301, d849, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d849, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7319 p hg
    simpa only [d4301, d849, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7342 (p : Pattern) (guard : d4301 p = 1) : d850 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d850, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6973 p hg
    simpa only [d4301, d850, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d850, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7306 p hg
    simpa only [d4301, d850, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7343 (p : Pattern) (guard : d4301 p = 1) : d851 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d851, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7341 p hg
    simpa only [d851, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d851, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7342 p hg
    simpa only [d851, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7344 (p : Pattern) (guard : d0 p = 1) : d833 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7345 (p : Pattern) (guard : d4302 p = 1) : d852 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d852, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7343 p hg
    simpa only [d4302, d852, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d852, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7344 p hg
    simpa only [d4302, d852, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7346 (p : Pattern) (guard : d4302 p = 1) : d853 p ≤ (0 : Int) + d554 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d853, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7345 p hg
    simpa only [d853, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d853, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7328 p hg
    simpa only [d853, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7347 (p : Pattern) (guard : d4302 p = 1) : d854 p ≤ (0 : Int) + d555 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d854, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7340 p hg
    simpa only [d854, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d854, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7346 p hg
    simpa only [d854, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7348 (p : Pattern) (guard : d4302 p = 1) : d855 p ≤ (0 : Int) + d556 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d855, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7330 p hg
    simpa only [d855, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d855, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7347 p hg
    simpa only [d855, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7349 (p : Pattern) (guard : d0 p = 1) : d858 p ≤ (0 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7350 (p : Pattern) (guard : d4301 p = 1) : d859 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d859, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7025 p hg
    simpa only [d4301, d859, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d859, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7349 p hg
    simpa only [d4301, d859, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7351 (p : Pattern) (guard : d0 p = 1) : d865 p ≤ (0 : Int) + d145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7352 (p : Pattern) (guard : d4301 p = 1) : d866 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d866, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7029 p hg
    simpa only [d4301, d866, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d866, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7351 p hg
    simpa only [d4301, d866, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7353 (p : Pattern) (guard : d4301 p = 1) : d867 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d867, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7350 p hg
    simpa only [d867, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d867, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7352 p hg
    simpa only [d867, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7354 (p : Pattern) (guard : d0 p = 1) : d877 p ≤ (0 : Int) + d439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7355 (p : Pattern) (guard : d4302 p = 1) : d878 p ≤ (0 : Int) + d557 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d878, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7353 p hg
    simpa only [d4302, d878, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d878, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7354 p hg
    simpa only [d4302, d878, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7356 (p : Pattern) (guard : d0 p = 1) : d870 p ≤ (0 : Int) + d568 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7357 (p : Pattern) (guard : d4301 p = 1) : d880 p ≤ (0 : Int) + d569 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d880, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7044 p hg
    simpa only [d4301, d880, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d880, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7356 p hg
    simpa only [d4301, d880, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7358 (p : Pattern) (guard : d0 p = 1) : d875 p ≤ (0 : Int) + d577 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7359 (p : Pattern) (guard : d4301 p = 1) : d876 p ≤ (0 : Int) + d578 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d876, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7038 p hg
    simpa only [d4301, d876, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d876, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7358 p hg
    simpa only [d4301, d876, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7360 (p : Pattern) (guard : d4301 p = 1) : d881 p ≤ (0 : Int) + d579 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d881, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7357 p hg
    simpa only [d881, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d881, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7359 p hg
    simpa only [d881, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7361 (p : Pattern) (guard : d4302 p = 1) : d882 p ≤ (0 : Int) + d580 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d882, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7360 p hg
    simpa only [d4302, d882, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d882, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d4302, d882, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7362 (p : Pattern) (guard : d4302 p = 1) : d883 p ≤ (0 : Int) + d581 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d883, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7355 p hg
    simpa only [d883, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d883, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7361 p hg
    simpa only [d883, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7363 (p : Pattern) (guard : d4301 p = 1) : d885 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d885, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7051 p hg
    simpa only [d4301, d885, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d885, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7349 p hg
    simpa only [d4301, d885, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7364 (p : Pattern) (guard : d4301 p = 1) : d887 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d887, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7055 p hg
    simpa only [d4301, d887, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d887, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7351 p hg
    simpa only [d4301, d887, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7365 (p : Pattern) (guard : d4301 p = 1) : d888 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d888, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7363 p hg
    simpa only [d888, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d888, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7364 p hg
    simpa only [d888, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7366 (p : Pattern) (guard : d0 p = 1) : d891 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7367 (p : Pattern) (guard : d4302 p = 1) : d892 p ≤ (0 : Int) + d582 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d892, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7365 p hg
    simpa only [d4302, d892, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d892, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7366 p hg
    simpa only [d4302, d892, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7368 (p : Pattern) (guard : d4301 p = 1) : d890 p ≤ (0 : Int) + d569 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d890, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7060 p hg
    simpa only [d4301, d890, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d890, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7356 p hg
    simpa only [d4301, d890, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7369 (p : Pattern) (guard : d4301 p = 1) : d891 p ≤ (0 : Int) + d579 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d891, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7368 p hg
    simpa only [d891, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d891, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7359 p hg
    simpa only [d891, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7370 (p : Pattern) (guard : d4302 p = 1) : d893 p ≤ (0 : Int) + d583 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d893, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7369 p hg
    simpa only [d4302, d893, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d893, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4302, d893, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7371 (p : Pattern) (guard : d4302 p = 1) : d894 p ≤ (0 : Int) + d584 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d894, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7367 p hg
    simpa only [d894, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d894, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7370 p hg
    simpa only [d894, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7372 (p : Pattern) (guard : d4302 p = 1) : d895 p ≤ (0 : Int) + d585 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d895, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7362 p hg
    simpa only [d895, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d895, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7371 p hg
    simpa only [d895, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7373 (p : Pattern) (guard : d4302 p = 1) : d896 p ≤ (0 : Int) + d586 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d896, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7330 p hg
    simpa only [d896, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d896, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7372 p hg
    simpa only [d896, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7374 (p : Pattern) (guard : d4302 p = 1) : d897 p ≤ (0 : Int) + d587 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d897, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7348 p hg
    simpa only [d897, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d897, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7373 p hg
    simpa only [d897, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7375 (p : Pattern) (guard : d0 p = 1) : d906 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7376 (p : Pattern) (guard : d4302 p = 1) : d907 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d907, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7343 p hg
    simpa only [d4302, d907, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d907, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7375 p hg
    simpa only [d4302, d907, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7377 (p : Pattern) (guard : d0 p = 1) : d900 p ≤ (0 : Int) + d595 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7378 (p : Pattern) (guard : d4301 p = 1) : d901 p ≤ (0 : Int) + d596 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d901, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7070 p hg
    simpa only [d4301, d901, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d901, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7377 p hg
    simpa only [d4301, d901, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7379 (p : Pattern) (guard : d0 p = 1) : d904 p ≤ (0 : Int) + d603 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7380 (p : Pattern) (guard : d4301 p = 1) : d905 p ≤ (0 : Int) + d604 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d905, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7074 p hg
    simpa only [d4301, d905, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d905, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7379 p hg
    simpa only [d4301, d905, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7381 (p : Pattern) (guard : d4301 p = 1) : d906 p ≤ (0 : Int) + d605 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d906, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7378 p hg
    simpa only [d906, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d906, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7380 p hg
    simpa only [d906, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7382 (p : Pattern) (guard : d4302 p = 1) : d908 p ≤ (0 : Int) + d606 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d908, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7381 p hg
    simpa only [d4302, d908, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d908, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4302, d908, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7383 (p : Pattern) (guard : d4302 p = 1) : d909 p ≤ (0 : Int) + d607 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d909, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7376 p hg
    simpa only [d909, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d909, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7382 p hg
    simpa only [d909, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7384 (p : Pattern) (guard : d4302 p = 1) : d910 p ≤ (0 : Int) + d608 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d910, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7340 p hg
    simpa only [d910, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d910, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7383 p hg
    simpa only [d910, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7385 (p : Pattern) (guard : d4302 p = 1) : d911 p ≤ (0 : Int) + d609 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d911, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7330 p hg
    simpa only [d911, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d911, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7384 p hg
    simpa only [d911, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7386 (p : Pattern) (guard : d0 p = 1) : d865 p ≤ (0 : Int) + d218 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7387 (p : Pattern) (guard : d4301 p = 1) : d913 p ≤ (0 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d913, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7084 p hg
    simpa only [d4301, d913, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d913, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7386 p hg
    simpa only [d4301, d913, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7388 (p : Pattern) (guard : d4301 p = 1) : d914 p ≤ (0 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d914, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7350 p hg
    simpa only [d914, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d914, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7387 p hg
    simpa only [d914, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7389 (p : Pattern) (guard : d0 p = 1) : d917 p ≤ (0 : Int) + d457 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7390 (p : Pattern) (guard : d4302 p = 1) : d918 p ≤ (0 : Int) + d610 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d918, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7388 p hg
    simpa only [d4302, d918, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d918, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7389 p hg
    simpa only [d4302, d918, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7391 (p : Pattern) (guard : d0 p = 1) : d875 p ≤ (0 : Int) + d614 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7392 (p : Pattern) (guard : d4301 p = 1) : d916 p ≤ (0 : Int) + d615 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d916, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7088 p hg
    simpa only [d4301, d916, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d916, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7391 p hg
    simpa only [d4301, d916, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7393 (p : Pattern) (guard : d4301 p = 1) : d919 p ≤ (0 : Int) + d616 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d919, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7357 p hg
    simpa only [d919, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d919, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7392 p hg
    simpa only [d919, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7394 (p : Pattern) (guard : d4302 p = 1) : d920 p ≤ (0 : Int) + d617 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d920, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7393 p hg
    simpa only [d4302, d920, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d920, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d4302, d920, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7395 (p : Pattern) (guard : d4302 p = 1) : d921 p ≤ (0 : Int) + d618 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d921, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7390 p hg
    simpa only [d921, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d921, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7394 p hg
    simpa only [d921, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7396 (p : Pattern) (guard : d0 p = 1) : d923 p ≤ (0 : Int) + d280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7397 (p : Pattern) (guard : d4301 p = 1) : d924 p ≤ (0 : Int) + d281 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d924, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7051 p hg
    simpa only [d4301, d924, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d924, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7396 p hg
    simpa only [d4301, d924, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7398 (p : Pattern) (guard : d0 p = 1) : d927 p ≤ (0 : Int) + d288 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7399 (p : Pattern) (guard : d4301 p = 1) : d928 p ≤ (0 : Int) + d289 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d928, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7088 p hg
    simpa only [d4301, d928, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d928, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7398 p hg
    simpa only [d4301, d928, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7400 (p : Pattern) (guard : d4301 p = 1) : d929 p ≤ (0 : Int) + d290 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d929, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7397 p hg
    simpa only [d929, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d929, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7399 p hg
    simpa only [d929, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7401 (p : Pattern) (guard : d0 p = 1) : d936 p ≤ (0 : Int) + d473 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7402 (p : Pattern) (guard : d4302 p = 1) : d937 p ≤ (0 : Int) + d619 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d937, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7400 p hg
    simpa only [d4302, d937, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d937, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7401 p hg
    simpa only [d4302, d937, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7403 (p : Pattern) (guard : d0 p = 1) : d940 p ≤ (0 : Int) + d630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7404 (p : Pattern) (guard : d4301 p = 1) : d941 p ≤ (0 : Int) + d631 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d941, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7110 p hg
    simpa only [d4301, d941, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d941, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7403 p hg
    simpa only [d4301, d941, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7405 (p : Pattern) (guard : d0 p = 1) : d934 p ≤ (0 : Int) + d644 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7406 (p : Pattern) (guard : d4301 p = 1) : d935 p ≤ (0 : Int) + d645 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d935, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7104 p hg
    simpa only [d4301, d935, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d935, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7405 p hg
    simpa only [d4301, d935, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7407 (p : Pattern) (guard : d4301 p = 1) : d942 p ≤ (0 : Int) + d646 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d942, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7404 p hg
    simpa only [d942, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d942, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7406 p hg
    simpa only [d942, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7408 (p : Pattern) (guard : d4302 p = 1) : d943 p ≤ (0 : Int) + d647 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d943, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7407 p hg
    simpa only [d4302, d943, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d943, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4302, d943, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7409 (p : Pattern) (guard : d4302 p = 1) : d944 p ≤ (0 : Int) + d648 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d944, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7402 p hg
    simpa only [d944, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d944, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7408 p hg
    simpa only [d944, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7410 (p : Pattern) (guard : d4302 p = 1) : d945 p ≤ (0 : Int) + d649 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d945, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7395 p hg
    simpa only [d945, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d945, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7409 p hg
    simpa only [d945, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7411 (p : Pattern) (guard : d4302 p = 1) : d946 p ≤ (0 : Int) + d650 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d946, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7330 p hg
    simpa only [d946, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d946, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7410 p hg
    simpa only [d946, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7412 (p : Pattern) (guard : d4302 p = 1) : d947 p ≤ (0 : Int) + d651 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d947, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7385 p hg
    simpa only [d947, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d947, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7411 p hg
    simpa only [d947, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7413 (p : Pattern) (guard : d4302 p = 1) : d948 p ≤ (0 : Int) + d652 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d948, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7374 p hg
    simpa only [d948, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d948, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7412 p hg
    simpa only [d948, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7414 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d22 p := by
  omega
theorem compare7415 (p : Pattern) (guard : d0 p = 1) : d362 p ≤ (0 : Int) + d1399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7416 (p : Pattern) (guard : d4670 p = 1) : d790 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d790, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d790, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d790, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7415 p hg
    simpa only [d4670, d790, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7417 (p : Pattern) (guard : d0 p = 1) : d79 p ≤ (0 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7418 (p : Pattern) (guard : d4395 p = 1) : d791 p ≤ (0 : Int) + d1401 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d791, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d791, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d791, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7417 p hg
    simpa only [d4395, d791, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7419 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
