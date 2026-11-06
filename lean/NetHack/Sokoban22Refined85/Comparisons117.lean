/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons116
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16380 (p : Pattern) (guard : d4474 p = 1) : d1754 p ≤ (0 : Int) + d2928 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1754, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16378 p hg
    simpa only [d1754, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1754, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16379 p hg
    simpa only [d1754, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16381 (p : Pattern) (guard : d4474 p = 1) : d1755 p ≤ (0 : Int) + d2929 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1755, d2929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16340 p hg
    simpa only [d1755, d2929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1755, d2929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16380 p hg
    simpa only [d1755, d2929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16382 (p : Pattern) (guard : d4474 p = 1) : d41 p ≤ (0 : Int) + d2930 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d41, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d4474, d41, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d41, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12737 p hg
    simpa only [d4474, d41, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16383 (p : Pattern) (guard : d4474 p = 1) : d1756 p ≤ (0 : Int) + d2931 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1756, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16382 p hg
    simpa only [d1756, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1756, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16356 p hg
    simpa only [d1756, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16384 (p : Pattern) (guard : d4474 p = 1) : d1757 p ≤ (0 : Int) + d2932 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1757, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16383 p hg
    simpa only [d1757, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1757, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1757, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16385 (p : Pattern) (guard : d4474 p = 1) : d1758 p ≤ (0 : Int) + d2933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1758, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16381 p hg
    simpa only [d1758, d2933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1758, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16384 p hg
    simpa only [d1758, d2933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16386 (p : Pattern) (guard : d4474 p = 1) : d1759 p ≤ (0 : Int) + d2934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1759, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16377 p hg
    simpa only [d1759, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1759, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16385 p hg
    simpa only [d1759, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16387 (p : Pattern) (guard : d4474 p = 1) : d32 p ≤ (0 : Int) + d2935 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d32, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4474, d32, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d32, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12732 p hg
    simpa only [d4474, d32, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16388 (p : Pattern) (guard : d4474 p = 1) : d1760 p ≤ (0 : Int) + d2936 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1760, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16387 p hg
    simpa only [d1760, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1760, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1760, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16389 (p : Pattern) (guard : d4474 p = 1) : d1761 p ≤ (0 : Int) + d2937 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1761, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16354 p hg
    simpa only [d1761, d2937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1761, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16388 p hg
    simpa only [d1761, d2937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16390 (p : Pattern) (guard : d4474 p = 1) : d1762 p ≤ (0 : Int) + d2938 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1762, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16359 p hg
    simpa only [d1762, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1762, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16364 p hg
    simpa only [d1762, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16391 (p : Pattern) (guard : d4474 p = 1) : d1763 p ≤ (0 : Int) + d2939 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1763, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16389 p hg
    simpa only [d1763, d2939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1763, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16390 p hg
    simpa only [d1763, d2939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16392 (p : Pattern) (guard : d4474 p = 1) : d277 p ≤ (0 : Int) + d2940 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d277, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16378 p hg
    simpa only [d277, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d277, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d277, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16393 (p : Pattern) (guard : d4474 p = 1) : d1764 p ≤ (0 : Int) + d2941 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1764, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16359 p hg
    simpa only [d1764, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1764, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16392 p hg
    simpa only [d1764, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16394 (p : Pattern) (guard : d4474 p = 1) : d538 p ≤ (0 : Int) + d2942 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d538, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16382 p hg
    simpa only [d538, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d538, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d538, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16395 (p : Pattern) (guard : d4474 p = 1) : d539 p ≤ (0 : Int) + d2943 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d539, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16394 p hg
    simpa only [d539, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d539, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d539, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16396 (p : Pattern) (guard : d4474 p = 1) : d1765 p ≤ (0 : Int) + d2944 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1765, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16393 p hg
    simpa only [d1765, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1765, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16395 p hg
    simpa only [d1765, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16397 (p : Pattern) (guard : d4474 p = 1) : d1766 p ≤ (0 : Int) + d2945 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1766, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16391 p hg
    simpa only [d1766, d2945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1766, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16396 p hg
    simpa only [d1766, d2945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16398 (p : Pattern) (guard : d4474 p = 1) : d1767 p ≤ (0 : Int) + d2946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1767, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16386 p hg
    simpa only [d1767, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1767, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16397 p hg
    simpa only [d1767, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16399 (p : Pattern) (guard : d4474 p = 1) : d1768 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1768, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16368 p hg
    simpa only [d1768, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1768, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16398 p hg
    simpa only [d1768, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16400 (p : Pattern) (guard : d4474 p = 1) : d15 p ≤ (0 : Int) + d2948 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d15, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d15, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d15, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12987 p hg
    simpa only [d4474, d15, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16401 (p : Pattern) (guard : d4474 p = 1) : d1773 p ≤ (0 : Int) + d1773 p := by
  omega
theorem compare16402 (p : Pattern) (guard : d4474 p = 1) : d1774 p ≤ (0 : Int) + d2949 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1774, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16400 p hg
    simpa only [d1774, d2949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1774, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16401 p hg
    simpa only [d1774, d2949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16403 (p : Pattern) (guard : d4474 p = 1) : d15 p ≤ (0 : Int) + d2950 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d15, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d15, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d15, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12989 p hg
    simpa only [d4474, d15, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16404 (p : Pattern) (guard : d4474 p = 1) : d1782 p ≤ (0 : Int) + d1782 p := by
  omega
theorem compare16405 (p : Pattern) (guard : d4474 p = 1) : d1783 p ≤ (0 : Int) + d2951 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1783, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16403 p hg
    simpa only [d1783, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1783, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16404 p hg
    simpa only [d1783, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16406 (p : Pattern) (guard : d4474 p = 1) : d1784 p ≤ (0 : Int) + d2952 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1784, d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16402 p hg
    simpa only [d1784, d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1784, d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16405 p hg
    simpa only [d1784, d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16407 (p : Pattern) (guard : d4474 p = 1) : d1789 p ≤ (0 : Int) + d1789 p := by
  omega
theorem compare16408 (p : Pattern) (guard : d4474 p = 1) : d1790 p ≤ (0 : Int) + d2953 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1790, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16350 p hg
    simpa only [d1790, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1790, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16407 p hg
    simpa only [d1790, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16409 (p : Pattern) (guard : d4474 p = 1) : d1798 p ≤ (0 : Int) + d1798 p := by
  omega
theorem compare16410 (p : Pattern) (guard : d4474 p = 1) : d1799 p ≤ (0 : Int) + d2954 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1799, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16358 p hg
    simpa only [d1799, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1799, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16409 p hg
    simpa only [d1799, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16411 (p : Pattern) (guard : d4474 p = 1) : d1800 p ≤ (0 : Int) + d2955 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1800, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16408 p hg
    simpa only [d1800, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1800, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16410 p hg
    simpa only [d1800, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16412 (p : Pattern) (guard : d4474 p = 1) : d1801 p ≤ (0 : Int) + d2956 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1801, d2956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16406 p hg
    simpa only [d1801, d2956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1801, d2956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16411 p hg
    simpa only [d1801, d2956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16413 (p : Pattern) (guard : d4474 p = 1) : d1804 p ≤ (0 : Int) + d1804 p := by
  omega
theorem compare16414 (p : Pattern) (guard : d4474 p = 1) : d1805 p ≤ (0 : Int) + d2957 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1805, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16343 p hg
    simpa only [d1805, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1805, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16413 p hg
    simpa only [d1805, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16415 (p : Pattern) (guard : d4474 p = 1) : d1806 p ≤ (0 : Int) + d2958 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1806, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16414 p hg
    simpa only [d1806, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1806, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1806, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16416 (p : Pattern) (guard : d4474 p = 1) : d1807 p ≤ (0 : Int) + d2959 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1807, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16411 p hg
    simpa only [d1807, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1807, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16415 p hg
    simpa only [d1807, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16417 (p : Pattern) (guard : d4474 p = 1) : d1808 p ≤ (0 : Int) + d2960 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1808, d2960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16412 p hg
    simpa only [d1808, d2960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1808, d2960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16416 p hg
    simpa only [d1808, d2960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16418 (p : Pattern) (guard : d4474 p = 1) : d1809 p ≤ (0 : Int) + d2961 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1809, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16387 p hg
    simpa only [d1809, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1809, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16351 p hg
    simpa only [d1809, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16419 (p : Pattern) (guard : d4474 p = 1) : d36 p ≤ (0 : Int) + d2962 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d36, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d4474, d36, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d36, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12734 p hg
    simpa only [d4474, d36, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16420 (p : Pattern) (guard : d4474 p = 1) : d1810 p ≤ (0 : Int) + d2963 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1810, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16419 p hg
    simpa only [d1810, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1810, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16353 p hg
    simpa only [d1810, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16421 (p : Pattern) (guard : d4474 p = 1) : d1811 p ≤ (0 : Int) + d2964 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1811, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16418 p hg
    simpa only [d1811, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1811, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16420 p hg
    simpa only [d1811, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16422 (p : Pattern) (guard : d4474 p = 1) : d1812 p ≤ (0 : Int) + d2965 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1812, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16421 p hg
    simpa only [d1812, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1812, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16384 p hg
    simpa only [d1812, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16423 (p : Pattern) (guard : d4474 p = 1) : d1813 p ≤ (0 : Int) + d2966 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1813, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16422 p hg
    simpa only [d1813, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1813, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1813, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16424 (p : Pattern) (guard : d4474 p = 1) : d1814 p ≤ (0 : Int) + d2967 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1814, d2967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16417 p hg
    simpa only [d1814, d2967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1814, d2967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16423 p hg
    simpa only [d1814, d2967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16425 (p : Pattern) (guard : d4474 p = 1) : d1815 p ≤ (0 : Int) + d2968 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1815, d2968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16405 p hg
    simpa only [d1815, d2968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1815, d2968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16418 p hg
    simpa only [d1815, d2968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16426 (p : Pattern) (guard : d4474 p = 1) : d1816 p ≤ (0 : Int) + d2969 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1816, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16410 p hg
    simpa only [d1816, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1816, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16414 p hg
    simpa only [d1816, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16427 (p : Pattern) (guard : d4474 p = 1) : d1817 p ≤ (0 : Int) + d2970 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1817, d2970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16425 p hg
    simpa only [d1817, d2970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1817, d2970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16426 p hg
    simpa only [d1817, d2970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16428 (p : Pattern) (guard : d4474 p = 1) : d1818 p ≤ (0 : Int) + d2971 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1818, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16410 p hg
    simpa only [d1818, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1818, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16380 p hg
    simpa only [d1818, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16429 (p : Pattern) (guard : d4474 p = 1) : d1819 p ≤ (0 : Int) + d2972 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1819, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16428 p hg
    simpa only [d1819, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1819, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16384 p hg
    simpa only [d1819, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16430 (p : Pattern) (guard : d4474 p = 1) : d1820 p ≤ (0 : Int) + d2973 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1820, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16427 p hg
    simpa only [d1820, d2973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1820, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16429 p hg
    simpa only [d1820, d2973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16431 (p : Pattern) (guard : d4474 p = 1) : d1821 p ≤ (0 : Int) + d2974 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1821, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16420 p hg
    simpa only [d1821, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1821, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1821, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16432 (p : Pattern) (guard : d4474 p = 1) : d1822 p ≤ (0 : Int) + d2975 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1822, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16431 p hg
    simpa only [d1822, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1822, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1822, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16433 (p : Pattern) (guard : d4474 p = 1) : d1823 p ≤ (0 : Int) + d2976 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1823, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16432 p hg
    simpa only [d1823, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1823, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1823, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16434 (p : Pattern) (guard : d4474 p = 1) : d1824 p ≤ (0 : Int) + d2977 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1824, d2977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16430 p hg
    simpa only [d1824, d2977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1824, d2977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16433 p hg
    simpa only [d1824, d2977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16435 (p : Pattern) (guard : d4474 p = 1) : d1825 p ≤ (0 : Int) + d2978 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1825, d2978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16424 p hg
    simpa only [d1825, d2978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1825, d2978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16434 p hg
    simpa only [d1825, d2978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16436 (p : Pattern) (guard : d4474 p = 1) : d1826 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1826, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16399 p hg
    simpa only [d1826, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1826, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16435 p hg
    simpa only [d1826, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16437 (p : Pattern) (guard : d4474 p = 1) : d1827 p ≤ (0 : Int) + d2980 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1827, d2980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16414 p hg
    simpa only [d1827, d2980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1827, d2980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16383 p hg
    simpa only [d1827, d2980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16438 (p : Pattern) (guard : d4474 p = 1) : d1828 p ≤ (0 : Int) + d2981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1828, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16437 p hg
    simpa only [d1828, d2981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1828, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16384 p hg
    simpa only [d1828, d2981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16439 (p : Pattern) (guard : d4474 p = 1) : d1829 p ≤ (0 : Int) + d2982 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1829, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16384 p hg
    simpa only [d1829, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1829, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1829, d2982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16440 (p : Pattern) (guard : d4474 p = 1) : d1830 p ≤ (0 : Int) + d2983 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1830, d2983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16438 p hg
    simpa only [d1830, d2983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1830, d2983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16439 p hg
    simpa only [d1830, d2983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16441 (p : Pattern) (guard : d4474 p = 1) : d1831 p ≤ (0 : Int) + d2984 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1831, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16439 p hg
    simpa only [d1831, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1831, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1831, d2984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16442 (p : Pattern) (guard : d4474 p = 1) : d1832 p ≤ (0 : Int) + d2985 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1832, d2985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16440 p hg
    simpa only [d1832, d2985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1832, d2985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16441 p hg
    simpa only [d1832, d2985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16443 (p : Pattern) (guard : d4474 p = 1) : d1833 p ≤ (0 : Int) + d2986 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1833, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16441 p hg
    simpa only [d1833, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1833, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1833, d2986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16444 (p : Pattern) (guard : d4474 p = 1) : d1834 p ≤ (0 : Int) + d2987 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1834, d2987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16442 p hg
    simpa only [d1834, d2987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1834, d2987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16443 p hg
    simpa only [d1834, d2987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16445 (p : Pattern) (guard : d4474 p = 1) : d1835 p ≤ (0 : Int) + d2988 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1835, d2988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16435 p hg
    simpa only [d1835, d2988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1835, d2988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16444 p hg
    simpa only [d1835, d2988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16446 (p : Pattern) (guard : d4474 p = 1) : d1836 p ≤ (0 : Int) + d2989 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1836, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16436 p hg
    simpa only [d1836, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1836, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16445 p hg
    simpa only [d1836, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16447 (p : Pattern) (guard : d4474 p = 1) : d1837 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16334 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16337 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16448 (p : Pattern) (guard : d4474 p = 1) : d1838 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1838, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16447 p hg
    simpa only [d1838, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1838, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16341 p hg
    simpa only [d1838, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16449 (p : Pattern) (guard : d4474 p = 1) : d1839 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1839, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16448 p hg
    simpa only [d1839, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1839, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16348 p hg
    simpa only [d1839, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16450 (p : Pattern) (guard : d4474 p = 1) : d1840 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1840, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16449 p hg
    simpa only [d1840, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1840, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16367 p hg
    simpa only [d1840, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16451 (p : Pattern) (guard : d4474 p = 1) : d1841 p ≤ (0 : Int) + d2924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1841, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16337 p hg
    simpa only [d1841, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1841, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16374 p hg
    simpa only [d1841, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16452 (p : Pattern) (guard : d4474 p = 1) : d1842 p ≤ (0 : Int) + d2926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1842, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16451 p hg
    simpa only [d1842, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1842, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16376 p hg
    simpa only [d1842, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16453 (p : Pattern) (guard : d4474 p = 1) : d1843 p ≤ (0 : Int) + d2934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1843, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16452 p hg
    simpa only [d1843, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1843, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16385 p hg
    simpa only [d1843, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16454 (p : Pattern) (guard : d4474 p = 1) : d1844 p ≤ (0 : Int) + d2946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1844, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16453 p hg
    simpa only [d1844, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1844, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16397 p hg
    simpa only [d1844, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16455 (p : Pattern) (guard : d4474 p = 1) : d1845 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1845, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16450 p hg
    simpa only [d1845, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1845, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16454 p hg
    simpa only [d1845, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16456 (p : Pattern) (guard : d4474 p = 1) : d1846 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1846, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16455 p hg
    simpa only [d1846, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1846, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16435 p hg
    simpa only [d1846, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16457 (p : Pattern) (guard : d4474 p = 1) : d1847 p ≤ (0 : Int) + d2990 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1847, d2990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16435 p hg
    simpa only [d1847, d2990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1847, d2990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1847, d2990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16458 (p : Pattern) (guard : d4474 p = 1) : d1848 p ≤ (0 : Int) + d2991 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1848, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16456 p hg
    simpa only [d1848, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1848, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16457 p hg
    simpa only [d1848, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16459 (p : Pattern) (guard : d4474 p = 1) : d1849 p ≤ (0 : Int) + d2992 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1849, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16446 p hg
    simpa only [d1849, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1849, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16458 p hg
    simpa only [d1849, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16460 (p : Pattern) (guard : d0 p = 1) : d358 p ≤ (0 : Int) + d1772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16461 (p : Pattern) (guard : d4474 p = 1) : d1850 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1850, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1850, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1850, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16460 p hg
    simpa only [d4474, d1850, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16462 (p : Pattern) (guard : d4474 p = 1) : d1851 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1851, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16461 p hg
    simpa only [d1851, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1851, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d1851, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16463 (p : Pattern) (guard : d4474 p = 1) : d1852 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16462 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16337 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16464 (p : Pattern) (guard : d4474 p = 1) : d1853 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1853, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16463 p hg
    simpa only [d1853, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1853, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16341 p hg
    simpa only [d1853, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16465 (p : Pattern) (guard : d4474 p = 1) : d1854 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1854, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16464 p hg
    simpa only [d1854, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1854, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16348 p hg
    simpa only [d1854, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16466 (p : Pattern) (guard : d4474 p = 1) : d1855 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1855, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16465 p hg
    simpa only [d1855, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1855, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16367 p hg
    simpa only [d1855, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16467 (p : Pattern) (guard : d4474 p = 1) : d1856 p ≤ (0 : Int) + d2924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1856, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16334 p hg
    simpa only [d1856, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1856, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16374 p hg
    simpa only [d1856, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16468 (p : Pattern) (guard : d4474 p = 1) : d1857 p ≤ (0 : Int) + d2926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1857, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16467 p hg
    simpa only [d1857, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1857, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16376 p hg
    simpa only [d1857, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16469 (p : Pattern) (guard : d4474 p = 1) : d1858 p ≤ (0 : Int) + d2934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1858, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16468 p hg
    simpa only [d1858, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1858, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16385 p hg
    simpa only [d1858, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16470 (p : Pattern) (guard : d4474 p = 1) : d1859 p ≤ (0 : Int) + d2946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1859, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16469 p hg
    simpa only [d1859, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1859, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16397 p hg
    simpa only [d1859, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16471 (p : Pattern) (guard : d4474 p = 1) : d1860 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1860, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16466 p hg
    simpa only [d1860, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1860, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16470 p hg
    simpa only [d1860, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16472 (p : Pattern) (guard : d4474 p = 1) : d1861 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1861, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16471 p hg
    simpa only [d1861, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1861, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16435 p hg
    simpa only [d1861, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16473 (p : Pattern) (guard : d4474 p = 1) : d1862 p ≤ (0 : Int) + d2989 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1862, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16472 p hg
    simpa only [d1862, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1862, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16445 p hg
    simpa only [d1862, d2989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16474 (p : Pattern) (guard : d4474 p = 1) : d1863 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1863, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16337 p hg
    simpa only [d1863, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1863, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16341 p hg
    simpa only [d1863, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16475 (p : Pattern) (guard : d4474 p = 1) : d1864 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1864, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16474 p hg
    simpa only [d1864, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1864, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16348 p hg
    simpa only [d1864, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16476 (p : Pattern) (guard : d4474 p = 1) : d1865 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1865, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16475 p hg
    simpa only [d1865, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1865, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16367 p hg
    simpa only [d1865, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16477 (p : Pattern) (guard : d4474 p = 1) : d1866 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1866, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16476 p hg
    simpa only [d1866, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1866, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16454 p hg
    simpa only [d1866, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16478 (p : Pattern) (guard : d4474 p = 1) : d1867 p ≤ (0 : Int) + d2979 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1867, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16477 p hg
    simpa only [d1867, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1867, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16435 p hg
    simpa only [d1867, d2979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16479 (p : Pattern) (guard : d4474 p = 1) : d1868 p ≤ (0 : Int) + d2991 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1868, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16478 p hg
    simpa only [d1868, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1868, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16457 p hg
    simpa only [d1868, d2991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16480 (p : Pattern) (guard : d4474 p = 1) : d1869 p ≤ (0 : Int) + d2992 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1869, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16473 p hg
    simpa only [d1869, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1869, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16479 p hg
    simpa only [d1869, d2992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16481 (p : Pattern) (guard : d4474 p = 1) : d1870 p ≤ (0 : Int) + d2992 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16459 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16480 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16482 (p : Pattern) (guard : d0 p = 1) : d358 p ≤ (0 : Int) + d1942 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16483 (p : Pattern) (guard : d4474 p = 1) : d1871 p ≤ (0 : Int) + d2993 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1871, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d1871, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1871, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16482 p hg
    simpa only [d4474, d1871, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16484 (p : Pattern) (guard : d4474 p = 1) : d1876 p ≤ (0 : Int) + d1876 p := by
  omega
theorem compare16485 (p : Pattern) (guard : d4474 p = 1) : d1877 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1877, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16483 p hg
    simpa only [d1877, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1877, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16484 p hg
    simpa only [d1877, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16486 (p : Pattern) (guard : d4474 p = 1) : d104 p ≤ (0 : Int) + d2993 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d104, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d104, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d104, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12903 p hg
    simpa only [d4474, d104, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16487 (p : Pattern) (guard : d4474 p = 1) : d1878 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1878, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16486 p hg
    simpa only [d1878, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1878, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16484 p hg
    simpa only [d1878, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16488 (p : Pattern) (guard : d4474 p = 1) : d1879 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16485 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16487 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16489 (p : Pattern) (guard : d4474 p = 1) : d108 p ≤ (0 : Int) + d2995 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d108, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4474, d108, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d108, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13055 p hg
    simpa only [d4474, d108, d2995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16490 (p : Pattern) (guard : d4474 p = 1) : d1884 p ≤ (0 : Int) + d1884 p := by
  omega
theorem compare16491 (p : Pattern) (guard : d4474 p = 1) : d1885 p ≤ (0 : Int) + d2996 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1885, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16489 p hg
    simpa only [d1885, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1885, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16490 p hg
    simpa only [d1885, d2996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16492 (p : Pattern) (guard : d4474 p = 1) : d1886 p ≤ (0 : Int) + d2997 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1886, d2997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16487 p hg
    simpa only [d1886, d2997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1886, d2997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16491 p hg
    simpa only [d1886, d2997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16493 (p : Pattern) (guard : d4474 p = 1) : d1887 p ≤ (0 : Int) + d2998 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1887, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16488 p hg
    simpa only [d1887, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1887, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16492 p hg
    simpa only [d1887, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16494 (p : Pattern) (guard : d4474 p = 1) : d1888 p ≤ (0 : Int) + d2999 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1888, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16380 p hg
    simpa only [d1888, d2999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1888, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1888, d2999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16495 (p : Pattern) (guard : d4474 p = 1) : d1889 p ≤ (0 : Int) + d3000 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1889, d3000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16492 p hg
    simpa only [d1889, d3000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1889, d3000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d1889, d3000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16496 (p : Pattern) (guard : d4474 p = 1) : d1890 p ≤ (0 : Int) + d3001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1890, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d1890, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1890, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d1890, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16497 (p : Pattern) (guard : d4474 p = 1) : d104 p ≤ (0 : Int) + d3002 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d104, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d104, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d104, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12908 p hg
    simpa only [d4474, d104, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16498 (p : Pattern) (guard : d4474 p = 1) : d1899 p ≤ (0 : Int) + d1899 p := by
  omega
theorem compare16499 (p : Pattern) (guard : d4474 p = 1) : d1900 p ≤ (0 : Int) + d3003 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1900, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d1900, d3003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1900, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d1900, d3003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16500 (p : Pattern) (guard : d4474 p = 1) : d1906 p ≤ (0 : Int) + d1906 p := by
  omega
theorem compare16501 (p : Pattern) (guard : d4474 p = 1) : d1907 p ≤ (0 : Int) + d3004 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1907, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d1907, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1907, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16500 p hg
    simpa only [d1907, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16502 (p : Pattern) (guard : d4474 p = 1) : d1908 p ≤ (0 : Int) + d3005 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1908, d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d1908, d3005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1908, d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d1908, d3005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16503 (p : Pattern) (guard : d4474 p = 1) : d1909 p ≤ (0 : Int) + d3006 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1909, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d1909, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1909, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1909, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16504 (p : Pattern) (guard : d4474 p = 1) : d108 p ≤ (0 : Int) + d3007 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d108, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4474, d108, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d108, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12910 p hg
    simpa only [d4474, d108, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16505 (p : Pattern) (guard : d4474 p = 1) : d1910 p ≤ (0 : Int) + d3008 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1910, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16504 p hg
    simpa only [d1910, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1910, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1910, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16506 (p : Pattern) (guard : d4474 p = 1) : d1911 p ≤ (0 : Int) + d3009 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1911, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d1911, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1911, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16505 p hg
    simpa only [d1911, d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16507 (p : Pattern) (guard : d4474 p = 1) : d1912 p ≤ (0 : Int) + d3010 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1912, d3010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16502 p hg
    simpa only [d1912, d3010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1912, d3010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16506 p hg
    simpa only [d1912, d3010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16508 (p : Pattern) (guard : d4474 p = 1) : d278 p ≤ (0 : Int) + d3011 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d278, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16392 p hg
    simpa only [d278, d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d278, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d278, d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16509 (p : Pattern) (guard : d4474 p = 1) : d1913 p ≤ (0 : Int) + d3012 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1913, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16506 p hg
    simpa only [d1913, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1913, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16508 p hg
    simpa only [d1913, d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16510 (p : Pattern) (guard : d4474 p = 1) : d1914 p ≤ (0 : Int) + d3013 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1914, d3013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16507 p hg
    simpa only [d1914, d3013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1914, d3013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d1914, d3013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16511 (p : Pattern) (guard : d4474 p = 1) : d1915 p ≤ (0 : Int) + d3014 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1915, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d1915, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1915, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16510 p hg
    simpa only [d1915, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16512 (p : Pattern) (guard : d0 p = 1) : d333 p ≤ (0 : Int) + d1942 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16513 (p : Pattern) (guard : d4474 p = 1) : d1916 p ≤ (0 : Int) + d2993 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1916, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d1916, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1916, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16512 p hg
    simpa only [d4474, d1916, d2993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16514 (p : Pattern) (guard : d4474 p = 1) : d1917 p ≤ (0 : Int) + d2994 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1917, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d1917, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1917, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16484 p hg
    simpa only [d1917, d2994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16515 (p : Pattern) (guard : d4474 p = 1) : d117 p ≤ (0 : Int) + d3015 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d117, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4474, d117, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d117, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13052 p hg
    simpa only [d4474, d117, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16516 (p : Pattern) (guard : d4474 p = 1) : d1922 p ≤ (0 : Int) + d1922 p := by
  omega
theorem compare16517 (p : Pattern) (guard : d4474 p = 1) : d1923 p ≤ (0 : Int) + d3016 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1923, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16515 p hg
    simpa only [d1923, d3016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1923, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16516 p hg
    simpa only [d1923, d3016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16518 (p : Pattern) (guard : d4474 p = 1) : d1924 p ≤ (0 : Int) + d3017 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1924, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16514 p hg
    simpa only [d1924, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1924, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16517 p hg
    simpa only [d1924, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16519 (p : Pattern) (guard : d4474 p = 1) : d1925 p ≤ (0 : Int) + d3018 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1925, d3018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16491 p hg
    simpa only [d1925, d3018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1925, d3018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16380 p hg
    simpa only [d1925, d3018, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
