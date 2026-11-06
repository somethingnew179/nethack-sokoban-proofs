/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons170
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23940 (p : Pattern) (guard : d4474 p = 1) : d2946 p ≤ (0 : Int) + d1767 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2946, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23927 p hg
    simpa only [d2946, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2946, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23939 p hg
    simpa only [d2946, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23941 (p : Pattern) (guard : d4474 p = 1) : d2947 p ≤ (0 : Int) + d1768 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2947, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23908 p hg
    simpa only [d2947, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2947, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23940 p hg
    simpa only [d2947, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23942 (p : Pattern) (guard : d0 p = 1) : d2048 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23943 (p : Pattern) (guard : d4474 p = 1) : d2948 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2948, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d2948, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2948, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23942 p hg
    simpa only [d4474, d2948, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23944 (p : Pattern) (guard : d4474 p = 1) : d2949 p ≤ (0 : Int) + d1774 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2949, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23943 p hg
    simpa only [d2949, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2949, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16401 p hg
    simpa only [d2949, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23945 (p : Pattern) (guard : d0 p = 1) : d2054 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23946 (p : Pattern) (guard : d4474 p = 1) : d2950 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2950, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d2950, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2950, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23945 p hg
    simpa only [d4474, d2950, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23947 (p : Pattern) (guard : d4474 p = 1) : d2951 p ≤ (0 : Int) + d1783 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2951, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23946 p hg
    simpa only [d2951, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2951, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16404 p hg
    simpa only [d2951, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23948 (p : Pattern) (guard : d4474 p = 1) : d2952 p ≤ (0 : Int) + d1784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2952, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23944 p hg
    simpa only [d2952, d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2952, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23947 p hg
    simpa only [d2952, d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23949 (p : Pattern) (guard : d4474 p = 1) : d2953 p ≤ (0 : Int) + d1790 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2953, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23892 p hg
    simpa only [d2953, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2953, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16407 p hg
    simpa only [d2953, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23950 (p : Pattern) (guard : d4474 p = 1) : d2954 p ≤ (0 : Int) + d1799 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2954, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23898 p hg
    simpa only [d2954, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2954, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16409 p hg
    simpa only [d2954, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23951 (p : Pattern) (guard : d4474 p = 1) : d2955 p ≤ (0 : Int) + d1800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2955, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23949 p hg
    simpa only [d2955, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2955, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23950 p hg
    simpa only [d2955, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23952 (p : Pattern) (guard : d4474 p = 1) : d2956 p ≤ (0 : Int) + d1801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2956, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23948 p hg
    simpa only [d2956, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2956, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23951 p hg
    simpa only [d2956, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23953 (p : Pattern) (guard : d4474 p = 1) : d2957 p ≤ (0 : Int) + d1805 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2957, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23886 p hg
    simpa only [d2957, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2957, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16413 p hg
    simpa only [d2957, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23954 (p : Pattern) (guard : d4474 p = 1) : d2958 p ≤ (0 : Int) + d1806 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2958, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23953 p hg
    simpa only [d2958, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2958, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2958, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23955 (p : Pattern) (guard : d4474 p = 1) : d2959 p ≤ (0 : Int) + d1807 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2959, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23951 p hg
    simpa only [d2959, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2959, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23954 p hg
    simpa only [d2959, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23956 (p : Pattern) (guard : d4474 p = 1) : d2960 p ≤ (0 : Int) + d1808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2960, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23952 p hg
    simpa only [d2960, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2960, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23955 p hg
    simpa only [d2960, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23957 (p : Pattern) (guard : d4474 p = 1) : d2961 p ≤ (0 : Int) + d1809 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2961, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23929 p hg
    simpa only [d2961, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2961, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16351 p hg
    simpa only [d2961, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23958 (p : Pattern) (guard : d0 p = 1) : d1724 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23959 (p : Pattern) (guard : d4474 p = 1) : d2962 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2962, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d4474, d2962, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2962, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23958 p hg
    simpa only [d4474, d2962, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23960 (p : Pattern) (guard : d4474 p = 1) : d2963 p ≤ (0 : Int) + d1810 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2963, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23959 p hg
    simpa only [d2963, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2963, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16353 p hg
    simpa only [d2963, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23961 (p : Pattern) (guard : d4474 p = 1) : d2964 p ≤ (0 : Int) + d1811 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2964, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23957 p hg
    simpa only [d2964, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2964, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23960 p hg
    simpa only [d2964, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23962 (p : Pattern) (guard : d4474 p = 1) : d2965 p ≤ (0 : Int) + d1812 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2965, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23961 p hg
    simpa only [d2965, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2965, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23925 p hg
    simpa only [d2965, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23963 (p : Pattern) (guard : d4474 p = 1) : d2966 p ≤ (0 : Int) + d1813 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2966, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23962 p hg
    simpa only [d2966, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2966, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2966, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23964 (p : Pattern) (guard : d4474 p = 1) : d2967 p ≤ (0 : Int) + d1814 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2967, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23956 p hg
    simpa only [d2967, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2967, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23963 p hg
    simpa only [d2967, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23965 (p : Pattern) (guard : d4474 p = 1) : d2968 p ≤ (0 : Int) + d1815 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2968, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23947 p hg
    simpa only [d2968, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2968, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23957 p hg
    simpa only [d2968, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23966 (p : Pattern) (guard : d4474 p = 1) : d2969 p ≤ (0 : Int) + d1816 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2969, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23950 p hg
    simpa only [d2969, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2969, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23953 p hg
    simpa only [d2969, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23967 (p : Pattern) (guard : d4474 p = 1) : d2970 p ≤ (0 : Int) + d1817 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2970, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23965 p hg
    simpa only [d2970, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2970, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23966 p hg
    simpa only [d2970, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23968 (p : Pattern) (guard : d4474 p = 1) : d2971 p ≤ (0 : Int) + d1818 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2971, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23950 p hg
    simpa only [d2971, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2971, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23920 p hg
    simpa only [d2971, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23969 (p : Pattern) (guard : d4474 p = 1) : d2972 p ≤ (0 : Int) + d1819 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2972, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23968 p hg
    simpa only [d2972, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2972, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23925 p hg
    simpa only [d2972, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23970 (p : Pattern) (guard : d4474 p = 1) : d2973 p ≤ (0 : Int) + d1820 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2973, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23967 p hg
    simpa only [d2973, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2973, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23969 p hg
    simpa only [d2973, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23971 (p : Pattern) (guard : d4474 p = 1) : d2974 p ≤ (0 : Int) + d1821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2974, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23960 p hg
    simpa only [d2974, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2974, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2974, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23972 (p : Pattern) (guard : d4474 p = 1) : d2975 p ≤ (0 : Int) + d1822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2975, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23971 p hg
    simpa only [d2975, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2975, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2975, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23973 (p : Pattern) (guard : d4474 p = 1) : d2976 p ≤ (0 : Int) + d1823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2976, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23972 p hg
    simpa only [d2976, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2976, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2976, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23974 (p : Pattern) (guard : d4474 p = 1) : d2977 p ≤ (0 : Int) + d1824 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2977, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23970 p hg
    simpa only [d2977, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2977, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23973 p hg
    simpa only [d2977, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23975 (p : Pattern) (guard : d4474 p = 1) : d2978 p ≤ (0 : Int) + d1825 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2978, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23964 p hg
    simpa only [d2978, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2978, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23974 p hg
    simpa only [d2978, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23976 (p : Pattern) (guard : d4474 p = 1) : d2979 p ≤ (0 : Int) + d1826 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2979, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23941 p hg
    simpa only [d2979, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2979, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23975 p hg
    simpa only [d2979, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23977 (p : Pattern) (guard : d4474 p = 1) : d2980 p ≤ (0 : Int) + d1827 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2980, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23953 p hg
    simpa only [d2980, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2980, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23924 p hg
    simpa only [d2980, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23978 (p : Pattern) (guard : d4474 p = 1) : d2981 p ≤ (0 : Int) + d1828 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2981, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23977 p hg
    simpa only [d2981, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2981, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23925 p hg
    simpa only [d2981, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23979 (p : Pattern) (guard : d4474 p = 1) : d2982 p ≤ (0 : Int) + d1829 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2982, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23925 p hg
    simpa only [d2982, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2982, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2982, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23980 (p : Pattern) (guard : d4474 p = 1) : d2983 p ≤ (0 : Int) + d1830 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2983, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23978 p hg
    simpa only [d2983, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2983, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23979 p hg
    simpa only [d2983, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23981 (p : Pattern) (guard : d4474 p = 1) : d2984 p ≤ (0 : Int) + d1831 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2984, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23979 p hg
    simpa only [d2984, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2984, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2984, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23982 (p : Pattern) (guard : d4474 p = 1) : d2985 p ≤ (0 : Int) + d1832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2985, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23980 p hg
    simpa only [d2985, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2985, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23981 p hg
    simpa only [d2985, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23983 (p : Pattern) (guard : d4474 p = 1) : d2986 p ≤ (0 : Int) + d1833 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2986, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23981 p hg
    simpa only [d2986, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2986, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2986, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23984 (p : Pattern) (guard : d4474 p = 1) : d2987 p ≤ (0 : Int) + d1834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2987, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23982 p hg
    simpa only [d2987, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2987, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23983 p hg
    simpa only [d2987, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23985 (p : Pattern) (guard : d4474 p = 1) : d2988 p ≤ (0 : Int) + d1835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2988, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23975 p hg
    simpa only [d2988, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2988, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23984 p hg
    simpa only [d2988, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23986 (p : Pattern) (guard : d4474 p = 1) : d2989 p ≤ (0 : Int) + d1836 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2989, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23976 p hg
    simpa only [d2989, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2989, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23985 p hg
    simpa only [d2989, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23987 (p : Pattern) (guard : d4474 p = 1) : d2896 p ≤ (0 : Int) + d1837 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23875 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23879 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23988 (p : Pattern) (guard : d4474 p = 1) : d2900 p ≤ (0 : Int) + d1838 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2900, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23987 p hg
    simpa only [d2900, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2900, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23883 p hg
    simpa only [d2900, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23989 (p : Pattern) (guard : d4474 p = 1) : d2905 p ≤ (0 : Int) + d1839 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2905, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23988 p hg
    simpa only [d2905, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2905, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23889 p hg
    simpa only [d2905, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23990 (p : Pattern) (guard : d4474 p = 1) : d2921 p ≤ (0 : Int) + d1840 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2921, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23989 p hg
    simpa only [d2921, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2921, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23907 p hg
    simpa only [d2921, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23991 (p : Pattern) (guard : d4474 p = 1) : d2924 p ≤ (0 : Int) + d1841 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2924, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23879 p hg
    simpa only [d2924, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2924, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23914 p hg
    simpa only [d2924, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23992 (p : Pattern) (guard : d4474 p = 1) : d2926 p ≤ (0 : Int) + d1842 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2926, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23991 p hg
    simpa only [d2926, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2926, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23916 p hg
    simpa only [d2926, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23993 (p : Pattern) (guard : d4474 p = 1) : d2934 p ≤ (0 : Int) + d1843 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2934, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23992 p hg
    simpa only [d2934, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2934, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23926 p hg
    simpa only [d2934, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23994 (p : Pattern) (guard : d4474 p = 1) : d2946 p ≤ (0 : Int) + d1844 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2946, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23993 p hg
    simpa only [d2946, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2946, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23939 p hg
    simpa only [d2946, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23995 (p : Pattern) (guard : d4474 p = 1) : d2947 p ≤ (0 : Int) + d1845 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2947, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23990 p hg
    simpa only [d2947, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2947, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23994 p hg
    simpa only [d2947, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23996 (p : Pattern) (guard : d4474 p = 1) : d2979 p ≤ (0 : Int) + d1846 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2979, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23995 p hg
    simpa only [d2979, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2979, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23975 p hg
    simpa only [d2979, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23997 (p : Pattern) (guard : d4474 p = 1) : d2990 p ≤ (0 : Int) + d1847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2990, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23975 p hg
    simpa only [d2990, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2990, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2990, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23998 (p : Pattern) (guard : d4474 p = 1) : d2991 p ≤ (0 : Int) + d1848 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2991, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23996 p hg
    simpa only [d2991, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2991, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23997 p hg
    simpa only [d2991, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23999 (p : Pattern) (guard : d4474 p = 1) : d2992 p ≤ (0 : Int) + d1849 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2992, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23986 p hg
    simpa only [d2992, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2992, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23998 p hg
    simpa only [d2992, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24000 (p : Pattern) (guard : d0 p = 1) : d1772 p ≤ (0 : Int) + d358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24001 (p : Pattern) (guard : d4474 p = 1) : d2895 p ≤ (0 : Int) + d1850 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2895, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d2895, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2895, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24000 p hg
    simpa only [d4474, d2895, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24002 (p : Pattern) (guard : d4474 p = 1) : d2896 p ≤ (0 : Int) + d1851 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24001 p hg
    simpa only [d2896, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d2896, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24003 (p : Pattern) (guard : d4474 p = 1) : d2896 p ≤ (0 : Int) + d1852 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24002 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23879 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24004 (p : Pattern) (guard : d4474 p = 1) : d2900 p ≤ (0 : Int) + d1853 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2900, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24003 p hg
    simpa only [d2900, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2900, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23883 p hg
    simpa only [d2900, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24005 (p : Pattern) (guard : d4474 p = 1) : d2905 p ≤ (0 : Int) + d1854 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2905, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24004 p hg
    simpa only [d2905, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2905, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23889 p hg
    simpa only [d2905, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24006 (p : Pattern) (guard : d4474 p = 1) : d2921 p ≤ (0 : Int) + d1855 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2921, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24005 p hg
    simpa only [d2921, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2921, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23907 p hg
    simpa only [d2921, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24007 (p : Pattern) (guard : d4474 p = 1) : d2924 p ≤ (0 : Int) + d1856 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2924, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23875 p hg
    simpa only [d2924, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2924, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23914 p hg
    simpa only [d2924, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24008 (p : Pattern) (guard : d4474 p = 1) : d2926 p ≤ (0 : Int) + d1857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2926, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24007 p hg
    simpa only [d2926, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2926, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23916 p hg
    simpa only [d2926, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24009 (p : Pattern) (guard : d4474 p = 1) : d2934 p ≤ (0 : Int) + d1858 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2934, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24008 p hg
    simpa only [d2934, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2934, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23926 p hg
    simpa only [d2934, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24010 (p : Pattern) (guard : d4474 p = 1) : d2946 p ≤ (0 : Int) + d1859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2946, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24009 p hg
    simpa only [d2946, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2946, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23939 p hg
    simpa only [d2946, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24011 (p : Pattern) (guard : d4474 p = 1) : d2947 p ≤ (0 : Int) + d1860 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2947, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24006 p hg
    simpa only [d2947, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2947, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24010 p hg
    simpa only [d2947, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24012 (p : Pattern) (guard : d4474 p = 1) : d2979 p ≤ (0 : Int) + d1861 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2979, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24011 p hg
    simpa only [d2979, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2979, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23975 p hg
    simpa only [d2979, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24013 (p : Pattern) (guard : d4474 p = 1) : d2989 p ≤ (0 : Int) + d1862 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2989, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24012 p hg
    simpa only [d2989, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2989, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23985 p hg
    simpa only [d2989, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24014 (p : Pattern) (guard : d4474 p = 1) : d2900 p ≤ (0 : Int) + d1863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2900, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23879 p hg
    simpa only [d2900, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2900, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23883 p hg
    simpa only [d2900, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24015 (p : Pattern) (guard : d4474 p = 1) : d2905 p ≤ (0 : Int) + d1864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2905, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24014 p hg
    simpa only [d2905, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2905, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23889 p hg
    simpa only [d2905, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24016 (p : Pattern) (guard : d4474 p = 1) : d2921 p ≤ (0 : Int) + d1865 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2921, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24015 p hg
    simpa only [d2921, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2921, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23907 p hg
    simpa only [d2921, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24017 (p : Pattern) (guard : d4474 p = 1) : d2947 p ≤ (0 : Int) + d1866 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2947, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24016 p hg
    simpa only [d2947, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2947, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23994 p hg
    simpa only [d2947, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24018 (p : Pattern) (guard : d4474 p = 1) : d2979 p ≤ (0 : Int) + d1867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2979, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24017 p hg
    simpa only [d2979, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2979, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23975 p hg
    simpa only [d2979, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24019 (p : Pattern) (guard : d4474 p = 1) : d2991 p ≤ (0 : Int) + d1868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2991, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24018 p hg
    simpa only [d2991, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2991, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23997 p hg
    simpa only [d2991, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24020 (p : Pattern) (guard : d4474 p = 1) : d2992 p ≤ (0 : Int) + d1869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2992, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24013 p hg
    simpa only [d2992, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2992, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24019 p hg
    simpa only [d2992, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24021 (p : Pattern) (guard : d4474 p = 1) : d2992 p ≤ (0 : Int) + d1870 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23999 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24020 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24022 (p : Pattern) (guard : d0 p = 1) : d1942 p ≤ (0 : Int) + d358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24023 (p : Pattern) (guard : d4474 p = 1) : d2993 p ≤ (0 : Int) + d1871 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2993, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d2993, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2993, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24022 p hg
    simpa only [d4474, d2993, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24024 (p : Pattern) (guard : d4474 p = 1) : d2994 p ≤ (0 : Int) + d1877 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2994, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24023 p hg
    simpa only [d2994, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2994, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16484 p hg
    simpa only [d2994, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24025 (p : Pattern) (guard : d0 p = 1) : d1942 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24026 (p : Pattern) (guard : d4474 p = 1) : d2993 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2993, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d2993, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2993, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24025 p hg
    simpa only [d4474, d2993, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24027 (p : Pattern) (guard : d4474 p = 1) : d2994 p ≤ (0 : Int) + d1878 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2994, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24026 p hg
    simpa only [d2994, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2994, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16484 p hg
    simpa only [d2994, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24028 (p : Pattern) (guard : d4474 p = 1) : d2994 p ≤ (0 : Int) + d1879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24024 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24027 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24029 (p : Pattern) (guard : d0 p = 1) : d2130 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24030 (p : Pattern) (guard : d4474 p = 1) : d2995 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2995, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4474, d2995, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2995, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24029 p hg
    simpa only [d4474, d2995, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24031 (p : Pattern) (guard : d4474 p = 1) : d2996 p ≤ (0 : Int) + d1885 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2996, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24030 p hg
    simpa only [d2996, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2996, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16490 p hg
    simpa only [d2996, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24032 (p : Pattern) (guard : d4474 p = 1) : d2997 p ≤ (0 : Int) + d1886 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2997, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24027 p hg
    simpa only [d2997, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2997, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24031 p hg
    simpa only [d2997, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24033 (p : Pattern) (guard : d4474 p = 1) : d2998 p ≤ (0 : Int) + d1887 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2998, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24028 p hg
    simpa only [d2998, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2998, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24032 p hg
    simpa only [d2998, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24034 (p : Pattern) (guard : d4474 p = 1) : d2999 p ≤ (0 : Int) + d1888 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2999, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23920 p hg
    simpa only [d2999, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2999, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2999, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24035 (p : Pattern) (guard : d4474 p = 1) : d3000 p ≤ (0 : Int) + d1889 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3000, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24032 p hg
    simpa only [d3000, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3000, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24034 p hg
    simpa only [d3000, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24036 (p : Pattern) (guard : d4474 p = 1) : d3001 p ≤ (0 : Int) + d1890 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3001, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24033 p hg
    simpa only [d3001, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3001, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24035 p hg
    simpa only [d3001, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24037 (p : Pattern) (guard : d0 p = 1) : d1957 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24038 (p : Pattern) (guard : d4474 p = 1) : d3002 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3002, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d3002, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3002, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24037 p hg
    simpa only [d4474, d3002, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24039 (p : Pattern) (guard : d4474 p = 1) : d3003 p ≤ (0 : Int) + d1900 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3003, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24038 p hg
    simpa only [d3003, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3003, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d3003, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24040 (p : Pattern) (guard : d4474 p = 1) : d3004 p ≤ (0 : Int) + d1907 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3004, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24038 p hg
    simpa only [d3004, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3004, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16500 p hg
    simpa only [d3004, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24041 (p : Pattern) (guard : d4474 p = 1) : d3005 p ≤ (0 : Int) + d1908 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3005, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24039 p hg
    simpa only [d3005, d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3005, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24040 p hg
    simpa only [d3005, d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24042 (p : Pattern) (guard : d4474 p = 1) : d3006 p ≤ (0 : Int) + d1909 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3006, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24038 p hg
    simpa only [d3006, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3006, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3006, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24043 (p : Pattern) (guard : d0 p = 1) : d1966 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24044 (p : Pattern) (guard : d4474 p = 1) : d3007 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3007, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4474, d3007, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3007, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24043 p hg
    simpa only [d4474, d3007, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24045 (p : Pattern) (guard : d4474 p = 1) : d3008 p ≤ (0 : Int) + d1910 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3008, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24044 p hg
    simpa only [d3008, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3008, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3008, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24046 (p : Pattern) (guard : d4474 p = 1) : d3009 p ≤ (0 : Int) + d1911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3009, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24042 p hg
    simpa only [d3009, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3009, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24045 p hg
    simpa only [d3009, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24047 (p : Pattern) (guard : d4474 p = 1) : d3010 p ≤ (0 : Int) + d1912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3010, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24041 p hg
    simpa only [d3010, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3010, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24046 p hg
    simpa only [d3010, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24048 (p : Pattern) (guard : d4474 p = 1) : d3011 p ≤ (0 : Int) + d278 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3011, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23934 p hg
    simpa only [d3011, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3011, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3011, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24049 (p : Pattern) (guard : d4474 p = 1) : d3012 p ≤ (0 : Int) + d1913 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3012, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24046 p hg
    simpa only [d3012, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3012, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24048 p hg
    simpa only [d3012, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24050 (p : Pattern) (guard : d4474 p = 1) : d3013 p ≤ (0 : Int) + d1914 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3013, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24047 p hg
    simpa only [d3013, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3013, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24049 p hg
    simpa only [d3013, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24051 (p : Pattern) (guard : d4474 p = 1) : d3014 p ≤ (0 : Int) + d1915 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3014, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24036 p hg
    simpa only [d3014, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3014, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24050 p hg
    simpa only [d3014, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24052 (p : Pattern) (guard : d0 p = 1) : d1942 p ≤ (0 : Int) + d333 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24053 (p : Pattern) (guard : d4474 p = 1) : d2993 p ≤ (0 : Int) + d1916 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2993, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d2993, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2993, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24052 p hg
    simpa only [d4474, d2993, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24054 (p : Pattern) (guard : d4474 p = 1) : d2994 p ≤ (0 : Int) + d1917 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2994, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24053 p hg
    simpa only [d2994, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2994, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16484 p hg
    simpa only [d2994, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24055 (p : Pattern) (guard : d0 p = 1) : d2125 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24056 (p : Pattern) (guard : d4474 p = 1) : d3015 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3015, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4474, d3015, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3015, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24055 p hg
    simpa only [d4474, d3015, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24057 (p : Pattern) (guard : d4474 p = 1) : d3016 p ≤ (0 : Int) + d1923 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3016, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24056 p hg
    simpa only [d3016, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3016, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16516 p hg
    simpa only [d3016, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24058 (p : Pattern) (guard : d4474 p = 1) : d3017 p ≤ (0 : Int) + d1924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3017, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24054 p hg
    simpa only [d3017, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3017, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24057 p hg
    simpa only [d3017, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24059 (p : Pattern) (guard : d4474 p = 1) : d3018 p ≤ (0 : Int) + d1925 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3018, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24031 p hg
    simpa only [d3018, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3018, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23920 p hg
    simpa only [d3018, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24060 (p : Pattern) (guard : d4474 p = 1) : d3019 p ≤ (0 : Int) + d1926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3019, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24058 p hg
    simpa only [d3019, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3019, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24059 p hg
    simpa only [d3019, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24061 (p : Pattern) (guard : d4474 p = 1) : d3020 p ≤ (0 : Int) + d1927 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3020, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24031 p hg
    simpa only [d3020, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3020, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23924 p hg
    simpa only [d3020, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24062 (p : Pattern) (guard : d4474 p = 1) : d3021 p ≤ (0 : Int) + d1928 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3021, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24061 p hg
    simpa only [d3021, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3021, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3021, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24063 (p : Pattern) (guard : d4474 p = 1) : d3022 p ≤ (0 : Int) + d1929 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3022, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24060 p hg
    simpa only [d3022, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3022, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24062 p hg
    simpa only [d3022, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24064 (p : Pattern) (guard : d0 p = 1) : d1898 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24065 (p : Pattern) (guard : d4474 p = 1) : d3023 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3023, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4474, d3023, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3023, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24064 p hg
    simpa only [d4474, d3023, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24066 (p : Pattern) (guard : d4474 p = 1) : d3024 p ≤ (0 : Int) + d1930 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3024, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24065 p hg
    simpa only [d3024, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3024, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3024, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24067 (p : Pattern) (guard : d4474 p = 1) : d3025 p ≤ (0 : Int) + d1931 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3025, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24040 p hg
    simpa only [d3025, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3025, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24066 p hg
    simpa only [d3025, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24068 (p : Pattern) (guard : d4474 p = 1) : d3026 p ≤ (0 : Int) + d1932 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3026, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24045 p hg
    simpa only [d3026, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3026, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23934 p hg
    simpa only [d3026, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24069 (p : Pattern) (guard : d4474 p = 1) : d3027 p ≤ (0 : Int) + d1933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3027, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24067 p hg
    simpa only [d3027, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3027, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24068 p hg
    simpa only [d3027, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24070 (p : Pattern) (guard : d4474 p = 1) : d3028 p ≤ (0 : Int) + d1934 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3028, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24045 p hg
    simpa only [d3028, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3028, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23936 p hg
    simpa only [d3028, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24071 (p : Pattern) (guard : d4474 p = 1) : d3029 p ≤ (0 : Int) + d1935 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3029, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24070 p hg
    simpa only [d3029, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3029, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3029, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24072 (p : Pattern) (guard : d4474 p = 1) : d3030 p ≤ (0 : Int) + d1936 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3030, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24069 p hg
    simpa only [d3030, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3030, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24071 p hg
    simpa only [d3030, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24073 (p : Pattern) (guard : d4474 p = 1) : d3031 p ≤ (0 : Int) + d1937 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3031, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24063 p hg
    simpa only [d3031, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3031, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24072 p hg
    simpa only [d3031, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24074 (p : Pattern) (guard : d4474 p = 1) : d3032 p ≤ (0 : Int) + d1938 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3032, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24051 p hg
    simpa only [d3032, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3032, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24073 p hg
    simpa only [d3032, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24075 (p : Pattern) (guard : d0 p = 1) : d2108 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24076 (p : Pattern) (guard : d4474 p = 1) : d3033 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3033, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d3033, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3033, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24075 p hg
    simpa only [d4474, d3033, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24077 (p : Pattern) (guard : d4474 p = 1) : d3034 p ≤ (0 : Int) + d1944 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3034, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24076 p hg
    simpa only [d3034, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3034, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16535 p hg
    simpa only [d3034, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24078 (p : Pattern) (guard : d0 p = 1) : d3038 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24079 (p : Pattern) (guard : d4474 p = 1) : d3039 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3039, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d3039, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3039, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24078 p hg
    simpa only [d4474, d3039, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
