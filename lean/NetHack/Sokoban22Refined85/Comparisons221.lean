/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons220
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30940 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (9 : Int) + d2 p := by
  change (11 : Int) ≤ (9 : Int) + 2
  decide
theorem compare30941 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (9 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30940 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30942 (p : Pattern) (guard : d6326 p = 1) : d1715 p ≤ (9 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d6326, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30941 p hg
    simpa only [d6326, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30943 (p : Pattern) (guard : d6326 p = 1) : d3586 p ≤ (9 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30939 p hg
    simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30942 p hg
    simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30944 (p : Pattern) (guard : d6326 p = 1) : d3587 p ≤ (9 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30943 p hg
    simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30945 (p : Pattern) (guard : d6326 p = 1) : d3588 p ≤ (9 : Int) + d6338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3588, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30944 p hg
    simpa only [d3588, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3588, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3588, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30946 (p : Pattern) (guard : d6326 p = 1) : d3589 p ≤ (9 : Int) + d6339 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3589, d6339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30927 p hg
    simpa only [d3589, d6339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3589, d6339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30945 p hg
    simpa only [d3589, d6339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30947 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (9 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30948 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (9 : Int) + d6 p := by
  omega
theorem compare30949 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30950 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (9 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30948 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30949 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30951 (p : Pattern) (guard : d6326 p = 1) : d34 p ≤ (9 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30947 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30950 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30952 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (9 : Int) + d6 p := by
  change (12 : Int) ≤ (9 : Int) + 6
  decide
theorem compare30953 (p : Pattern) (guard : d6326 p = 1) : d364 p ≤ (9 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30947 p hg
    simpa only [d6326, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30952 p hg
    simpa only [d6326, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30954 (p : Pattern) (guard : d6326 p = 1) : d3590 p ≤ (9 : Int) + d6 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30951 p hg
    simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30953 p hg
    simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30955 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (9 : Int) + d6 p := by
  change (10 : Int) ≤ (9 : Int) + 6
  decide
theorem compare30956 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (9 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30955 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30949 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30957 (p : Pattern) (guard : d6326 p = 1) : d3591 p ≤ (9 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30947 p hg
    simpa only [d6326, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30956 p hg
    simpa only [d6326, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30958 (p : Pattern) (guard : d6326 p = 1) : d3592 p ≤ (9 : Int) + d6 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30957 p hg
    simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30953 p hg
    simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30959 (p : Pattern) (guard : d6326 p = 1) : d3593 p ≤ (9 : Int) + d6 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30954 p hg
    simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30958 p hg
    simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30960 (p : Pattern) (guard : d6326 p = 1) : d3594 p ≤ (9 : Int) + d6340 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3594, d6340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30959 p hg
    simpa only [d3594, d6340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3594, d6340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3594, d6340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30961 (p : Pattern) (guard : d6326 p = 1) : d3595 p ≤ (9 : Int) + d6341 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3595, d6341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30927 p hg
    simpa only [d3595, d6341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3595, d6341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30960 p hg
    simpa only [d3595, d6341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30962 (p : Pattern) (guard : d6326 p = 1) : d3596 p ≤ (9 : Int) + d6342 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3596, d6342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30946 p hg
    simpa only [d3596, d6342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3596, d6342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30961 p hg
    simpa only [d3596, d6342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30963 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (9 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30964 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (9 : Int) + d11 p := by
  omega
theorem compare30965 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30966 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (9 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30964 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30965 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30967 (p : Pattern) (guard : d6326 p = 1) : d39 p ≤ (9 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30963 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30966 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30968 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (9 : Int) + d11 p := by
  change (12 : Int) ≤ (9 : Int) + 11
  decide
theorem compare30969 (p : Pattern) (guard : d6326 p = 1) : d327 p ≤ (9 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30963 p hg
    simpa only [d6326, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30968 p hg
    simpa only [d6326, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30970 (p : Pattern) (guard : d6326 p = 1) : d3597 p ≤ (9 : Int) + d11 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30967 p hg
    simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30969 p hg
    simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30971 (p : Pattern) (guard : d6326 p = 1) : d3598 p ≤ (9 : Int) + d11 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30970 p hg
    simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30969 p hg
    simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30972 (p : Pattern) (guard : d6326 p = 1) : d3599 p ≤ (9 : Int) + d6343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3599, d6343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30971 p hg
    simpa only [d3599, d6343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3599, d6343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3599, d6343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30973 (p : Pattern) (guard : d6326 p = 1) : d3600 p ≤ (9 : Int) + d6344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3600, d6344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30927 p hg
    simpa only [d3600, d6344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3600, d6344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30972 p hg
    simpa only [d3600, d6344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30974 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (9 : Int) + d4 p := by
  change (10 : Int) ≤ (9 : Int) + 4
  decide
theorem compare30975 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (9 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30974 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30880 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30976 (p : Pattern) (guard : d6326 p = 1) : d3601 p ≤ (9 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30878 p hg
    simpa only [d6326, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30975 p hg
    simpa only [d6326, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30977 (p : Pattern) (guard : d6326 p = 1) : d3602 p ≤ (9 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30882 p hg
    simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30976 p hg
    simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30978 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (9 : Int) + d4 p := by
  change (12 : Int) ≤ (9 : Int) + 4
  decide
theorem compare30979 (p : Pattern) (guard : d6326 p = 1) : d339 p ≤ (9 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30878 p hg
    simpa only [d6326, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30978 p hg
    simpa only [d6326, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30980 (p : Pattern) (guard : d6326 p = 1) : d3603 p ≤ (9 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30885 p hg
    simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30979 p hg
    simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30981 (p : Pattern) (guard : d6326 p = 1) : d3604 p ≤ (9 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30977 p hg
    simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30980 p hg
    simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30982 (p : Pattern) (guard : d6326 p = 1) : d3605 p ≤ (9 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30882 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30981 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30983 (p : Pattern) (guard : d6326 p = 1) : d3606 p ≤ (9 : Int) + d6345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3606, d6345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30982 p hg
    simpa only [d3606, d6345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3606, d6345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3606, d6345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30984 (p : Pattern) (guard : d6326 p = 1) : d3607 p ≤ (9 : Int) + d6346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3607, d6346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30973 p hg
    simpa only [d3607, d6346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3607, d6346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30983 p hg
    simpa only [d3607, d6346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30985 (p : Pattern) (guard : d6326 p = 1) : d3608 p ≤ (9 : Int) + d6347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3608, d6347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30962 p hg
    simpa only [d3608, d6347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3608, d6347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30984 p hg
    simpa only [d3608, d6347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30986 (p : Pattern) (guard : d6326 p = 1) : d3609 p ≤ (9 : Int) + d6348 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3609, d6348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30927 p hg
    simpa only [d3609, d6348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3609, d6348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3609, d6348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30987 (p : Pattern) (guard : d6326 p = 1) : d3610 p ≤ (9 : Int) + d6349 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3610, d6349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30986 p hg
    simpa only [d3610, d6349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3610, d6349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30983 p hg
    simpa only [d3610, d6349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30988 (p : Pattern) (guard : d6326 p = 1) : d3611 p ≤ (9 : Int) + d6350 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3611, d6350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30907 p hg
    simpa only [d3611, d6350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3611, d6350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3611, d6350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30989 (p : Pattern) (guard : d6326 p = 1) : d3612 p ≤ (9 : Int) + d6351 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3612, d6351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30988 p hg
    simpa only [d3612, d6351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3612, d6351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3612, d6351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30990 (p : Pattern) (guard : d6326 p = 1) : d3613 p ≤ (9 : Int) + d6352 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3613, d6352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30987 p hg
    simpa only [d3613, d6352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3613, d6352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30989 p hg
    simpa only [d3613, d6352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30991 (p : Pattern) (guard : d6326 p = 1) : d3614 p ≤ (9 : Int) + d6353 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3614, d6353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30985 p hg
    simpa only [d3614, d6353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3614, d6353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30990 p hg
    simpa only [d3614, d6353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30992 (p : Pattern) (guard : d6326 p = 1) : d3615 p ≤ (9 : Int) + d6354 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3615, d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30917 p hg
    simpa only [d3615, d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3615, d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30991 p hg
    simpa only [d3615, d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30993 (p : Pattern) (guard : d0 p = 1) : d1785 p ≤ (9 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30994 (p : Pattern) (guard : d6326 p = 1) : d3616 p ≤ (9 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30993 p hg
    simpa only [d6326, d3616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30855 p hg
    simpa only [d6326, d3616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30995 (p : Pattern) (guard : d6326 p = 1) : d3617 p ≤ (9 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30994 p hg
    simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30996 (p : Pattern) (guard : d6326 p = 1) : d3618 p ≤ (9 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30995 p hg
    simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30997 (p : Pattern) (guard : d6326 p = 1) : d3619 p ≤ (9 : Int) + d0 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30996 p hg
    simpa only [d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30865 p hg
    simpa only [d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30998 (p : Pattern) (guard : d6326 p = 1) : d3620 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3620, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30997 p hg
    simpa only [d3620, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3620, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30873 p hg
    simpa only [d3620, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30999 (p : Pattern) (guard : d6326 p = 1) : d3621 p ≤ (9 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30932 p hg
    simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30939 p hg
    simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31000 (p : Pattern) (guard : d6326 p = 1) : d3622 p ≤ (9 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30999 p hg
    simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30939 p hg
    simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31001 (p : Pattern) (guard : d6326 p = 1) : d3623 p ≤ (9 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30932 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31000 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31002 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (9 : Int) + d2 p := by
  change (4 : Int) ≤ (9 : Int) + 2
  decide
theorem compare31003 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (9 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31002 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31004 (p : Pattern) (guard : d6326 p = 1) : d3624 p ≤ (9 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d6326, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31003 p hg
    simpa only [d6326, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31005 (p : Pattern) (guard : d6326 p = 1) : d3625 p ≤ (9 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30932 p hg
    simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31004 p hg
    simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31006 (p : Pattern) (guard : d6326 p = 1) : d3626 p ≤ (9 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31005 p hg
    simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31004 p hg
    simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31007 (p : Pattern) (guard : d6326 p = 1) : d3627 p ≤ (9 : Int) + d6338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3627, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31006 p hg
    simpa only [d3627, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3627, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3627, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31008 (p : Pattern) (guard : d6326 p = 1) : d3628 p ≤ (9 : Int) + d6355 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3628, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31001 p hg
    simpa only [d3628, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3628, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31007 p hg
    simpa only [d3628, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31009 (p : Pattern) (guard : d6326 p = 1) : d3629 p ≤ (9 : Int) + d6356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3629, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30998 p hg
    simpa only [d3629, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3629, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31008 p hg
    simpa only [d3629, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31010 (p : Pattern) (guard : d6326 p = 1) : d3630 p ≤ (9 : Int) + d6357 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3630, d6357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30895 p hg
    simpa only [d3630, d6357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3630, d6357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30914 p hg
    simpa only [d3630, d6357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31011 (p : Pattern) (guard : d6326 p = 1) : d3631 p ≤ (9 : Int) + d6358 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3631, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31009 p hg
    simpa only [d3631, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3631, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31010 p hg
    simpa only [d3631, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31012 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (9 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31013 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (9 : Int) + d10 p := by
  omega
theorem compare31014 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31015 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (9 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31013 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31014 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31016 (p : Pattern) (guard : d6326 p = 1) : d57 p ≤ (9 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31012 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31015 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31017 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (9 : Int) + d10 p := by
  change (12 : Int) ≤ (9 : Int) + 10
  decide
theorem compare31018 (p : Pattern) (guard : d6326 p = 1) : d329 p ≤ (9 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31012 p hg
    simpa only [d6326, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31017 p hg
    simpa only [d6326, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31019 (p : Pattern) (guard : d6326 p = 1) : d3632 p ≤ (9 : Int) + d10 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31016 p hg
    simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31018 p hg
    simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31020 (p : Pattern) (guard : d6326 p = 1) : d3633 p ≤ (9 : Int) + d10 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31019 p hg
    simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31018 p hg
    simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31021 (p : Pattern) (guard : d6326 p = 1) : d3634 p ≤ (9 : Int) + d10 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31016 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31020 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31022 (p : Pattern) (guard : d6326 p = 1) : d3635 p ≤ (9 : Int) + d6359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3635, d6359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31020 p hg
    simpa only [d3635, d6359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3635, d6359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3635, d6359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31023 (p : Pattern) (guard : d6326 p = 1) : d3636 p ≤ (9 : Int) + d6360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3636, d6360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31021 p hg
    simpa only [d3636, d6360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3636, d6360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31022 p hg
    simpa only [d3636, d6360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31024 (p : Pattern) (guard : d6326 p = 1) : d3637 p ≤ (9 : Int) + d6361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3637, d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30895 p hg
    simpa only [d3637, d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3637, d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31023 p hg
    simpa only [d3637, d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31025 (p : Pattern) (guard : d6326 p = 1) : d3638 p ≤ (9 : Int) + d11 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30967 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30971 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31026 (p : Pattern) (guard : d6326 p = 1) : d3639 p ≤ (9 : Int) + d6362 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3639, d6362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31025 p hg
    simpa only [d3639, d6362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3639, d6362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30972 p hg
    simpa only [d3639, d6362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31027 (p : Pattern) (guard : d6326 p = 1) : d3640 p ≤ (9 : Int) + d6363 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3640, d6363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31026 p hg
    simpa only [d3640, d6363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3640, d6363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3640, d6363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31028 (p : Pattern) (guard : d6326 p = 1) : d3641 p ≤ (9 : Int) + d6364 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3641, d6364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31024 p hg
    simpa only [d3641, d6364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3641, d6364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31027 p hg
    simpa only [d3641, d6364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31029 (p : Pattern) (guard : d6326 p = 1) : d3642 p ≤ (9 : Int) + d6365 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3642, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31011 p hg
    simpa only [d3642, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3642, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31028 p hg
    simpa only [d3642, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31030 (p : Pattern) (guard : d6326 p = 1) : d3643 p ≤ (9 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30932 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30944 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31031 (p : Pattern) (guard : d6326 p = 1) : d3644 p ≤ (9 : Int) + d6366 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3644, d6366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31030 p hg
    simpa only [d3644, d6366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3644, d6366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3644, d6366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31032 (p : Pattern) (guard : d6326 p = 1) : d3645 p ≤ (9 : Int) + d6367 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3645, d6367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30961 p hg
    simpa only [d3645, d6367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3645, d6367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31031 p hg
    simpa only [d3645, d6367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31033 (p : Pattern) (guard : d6326 p = 1) : d3646 p ≤ (9 : Int) + d6368 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3646, d6368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30983 p hg
    simpa only [d3646, d6368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3646, d6368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30988 p hg
    simpa only [d3646, d6368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31034 (p : Pattern) (guard : d6326 p = 1) : d3647 p ≤ (9 : Int) + d6369 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3647, d6369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31032 p hg
    simpa only [d3647, d6369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3647, d6369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31033 p hg
    simpa only [d3647, d6369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31035 (p : Pattern) (guard : d6326 p = 1) : d3648 p ≤ (9 : Int) + d6370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3648, d6370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31021 p hg
    simpa only [d3648, d6370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3648, d6370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3648, d6370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31036 (p : Pattern) (guard : d6326 p = 1) : d3649 p ≤ (9 : Int) + d6371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3649, d6371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30983 p hg
    simpa only [d3649, d6371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3649, d6371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31035 p hg
    simpa only [d3649, d6371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31037 (p : Pattern) (guard : d6326 p = 1) : d3650 p ≤ (9 : Int) + d6372 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3650, d6372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31025 p hg
    simpa only [d3650, d6372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3650, d6372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3650, d6372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31038 (p : Pattern) (guard : d6326 p = 1) : d3651 p ≤ (9 : Int) + d6373 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3651, d6373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31037 p hg
    simpa only [d3651, d6373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3651, d6373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3651, d6373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31039 (p : Pattern) (guard : d6326 p = 1) : d3652 p ≤ (9 : Int) + d6374 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3652, d6374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31036 p hg
    simpa only [d3652, d6374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3652, d6374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31038 p hg
    simpa only [d3652, d6374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31040 (p : Pattern) (guard : d6326 p = 1) : d3653 p ≤ (9 : Int) + d6375 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3653, d6375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31034 p hg
    simpa only [d3653, d6375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3653, d6375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31039 p hg
    simpa only [d3653, d6375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31041 (p : Pattern) (guard : d6326 p = 1) : d3654 p ≤ (9 : Int) + d6376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3654, d6376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31029 p hg
    simpa only [d3654, d6376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3654, d6376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31040 p hg
    simpa only [d3654, d6376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31042 (p : Pattern) (guard : d6326 p = 1) : d3655 p ≤ (9 : Int) + d6377 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3655, d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30992 p hg
    simpa only [d3655, d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3655, d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31041 p hg
    simpa only [d3655, d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31043 (p : Pattern) (guard : d6326 p = 1) : d3656 p ≤ (9 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30863 p hg
    simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30920 p hg
    simpa only [d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31044 (p : Pattern) (guard : d6326 p = 1) : d3657 p ≤ (9 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31043 p hg
    simpa only [d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31045 (p : Pattern) (guard : d6326 p = 1) : d3658 p ≤ (9 : Int) + d0 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31044 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31046 (p : Pattern) (guard : d6326 p = 1) : d3659 p ≤ (9 : Int) + d6327 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3659, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30865 p hg
    simpa only [d3659, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3659, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3659, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31047 (p : Pattern) (guard : d6326 p = 1) : d3660 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3660, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31045 p hg
    simpa only [d3660, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3660, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31046 p hg
    simpa only [d3660, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31048 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (9 : Int) + d0 p := by
  change (8 : Int) ≤ (9 : Int) + 0
  decide
theorem compare31049 (p : Pattern) (guard : d5843 p = 1) : d190 p ≤ (9 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31048 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30854 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31050 (p : Pattern) (guard : d6326 p = 1) : d3661 p ≤ (9 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30857 p hg
    simpa only [d6326, d3661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31049 p hg
    simpa only [d6326, d3661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31051 (p : Pattern) (guard : d6326 p = 1) : d3662 p ≤ (9 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30863 p hg
    simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31050 p hg
    simpa only [d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31052 (p : Pattern) (guard : d6326 p = 1) : d3663 p ≤ (9 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31051 p hg
    simpa only [d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31053 (p : Pattern) (guard : d6326 p = 1) : d3664 p ≤ (9 : Int) + d6327 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3664, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31052 p hg
    simpa only [d3664, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3664, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3664, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31054 (p : Pattern) (guard : d6326 p = 1) : d3665 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3665, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30927 p hg
    simpa only [d3665, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3665, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31053 p hg
    simpa only [d3665, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31055 (p : Pattern) (guard : d6326 p = 1) : d3666 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31047 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31054 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31056 (p : Pattern) (guard : d6326 p = 1) : d3667 p ≤ (9 : Int) + d6327 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3667, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30926 p hg
    simpa only [d3667, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3667, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3667, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31057 (p : Pattern) (guard : d6326 p = 1) : d3668 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3668, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30927 p hg
    simpa only [d3668, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3668, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31056 p hg
    simpa only [d3668, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31058 (p : Pattern) (guard : d6326 p = 1) : d3669 p ≤ (9 : Int) + d6329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3669, d6329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30981 p hg
    simpa only [d3669, d6329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3669, d6329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3669, d6329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31059 (p : Pattern) (guard : d6326 p = 1) : d3670 p ≤ (9 : Int) + d6330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3670, d6330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30982 p hg
    simpa only [d3670, d6330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3670, d6330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31058 p hg
    simpa only [d3670, d6330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31060 (p : Pattern) (guard : d6326 p = 1) : d3671 p ≤ (9 : Int) + d6331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3671, d6331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31057 p hg
    simpa only [d3671, d6331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3671, d6331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31059 p hg
    simpa only [d3671, d6331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31061 (p : Pattern) (guard : d6326 p = 1) : d3672 p ≤ (9 : Int) + d6332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3672, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31055 p hg
    simpa only [d3672, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3672, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31060 p hg
    simpa only [d3672, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31062 (p : Pattern) (guard : d6326 p = 1) : d3673 p ≤ (9 : Int) + d6333 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3673, d6333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30906 p hg
    simpa only [d3673, d6333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3673, d6333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3673, d6333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31063 (p : Pattern) (guard : d6326 p = 1) : d3674 p ≤ (9 : Int) + d6334 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3674, d6334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30907 p hg
    simpa only [d3674, d6334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3674, d6334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31062 p hg
    simpa only [d3674, d6334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31064 (p : Pattern) (guard : d6326 p = 1) : d3675 p ≤ (9 : Int) + d6335 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3675, d6335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31063 p hg
    simpa only [d3675, d6335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3675, d6335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3675, d6335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31065 (p : Pattern) (guard : d6326 p = 1) : d3676 p ≤ (9 : Int) + d6336 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3676, d6336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31060 p hg
    simpa only [d3676, d6336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3676, d6336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31064 p hg
    simpa only [d3676, d6336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31066 (p : Pattern) (guard : d6326 p = 1) : d3677 p ≤ (9 : Int) + d6337 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3677, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31061 p hg
    simpa only [d3677, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3677, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31065 p hg
    simpa only [d3677, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31067 (p : Pattern) (guard : d6326 p = 1) : d3678 p ≤ (9 : Int) + d6355 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3678, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31030 p hg
    simpa only [d3678, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3678, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30945 p hg
    simpa only [d3678, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31068 (p : Pattern) (guard : d6326 p = 1) : d3679 p ≤ (9 : Int) + d6 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30951 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30959 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31069 (p : Pattern) (guard : d6326 p = 1) : d3680 p ≤ (9 : Int) + d6378 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3680, d6378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31068 p hg
    simpa only [d3680, d6378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3680, d6378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30960 p hg
    simpa only [d3680, d6378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31070 (p : Pattern) (guard : d6326 p = 1) : d3681 p ≤ (9 : Int) + d6379 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3681, d6379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31067 p hg
    simpa only [d3681, d6379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3681, d6379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31069 p hg
    simpa only [d3681, d6379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31071 (p : Pattern) (guard : d6326 p = 1) : d3682 p ≤ (9 : Int) + d6380 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3682, d6380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31070 p hg
    simpa only [d3682, d6380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3682, d6380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31027 p hg
    simpa only [d3682, d6380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31072 (p : Pattern) (guard : d6326 p = 1) : d3683 p ≤ (9 : Int) + d6381 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3683, d6381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31071 p hg
    simpa only [d3683, d6381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3683, d6381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3683, d6381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31073 (p : Pattern) (guard : d6326 p = 1) : d3684 p ≤ (9 : Int) + d6382 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3684, d6382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31066 p hg
    simpa only [d3684, d6382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3684, d6382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31072 p hg
    simpa only [d3684, d6382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31074 (p : Pattern) (guard : d6326 p = 1) : d3685 p ≤ (9 : Int) + d6356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3685, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31054 p hg
    simpa only [d3685, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3685, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31067 p hg
    simpa only [d3685, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31075 (p : Pattern) (guard : d6326 p = 1) : d3686 p ≤ (9 : Int) + d6357 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3686, d6357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31059 p hg
    simpa only [d3686, d6357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3686, d6357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31063 p hg
    simpa only [d3686, d6357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31076 (p : Pattern) (guard : d6326 p = 1) : d3687 p ≤ (9 : Int) + d6358 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3687, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31074 p hg
    simpa only [d3687, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3687, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31075 p hg
    simpa only [d3687, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31077 (p : Pattern) (guard : d6326 p = 1) : d3688 p ≤ (9 : Int) + d6361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3688, d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31059 p hg
    simpa only [d3688, d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3688, d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31023 p hg
    simpa only [d3688, d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31078 (p : Pattern) (guard : d6326 p = 1) : d3689 p ≤ (9 : Int) + d6364 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3689, d6364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31077 p hg
    simpa only [d3689, d6364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3689, d6364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31027 p hg
    simpa only [d3689, d6364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31079 (p : Pattern) (guard : d6326 p = 1) : d3690 p ≤ (9 : Int) + d6365 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3690, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31076 p hg
    simpa only [d3690, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3690, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31078 p hg
    simpa only [d3690, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
