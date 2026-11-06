/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions118
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare0 (p : Pattern) (guard : d1 p = 1) : d267 p ≤ (0 : Int) + d267 p := by
  omega
theorem compare1 (p : Pattern) (guard : d1 p = 1) : d267 p ≤ (1 : Int) + d267 p := by
  omega
theorem compare2 (p : Pattern) (guard : d1 p = 1) : d169 p ≤ (0 : Int) + d169 p := by
  omega
theorem compare3 (p : Pattern) (guard : d0 p = 1) : d266 p ≤ (0 : Int) + d480 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4 (p : Pattern) (guard : d4038 p = 1) : d267 p ≤ (0 : Int) + d481 p := by
  cases selected : p 48 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4038, d267, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2 p hg
    simpa only [d4038, d267, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4038, d267, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3 p hg
    simpa only [d4038, d267, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (0 : Int) + d101 p := by
  omega
theorem compare6 (p : Pattern) (guard : d0 p = 1) : d168 p ≤ (0 : Int) + d447 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7 (p : Pattern) (guard : d4040 p = 1) : d169 p ≤ (0 : Int) + d482 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d169, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4040, d169, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d169, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d4040, d169, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8 (p : Pattern) (guard : d0 p = 1) : d310 p ≤ (0 : Int) + d479 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9 (p : Pattern) (guard : d4040 p = 1) : d311 p ≤ (0 : Int) + d483 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d311, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4040, d311, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d311, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d4040, d311, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10 (p : Pattern) (guard : d4040 p = 1) : d312 p ≤ (0 : Int) + d484 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d312, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7 p hg
    simpa only [d312, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4040 p = 1 := by simpa only [d312, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d312, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11 (p : Pattern) (guard : d0 p = 1) : d101 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12 (p : Pattern) (guard : d0 p = 1) : d167 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13 (p : Pattern) (guard : d4042 p = 1) : d168 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12 p hg
    simpa only [d4042, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14 (p : Pattern) (guard : d4043 p = 1) : d169 p ≤ (0 : Int) + d101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4043, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11 p hg
    simpa only [d4043, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d4043, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13 p hg
    simpa only [d4043, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15 (p : Pattern) (guard : d0 p = 1) : d309 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16 (p : Pattern) (guard : d4042 p = 1) : d310 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15 p hg
    simpa only [d4042, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17 (p : Pattern) (guard : d4043 p = 1) : d311 p ≤ (0 : Int) + d101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4043, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11 p hg
    simpa only [d4043, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d4043, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16 p hg
    simpa only [d4043, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18 (p : Pattern) (guard : d4043 p = 1) : d312 p ≤ (0 : Int) + d101 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4043 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4043 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19 (p : Pattern) (guard : d1 p = 1) : d312 p ≤ (0 : Int) + d312 p := by
  omega
theorem compare20 (p : Pattern) (guard : d1 p = 1) : d312 p ≤ (1 : Int) + d312 p := by
  omega
theorem compare21 (p : Pattern) (guard : d4040 p = 1) : d169 p ≤ (0 : Int) + d169 p := by
  omega
theorem compare22 (p : Pattern) (guard : d0 p = 1) : d311 p ≤ (0 : Int) + d480 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23 (p : Pattern) (guard : d4044 p = 1) : d312 p ≤ (0 : Int) + d481 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d4044, d312, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d4044, d312, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4044, d312, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d4044, d312, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (1 : Int) + d101 p := by
  omega
theorem compare25 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (1 : Int) + d98 p := by
  omega
theorem compare26 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (1 : Int) + d29 p := by
  omega
theorem compare27 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d2 p := by
  change (0 : Int) ≤ (1 : Int) + 2
  decide
theorem compare28 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d12 p := by
  omega
theorem compare29 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (1 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (1 : Int) + d32 p := by
  omega
theorem compare32 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (1 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31 p hg
    simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (1 : Int) + d36 p := by
  omega
theorem compare34 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (1 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d37, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33 p hg
    simpa only [d37, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (1 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32 p hg
    simpa only [d38, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d38, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (1 : Int) + d41 p := by
  omega
theorem compare37 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (1 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d42, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36 p hg
    simpa only [d42, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d6 p := by
  change (4 : Int) ≤ (1 : Int) + 6
  decide
theorem compare39 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (1 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38 p hg
    simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38 p hg
    simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39 p hg
    simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (1 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40 p hg
    simpa only [d43, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d43, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (1 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41 p hg
    simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (1 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35 p hg
    simpa only [d45, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42 p hg
    simpa only [d45, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (1 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d46, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d46, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (1 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44 p hg
    simpa only [d47, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41 p hg
    simpa only [d47, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (1 : Int) + d11 p := by
  change (9 : Int) ≤ (1 : Int) + 11
  decide
theorem compare47 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (1 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (1 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46 p hg
    simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47 p hg
    simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (1 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48 p hg
    simpa only [d48, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d48, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare50 (p : Pattern) (guard : d1 p = 1) : d49 p ≤ (1 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d49, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49 p hg
    simpa only [d49, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d49, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d49, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare51 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (1 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d50, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d50, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare52 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (1 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43 p hg
    simpa only [d51, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare51 p hg
    simpa only [d51, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare53 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (1 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26 p hg
    simpa only [d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare52 p hg
    simpa only [d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare54 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (1 : Int) + d65 p := by
  omega
theorem compare55 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d4 p := by
  change (2 : Int) ≤ (1 : Int) + 4
  decide
theorem compare56 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (1 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare57 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (1 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare56 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare58 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (1 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d66, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d66, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare59 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (1 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d67, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare58 p hg
    simpa only [d67, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare60 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41 p hg
    simpa only [d68, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49 p hg
    simpa only [d68, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare61 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (1 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare59 p hg
    simpa only [d69, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d69, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare62 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (1 : Int) + d12 p := by
  change (10 : Int) ≤ (1 : Int) + 12
  decide
theorem compare63 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare64 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare63 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare65 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare66 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (1 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41 p hg
    simpa only [d71, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d71, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare67 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (1 : Int) + d12 p := by
  change (11 : Int) ≤ (1 : Int) + 12
  decide
theorem compare68 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare67 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare69 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare67 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare68 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare70 (p : Pattern) (guard : d1 p = 1) : d72 p ≤ (1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare69 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare71 (p : Pattern) (guard : d1 p = 1) : d73 p ≤ (1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare72 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (1 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare66 p hg
    simpa only [d74, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare71 p hg
    simpa only [d74, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare73 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (1 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare61 p hg
    simpa only [d75, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare72 p hg
    simpa only [d75, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare74 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (1 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare54 p hg
    simpa only [d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare73 p hg
    simpa only [d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare75 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (1 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare76 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (1 : Int) + d16 p := by
  omega
theorem compare77 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (1 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare78 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (1 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare79 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (1 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40 p hg
    simpa only [d19, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d19, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare80 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40 p hg
    simpa only [d20, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d20, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare81 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (1 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare78 p hg
    simpa only [d21, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare80 p hg
    simpa only [d21, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare82 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (1 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare76 p hg
    simpa only [d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare81 p hg
    simpa only [d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare83 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (1 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48 p hg
    simpa only [d25, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d25, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare84 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (1 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48 p hg
    simpa only [d26, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare83 p hg
    simpa only [d26, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare85 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (1 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare84 p hg
    simpa only [d27, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d27, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare86 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (1 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare81 p hg
    simpa only [d28, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare85 p hg
    simpa only [d28, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare87 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (1 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare82 p hg
    simpa only [d29, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare86 p hg
    simpa only [d29, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare88 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (1 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare89 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare90 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (1 : Int) + d8 p := by
  change (6 : Int) ≤ (1 : Int) + 8
  decide
theorem compare91 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (1 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare90 p hg
    simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare92 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (1 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare90 p hg
    simpa only [d35, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d35, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare93 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (1 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare92 p hg
    simpa only [d36, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d36, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare94 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (1 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare92 p hg
    simpa only [d78, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare93 p hg
    simpa only [d78, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare95 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (1 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare89 p hg
    simpa only [d79, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare94 p hg
    simpa only [d79, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare96 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare69 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare97 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare69 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare96 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare98 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare97 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare99 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (1 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare95 p hg
    simpa only [d80, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d80, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare100 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (1 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare99 p hg
    simpa only [d81, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d81, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare101 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (1 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare87 p hg
    simpa only [d82, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d82, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare102 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d53 p := by
  omega
theorem compare103 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (1 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare78 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare102 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare104 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d20 p := by
  omega
theorem compare105 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (1 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare104 p hg
    simpa only [d55, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare84 p hg
    simpa only [d55, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare106 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (1 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d56, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare105 p hg
    simpa only [d56, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare107 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare108 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare107 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare109 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (1 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare80 p hg
    simpa only [d61, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d61, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare110 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (1 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare109 p hg
    simpa only [d64, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d64, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare111 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (1 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare106 p hg
    simpa only [d65, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare110 p hg
    simpa only [d65, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare112 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (1 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare94 p hg
    simpa only [d83, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d83, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare113 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (1 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare112 p hg
    simpa only [d84, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d84, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare114 (p : Pattern) (guard : d1 p = 1) : d85 p ≤ (1 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d85, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare113 p hg
    simpa only [d85, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d85, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d85, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare115 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (1 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare111 p hg
    simpa only [d86, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare114 p hg
    simpa only [d86, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare116 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (1 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare101 p hg
    simpa only [d87, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d87, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare117 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (1 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d88, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare116 p hg
    simpa only [d88, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare118 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (1 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare116 p hg
    simpa only [d99, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d99, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare119 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (1 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d100, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d100, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d100, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare118 p hg
    simpa only [d100, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare120 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (1 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare119 p hg
    simpa only [d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare121 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (1 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare120 p hg
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare122 (p : Pattern) (guard : d1 p = 1) : d131 p ≤ (1 : Int) + d131 p := by
  omega
theorem compare123 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (1 : Int) + d133 p := by
  omega
theorem compare124 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d109 p := by
  omega
theorem compare125 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (1 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d134, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare124 p hg
    simpa only [d134, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d134, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d134, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare126 (p : Pattern) (guard : d1 p = 1) : d135 p ≤ (1 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d135, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d135, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d135, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare125 p hg
    simpa only [d135, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare127 (p : Pattern) (guard : d1 p = 1) : d136 p ≤ (1 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d136, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare124 p hg
    simpa only [d136, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d136, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare97 p hg
    simpa only [d136, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare128 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (1 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare127 p hg
    simpa only [d137, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d137, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare129 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (1 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare126 p hg
    simpa only [d138, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare128 p hg
    simpa only [d138, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare130 (p : Pattern) (guard : d1 p = 1) : d140 p ≤ (1 : Int) + d140 p := by
  omega
theorem compare131 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (1 : Int) + d125 p := by
  omega
theorem compare132 (p : Pattern) (guard : d1 p = 1) : d141 p ≤ (1 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d141, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare131 p hg
    simpa only [d141, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d141, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d141, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare133 (p : Pattern) (guard : d1 p = 1) : d142 p ≤ (1 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d142, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare130 p hg
    simpa only [d142, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d142, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare132 p hg
    simpa only [d142, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare134 (p : Pattern) (guard : d1 p = 1) : d143 p ≤ (1 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare131 p hg
    simpa only [d143, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d143, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare135 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (1 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d144, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare134 p hg
    simpa only [d144, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d144, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d144, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare136 (p : Pattern) (guard : d1 p = 1) : d145 p ≤ (1 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d145, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare133 p hg
    simpa only [d145, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d145, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare135 p hg
    simpa only [d145, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare137 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (1 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare129 p hg
    simpa only [d146, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare136 p hg
    simpa only [d146, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare138 (p : Pattern) (guard : d1 p = 1) : d147 p ≤ (1 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d147, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare122 p hg
    simpa only [d147, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d147, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare137 p hg
    simpa only [d147, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare139 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (1 : Int) + d152 p := by
  omega
end NetHack.Sokoban22Refined85
