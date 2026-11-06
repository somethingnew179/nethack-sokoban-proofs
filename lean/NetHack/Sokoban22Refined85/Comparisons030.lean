/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4200 (p : Pattern) (guard : d4148 p = 1) : d295 p ≤ (0 : Int) + d1490 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d295, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4199 p hg
    simpa only [d295, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d295, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d295, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4201 (p : Pattern) (guard : d4148 p = 1) : d296 p ≤ (0 : Int) + d1491 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d296, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4197 p hg
    simpa only [d296, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d296, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4200 p hg
    simpa only [d296, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4202 (p : Pattern) (guard : d4148 p = 1) : d297 p ≤ (0 : Int) + d1492 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d297, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4201 p hg
    simpa only [d297, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d297, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4142 p hg
    simpa only [d297, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4203 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1495 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4204 (p : Pattern) (guard : d4303 p = 1) : d702 p ≤ (0 : Int) + d1496 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d702, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4202 p hg
    simpa only [d4303, d702, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d702, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4203 p hg
    simpa only [d4303, d702, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4205 (p : Pattern) (guard : d4303 p = 1) : d703 p ≤ (0 : Int) + d1497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d703, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4193 p hg
    simpa only [d703, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d703, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4204 p hg
    simpa only [d703, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4206 (p : Pattern) (guard : d4303 p = 1) : d704 p ≤ (0 : Int) + d1498 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d704, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4204 p hg
    simpa only [d704, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d704, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d704, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4207 (p : Pattern) (guard : d4303 p = 1) : d705 p ≤ (0 : Int) + d1499 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d705, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4205 p hg
    simpa only [d705, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d705, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4206 p hg
    simpa only [d705, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4208 (p : Pattern) (guard : d4303 p = 1) : d706 p ≤ (0 : Int) + d1500 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d706, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4180 p hg
    simpa only [d706, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d706, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4207 p hg
    simpa only [d706, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4209 (p : Pattern) (guard : d4303 p = 1) : d707 p ≤ (0 : Int) + d1501 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d707, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4103 p hg
    simpa only [d707, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d707, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4208 p hg
    simpa only [d707, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4210 (p : Pattern) (guard : d4303 p = 1) : d708 p ≤ (0 : Int) + d1502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d708, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4171 p hg
    simpa only [d708, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d708, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4209 p hg
    simpa only [d708, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4211 (p : Pattern) (guard : d4303 p = 1) : d709 p ≤ (0 : Int) + d1503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d709, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4162 p hg
    simpa only [d709, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d709, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4210 p hg
    simpa only [d709, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4212 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d16 p := by
  omega
theorem compare4213 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d346 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4214 (p : Pattern) (guard : d4397 p = 1) : d22 p ≤ (0 : Int) + d949 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d22, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d22, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d22, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4213 p hg
    simpa only [d4397, d22, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4215 (p : Pattern) (guard : d0 p = 1) : d27 p ≤ (0 : Int) + d361 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4216 (p : Pattern) (guard : d4397 p = 1) : d28 p ≤ (0 : Int) + d951 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d28, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d4397, d28, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d28, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d4397, d28, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4217 (p : Pattern) (guard : d4397 p = 1) : d29 p ≤ (0 : Int) + d952 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d29, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4214 p hg
    simpa only [d29, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d29, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4216 p hg
    simpa only [d29, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4218 (p : Pattern) (guard : d0 p = 1) : d44 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4219 (p : Pattern) (guard : d4397 p = 1) : d45 p ≤ (0 : Int) + d953 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d45, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4068 p hg
    simpa only [d4397, d45, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d45, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4218 p hg
    simpa only [d4397, d45, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4220 (p : Pattern) (guard : d4148 p = 1) : d47 p ≤ (0 : Int) + d47 p := by
  omega
theorem compare4221 (p : Pattern) (guard : d0 p = 1) : d49 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4222 (p : Pattern) (guard : d4397 p = 1) : d50 p ≤ (0 : Int) + d954 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d50, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4220 p hg
    simpa only [d4397, d50, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d50, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d4397, d50, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4223 (p : Pattern) (guard : d4397 p = 1) : d51 p ≤ (0 : Int) + d955 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d51, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4219 p hg
    simpa only [d51, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d51, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4222 p hg
    simpa only [d51, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4224 (p : Pattern) (guard : d4397 p = 1) : d52 p ≤ (0 : Int) + d956 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d52, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4217 p hg
    simpa only [d52, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d52, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4223 p hg
    simpa only [d52, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4225 (p : Pattern) (guard : d0 p = 1) : d392 p ≤ (0 : Int) + d963 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4226 (p : Pattern) (guard : d4398 p = 1) : d653 p ≤ (0 : Int) + d964 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d653, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4224 p hg
    simpa only [d4398, d653, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d653, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4225 p hg
    simpa only [d4398, d653, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4227 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d361 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4228 (p : Pattern) (guard : d4397 p = 1) : d22 p ≤ (0 : Int) + d965 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d22, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d22, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d22, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4227 p hg
    simpa only [d4397, d22, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4229 (p : Pattern) (guard : d0 p = 1) : d27 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4230 (p : Pattern) (guard : d4397 p = 1) : d28 p ≤ (0 : Int) + d966 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d28, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4077 p hg
    simpa only [d4397, d28, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d28, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d4397, d28, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4231 (p : Pattern) (guard : d4397 p = 1) : d29 p ≤ (0 : Int) + d967 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d29, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4228 p hg
    simpa only [d29, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d29, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d29, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4232 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4233 (p : Pattern) (guard : d4397 p = 1) : d80 p ≤ (0 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d80, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4081 p hg
    simpa only [d4397, d80, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d80, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4397, d80, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4234 (p : Pattern) (guard : d4397 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare4235 (p : Pattern) (guard : d4397 p = 1) : d81 p ≤ (0 : Int) + d969 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d81, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4233 p hg
    simpa only [d81, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d81, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d81, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4236 (p : Pattern) (guard : d4397 p = 1) : d82 p ≤ (0 : Int) + d970 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d82, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4231 p hg
    simpa only [d82, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d82, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4235 p hg
    simpa only [d82, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4237 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (0 : Int) + d975 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4238 (p : Pattern) (guard : d4398 p = 1) : d654 p ≤ (0 : Int) + d976 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d654, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4236 p hg
    simpa only [d4398, d654, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d654, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4237 p hg
    simpa only [d4398, d654, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4239 (p : Pattern) (guard : d4398 p = 1) : d655 p ≤ (0 : Int) + d977 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d655, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4226 p hg
    simpa only [d655, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d655, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4238 p hg
    simpa only [d655, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4240 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d389 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4241 (p : Pattern) (guard : d4397 p = 1) : d22 p ≤ (0 : Int) + d978 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d22, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d22, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d22, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4240 p hg
    simpa only [d4397, d22, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4242 (p : Pattern) (guard : d4397 p = 1) : d29 p ≤ (0 : Int) + d979 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d29, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4241 p hg
    simpa only [d29, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d29, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d29, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4243 (p : Pattern) (guard : d4397 p = 1) : d82 p ≤ (0 : Int) + d980 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d82, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4242 p hg
    simpa only [d82, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d82, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4235 p hg
    simpa only [d82, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4244 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d983 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4245 (p : Pattern) (guard : d4398 p = 1) : d656 p ≤ (0 : Int) + d984 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d656, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4243 p hg
    simpa only [d4398, d656, d984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d656, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4244 p hg
    simpa only [d4398, d656, d984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4246 (p : Pattern) (guard : d4148 p = 1) : d89 p ≤ (0 : Int) + d89 p := by
  omega
theorem compare4247 (p : Pattern) (guard : d4397 p = 1) : d90 p ≤ (0 : Int) + d985 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d90, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4246 p hg
    simpa only [d4397, d90, d985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d90, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4397, d90, d985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4248 (p : Pattern) (guard : d4397 p = 1) : d91 p ≤ (0 : Int) + d91 p := by
  omega
theorem compare4249 (p : Pattern) (guard : d4397 p = 1) : d92 p ≤ (0 : Int) + d986 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d92, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4247 p hg
    simpa only [d92, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d92, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4248 p hg
    simpa only [d92, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4250 (p : Pattern) (guard : d4397 p = 1) : d93 p ≤ (0 : Int) + d93 p := by
  omega
theorem compare4251 (p : Pattern) (guard : d4397 p = 1) : d94 p ≤ (0 : Int) + d987 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d94, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4249 p hg
    simpa only [d94, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d94, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4250 p hg
    simpa only [d94, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4252 (p : Pattern) (guard : d4398 p = 1) : d657 p ≤ (0 : Int) + d988 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d657, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4251 p hg
    simpa only [d4398, d657, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d657, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d4398, d657, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4253 (p : Pattern) (guard : d4398 p = 1) : d658 p ≤ (0 : Int) + d989 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d658, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4245 p hg
    simpa only [d658, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d658, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4252 p hg
    simpa only [d658, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4254 (p : Pattern) (guard : d4398 p = 1) : d659 p ≤ (0 : Int) + d990 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d659, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4239 p hg
    simpa only [d659, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d659, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4253 p hg
    simpa only [d659, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4255 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d386 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4256 (p : Pattern) (guard : d4397 p = 1) : d22 p ≤ (0 : Int) + d991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d22, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d22, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d22, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4255 p hg
    simpa only [d4397, d22, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4257 (p : Pattern) (guard : d4397 p = 1) : d28 p ≤ (0 : Int) + d992 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d28, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d4397, d28, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d28, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d4397, d28, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4258 (p : Pattern) (guard : d4397 p = 1) : d29 p ≤ (0 : Int) + d993 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d29, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d29, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d29, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d29, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4259 (p : Pattern) (guard : d0 p = 1) : d44 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4260 (p : Pattern) (guard : d4397 p = 1) : d45 p ≤ (0 : Int) + d994 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d45, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4068 p hg
    simpa only [d4397, d45, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d45, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4259 p hg
    simpa only [d4397, d45, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4261 (p : Pattern) (guard : d4397 p = 1) : d51 p ≤ (0 : Int) + d995 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d51, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4260 p hg
    simpa only [d51, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d51, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4222 p hg
    simpa only [d51, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4262 (p : Pattern) (guard : d4397 p = 1) : d52 p ≤ (0 : Int) + d996 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d52, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4258 p hg
    simpa only [d52, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d52, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4261 p hg
    simpa only [d52, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4263 (p : Pattern) (guard : d0 p = 1) : d397 p ≤ (0 : Int) + d999 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4264 (p : Pattern) (guard : d4398 p = 1) : d660 p ≤ (0 : Int) + d1000 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d660, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4262 p hg
    simpa only [d4398, d660, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d660, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4263 p hg
    simpa only [d4398, d660, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4265 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4266 (p : Pattern) (guard : d4397 p = 1) : d22 p ≤ (0 : Int) + d1001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d22, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d22, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d22, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d4397, d22, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4267 (p : Pattern) (guard : d4397 p = 1) : d29 p ≤ (0 : Int) + d1002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d29, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4266 p hg
    simpa only [d29, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d29, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d29, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4268 (p : Pattern) (guard : d4397 p = 1) : d82 p ≤ (0 : Int) + d1003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d82, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4267 p hg
    simpa only [d82, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d82, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4235 p hg
    simpa only [d82, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4269 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d1005 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4270 (p : Pattern) (guard : d4398 p = 1) : d661 p ≤ (0 : Int) + d1006 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d661, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4268 p hg
    simpa only [d4398, d661, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d661, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4269 p hg
    simpa only [d4398, d661, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4271 (p : Pattern) (guard : d4398 p = 1) : d662 p ≤ (0 : Int) + d1007 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d662, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4264 p hg
    simpa only [d662, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d662, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4270 p hg
    simpa only [d662, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4272 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4273 (p : Pattern) (guard : d4397 p = 1) : d22 p ≤ (0 : Int) + d1008 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d22, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d22, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d22, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4272 p hg
    simpa only [d4397, d22, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4274 (p : Pattern) (guard : d4397 p = 1) : d29 p ≤ (0 : Int) + d1009 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d29, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d29, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d29, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d29, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4275 (p : Pattern) (guard : d4397 p = 1) : d82 p ≤ (0 : Int) + d1010 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d82, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4274 p hg
    simpa only [d82, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d82, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4235 p hg
    simpa only [d82, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4276 (p : Pattern) (guard : d0 p = 1) : d410 p ≤ (0 : Int) + d1005 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4277 (p : Pattern) (guard : d4398 p = 1) : d663 p ≤ (0 : Int) + d1011 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d663, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4275 p hg
    simpa only [d4398, d663, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d663, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4276 p hg
    simpa only [d4398, d663, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4278 (p : Pattern) (guard : d4398 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare4279 (p : Pattern) (guard : d4398 p = 1) : d664 p ≤ (0 : Int) + d1012 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d664, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4277 p hg
    simpa only [d664, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d664, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d664, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4280 (p : Pattern) (guard : d4398 p = 1) : d665 p ≤ (0 : Int) + d1013 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d665, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4271 p hg
    simpa only [d665, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d665, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4279 p hg
    simpa only [d665, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4281 (p : Pattern) (guard : d4398 p = 1) : d666 p ≤ (0 : Int) + d1014 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d666, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4254 p hg
    simpa only [d666, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d666, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4280 p hg
    simpa only [d666, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4282 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d355 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4283 (p : Pattern) (guard : d4397 p = 1) : d22 p ≤ (0 : Int) + d1015 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d22, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d22, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d22, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4282 p hg
    simpa only [d4397, d22, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4284 (p : Pattern) (guard : d0 p = 1) : d27 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4285 (p : Pattern) (guard : d4397 p = 1) : d28 p ≤ (0 : Int) + d1016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d28, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d4397, d28, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d28, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4284 p hg
    simpa only [d4397, d28, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4286 (p : Pattern) (guard : d4397 p = 1) : d29 p ≤ (0 : Int) + d1017 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d29, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4283 p hg
    simpa only [d29, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d29, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4285 p hg
    simpa only [d29, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4287 (p : Pattern) (guard : d0 p = 1) : d44 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4288 (p : Pattern) (guard : d4397 p = 1) : d45 p ≤ (0 : Int) + d1018 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d45, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4068 p hg
    simpa only [d4397, d45, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d45, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4287 p hg
    simpa only [d4397, d45, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4289 (p : Pattern) (guard : d4397 p = 1) : d51 p ≤ (0 : Int) + d1019 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d51, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4288 p hg
    simpa only [d51, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d51, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4222 p hg
    simpa only [d51, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4290 (p : Pattern) (guard : d4397 p = 1) : d52 p ≤ (0 : Int) + d1020 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d52, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4286 p hg
    simpa only [d52, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d52, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4289 p hg
    simpa only [d52, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4291 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d1023 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4292 (p : Pattern) (guard : d4398 p = 1) : d667 p ≤ (0 : Int) + d1024 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d667, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4290 p hg
    simpa only [d4398, d667, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d667, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d4398, d667, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4293 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4294 (p : Pattern) (guard : d4397 p = 1) : d22 p ≤ (0 : Int) + d1025 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d22, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d22, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d22, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4293 p hg
    simpa only [d4397, d22, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4295 (p : Pattern) (guard : d4397 p = 1) : d29 p ≤ (0 : Int) + d1026 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d29, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4294 p hg
    simpa only [d29, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d29, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d29, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4296 (p : Pattern) (guard : d4397 p = 1) : d82 p ≤ (0 : Int) + d1027 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4295 p hg
    simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4235 p hg
    simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4297 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d1005 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4298 (p : Pattern) (guard : d4398 p = 1) : d668 p ≤ (0 : Int) + d1028 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d668, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4296 p hg
    simpa only [d4398, d668, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d668, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4297 p hg
    simpa only [d4398, d668, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4299 (p : Pattern) (guard : d4398 p = 1) : d669 p ≤ (0 : Int) + d1029 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d669, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4292 p hg
    simpa only [d669, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d669, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4298 p hg
    simpa only [d669, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4300 (p : Pattern) (guard : d4398 p = 1) : d670 p ≤ (0 : Int) + d988 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d670, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4251 p hg
    simpa only [d4398, d670, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d670, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3470 p hg
    simpa only [d4398, d670, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4301 (p : Pattern) (guard : d4398 p = 1) : d671 p ≤ (0 : Int) + d1030 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d671, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4238 p hg
    simpa only [d671, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d671, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4300 p hg
    simpa only [d671, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4302 (p : Pattern) (guard : d4398 p = 1) : d672 p ≤ (0 : Int) + d1031 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d672, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4299 p hg
    simpa only [d672, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d672, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4301 p hg
    simpa only [d672, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4303 (p : Pattern) (guard : d4397 p = 1) : d29 p ≤ (0 : Int) + d1032 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d29, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4241 p hg
    simpa only [d29, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d29, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d29, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4304 (p : Pattern) (guard : d4397 p = 1) : d52 p ≤ (0 : Int) + d1033 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d52, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4303 p hg
    simpa only [d52, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d52, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4261 p hg
    simpa only [d52, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4305 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d1035 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4306 (p : Pattern) (guard : d4398 p = 1) : d673 p ≤ (0 : Int) + d1036 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d673, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4304 p hg
    simpa only [d4398, d673, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d673, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4305 p hg
    simpa only [d4398, d673, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4307 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d1005 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4308 (p : Pattern) (guard : d4398 p = 1) : d674 p ≤ (0 : Int) + d1006 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d674, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4268 p hg
    simpa only [d4398, d674, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d674, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4307 p hg
    simpa only [d4398, d674, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4309 (p : Pattern) (guard : d4398 p = 1) : d675 p ≤ (0 : Int) + d1037 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d675, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d675, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d675, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4308 p hg
    simpa only [d675, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4310 (p : Pattern) (guard : d4398 p = 1) : d676 p ≤ (0 : Int) + d1038 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d676, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4270 p hg
    simpa only [d676, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d676, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d676, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4311 (p : Pattern) (guard : d4398 p = 1) : d677 p ≤ (0 : Int) + d1039 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d677, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4309 p hg
    simpa only [d677, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d677, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d677, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4312 (p : Pattern) (guard : d4398 p = 1) : d678 p ≤ (0 : Int) + d1040 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d678, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4302 p hg
    simpa only [d678, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d678, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4311 p hg
    simpa only [d678, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4313 (p : Pattern) (guard : d4398 p = 1) : d679 p ≤ (0 : Int) + d1041 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d679, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4281 p hg
    simpa only [d679, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d679, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4312 p hg
    simpa only [d679, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4314 (p : Pattern) (guard : d4148 p = 1) : d105 p ≤ (0 : Int) + d105 p := by
  omega
theorem compare4315 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d355 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4316 (p : Pattern) (guard : d4397 p = 1) : d111 p ≤ (0 : Int) + d1042 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d111, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d111, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d111, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4315 p hg
    simpa only [d4397, d111, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4317 (p : Pattern) (guard : d0 p = 1) : d112 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4318 (p : Pattern) (guard : d4397 p = 1) : d113 p ≤ (0 : Int) + d1044 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d113, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4123 p hg
    simpa only [d4397, d113, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d113, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4317 p hg
    simpa only [d4397, d113, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4319 (p : Pattern) (guard : d4397 p = 1) : d114 p ≤ (0 : Int) + d1045 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d114, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4316 p hg
    simpa only [d114, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d114, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4318 p hg
    simpa only [d114, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4320 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4321 (p : Pattern) (guard : d4397 p = 1) : d127 p ≤ (0 : Int) + d1046 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d127, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4127 p hg
    simpa only [d4397, d127, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d127, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4320 p hg
    simpa only [d4397, d127, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4322 (p : Pattern) (guard : d0 p = 1) : d128 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4323 (p : Pattern) (guard : d4397 p = 1) : d129 p ≤ (0 : Int) + d1047 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d129, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4128 p hg
    simpa only [d4397, d129, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d129, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d4397, d129, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4324 (p : Pattern) (guard : d4397 p = 1) : d130 p ≤ (0 : Int) + d1048 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d130, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4321 p hg
    simpa only [d130, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d130, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4323 p hg
    simpa only [d130, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4325 (p : Pattern) (guard : d4397 p = 1) : d131 p ≤ (0 : Int) + d1049 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d131, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4319 p hg
    simpa only [d131, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d131, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4324 p hg
    simpa only [d131, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4326 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d1056 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4327 (p : Pattern) (guard : d4398 p = 1) : d680 p ≤ (0 : Int) + d1057 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d680, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4325 p hg
    simpa only [d4398, d680, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d680, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4326 p hg
    simpa only [d4398, d680, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4328 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4329 (p : Pattern) (guard : d4397 p = 1) : d111 p ≤ (0 : Int) + d1058 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d111, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d111, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d111, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4328 p hg
    simpa only [d4397, d111, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4330 (p : Pattern) (guard : d0 p = 1) : d112 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4331 (p : Pattern) (guard : d4397 p = 1) : d113 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d113, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4136 p hg
    simpa only [d4397, d113, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d113, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4397, d113, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4332 (p : Pattern) (guard : d4397 p = 1) : d114 p ≤ (0 : Int) + d1060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d114, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4329 p hg
    simpa only [d114, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d114, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4331 p hg
    simpa only [d114, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4333 (p : Pattern) (guard : d4397 p = 1) : d150 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4140 p hg
    simpa only [d4397, d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4334 (p : Pattern) (guard : d4397 p = 1) : d151 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4333 p hg
    simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4335 (p : Pattern) (guard : d4397 p = 1) : d152 p ≤ (0 : Int) + d1063 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d152, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4332 p hg
    simpa only [d152, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d152, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4334 p hg
    simpa only [d152, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4336 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d1067 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4337 (p : Pattern) (guard : d4398 p = 1) : d681 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d681, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4335 p hg
    simpa only [d4398, d681, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d681, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4336 p hg
    simpa only [d4398, d681, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4338 (p : Pattern) (guard : d4398 p = 1) : d682 p ≤ (0 : Int) + d1069 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d682, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4327 p hg
    simpa only [d682, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d682, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4337 p hg
    simpa only [d682, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4339 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d361 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
