/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4200 (p : Pattern) (guard : d851 p = 1) : d516 p ≤ (8 : Int) + d233 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d516, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4192 p hg
    simpa only [d516, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d516, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4199 p hg
    simpa only [d516, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4201 (p : Pattern) (guard : d851 p = 1) : d66 p ≤ (8 : Int) + d66 p := by
  omega
theorem compare4202 (p : Pattern) (guard : d851 p = 1) : d517 p ≤ (8 : Int) + d234 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d517, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4199 p hg
    simpa only [d517, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d517, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4201 p hg
    simpa only [d517, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4203 (p : Pattern) (guard : d851 p = 1) : d518 p ≤ (8 : Int) + d235 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d518, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4200 p hg
    simpa only [d518, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d518, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4202 p hg
    simpa only [d518, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4204 (p : Pattern) (guard : d851 p = 1) : d519 p ≤ (8 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d519, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4187 p hg
    simpa only [d519, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d519, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4201 p hg
    simpa only [d519, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4205 (p : Pattern) (guard : d851 p = 1) : d520 p ≤ (8 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d520, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4195 p hg
    simpa only [d520, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d520, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4201 p hg
    simpa only [d520, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4206 (p : Pattern) (guard : d851 p = 1) : d521 p ≤ (8 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d521, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4204 p hg
    simpa only [d521, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d521, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4205 p hg
    simpa only [d521, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4207 (p : Pattern) (guard : d851 p = 1) : d522 p ≤ (8 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d522, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4205 p hg
    simpa only [d522, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d522, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4201 p hg
    simpa only [d522, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4208 (p : Pattern) (guard : d851 p = 1) : d523 p ≤ (8 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d523, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4206 p hg
    simpa only [d523, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d523, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4207 p hg
    simpa only [d523, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4209 (p : Pattern) (guard : d851 p = 1) : d524 p ≤ (8 : Int) + d236 p := by
  cases selected : p 108 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d524, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4203 p hg
    simpa only [d524, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d524, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4208 p hg
    simpa only [d524, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4210 (p : Pattern) (guard : d851 p = 1) : d119 p ≤ (0 : Int) + d119 p := by
  omega
theorem compare4211 (p : Pattern) (guard : d851 p = 1) : d119 p ≤ (0 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4210 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4212 (p : Pattern) (guard : d851 p = 1) : d505 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d505, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4211 p hg
    simpa only [d505, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d505, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d505, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4213 (p : Pattern) (guard : d851 p = 1) : d505 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4153 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4214 (p : Pattern) (guard : d851 p = 1) : d505 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4153 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4213 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4215 (p : Pattern) (guard : d851 p = 1) : d125 p ≤ (0 : Int) + d125 p := by
  omega
theorem compare4216 (p : Pattern) (guard : d851 p = 1) : d125 p ≤ (0 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4085 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4217 (p : Pattern) (guard : d851 p = 1) : d502 p ≤ (0 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d502, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4211 p hg
    simpa only [d502, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d502, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4216 p hg
    simpa only [d502, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4218 (p : Pattern) (guard : d851 p = 1) : d506 p ≤ (0 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d506, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4217 p hg
    simpa only [d506, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d506, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d506, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4219 (p : Pattern) (guard : d851 p = 1) : d506 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4154 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4218 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4220 (p : Pattern) (guard : d851 p = 1) : d506 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4154 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4219 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4221 (p : Pattern) (guard : d851 p = 1) : d507 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d507, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4214 p hg
    simpa only [d507, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d507, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4220 p hg
    simpa only [d507, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4222 (p : Pattern) (guard : d851 p = 1) : d508 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d508, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4152 p hg
    simpa only [d508, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d508, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d508, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4223 (p : Pattern) (guard : d851 p = 1) : d512 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d512, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4213 p hg
    simpa only [d512, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d512, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d512, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4224 (p : Pattern) (guard : d851 p = 1) : d513 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d513, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4219 p hg
    simpa only [d513, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d513, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d513, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4225 (p : Pattern) (guard : d851 p = 1) : d514 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d514, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4223 p hg
    simpa only [d514, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d514, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4224 p hg
    simpa only [d514, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4226 (p : Pattern) (guard : d851 p = 1) : d515 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d515, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4159 p hg
    simpa only [d515, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d515, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4225 p hg
    simpa only [d515, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4227 (p : Pattern) (guard : d851 p = 1) : d516 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d516, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4222 p hg
    simpa only [d516, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d516, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4226 p hg
    simpa only [d516, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4228 (p : Pattern) (guard : d851 p = 1) : d517 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d517, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4226 p hg
    simpa only [d517, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d517, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d517, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4229 (p : Pattern) (guard : d851 p = 1) : d518 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d518, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4227 p hg
    simpa only [d518, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d518, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4228 p hg
    simpa only [d518, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4230 (p : Pattern) (guard : d851 p = 1) : d137 p ≤ (0 : Int) + d137 p := by
  omega
theorem compare4231 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4211 p hg
    simpa only [d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4232 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4147 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4231 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4233 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4147 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4234 (p : Pattern) (guard : d851 p = 1) : d144 p ≤ (0 : Int) + d144 p := by
  omega
theorem compare4235 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d503, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4217 p hg
    simpa only [d503, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d503, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d503, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4236 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4151 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4235 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4237 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4151 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4236 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4238 (p : Pattern) (guard : d851 p = 1) : d504 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d504, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4233 p hg
    simpa only [d504, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d504, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4237 p hg
    simpa only [d504, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4239 (p : Pattern) (guard : d851 p = 1) : d519 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d519, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4238 p hg
    simpa only [d519, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d519, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d519, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4240 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d501, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d501, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d501, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d501, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4241 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4240 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4231 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4242 (p : Pattern) (guard : d851 p = 1) : d509 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d509, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4241 p hg
    simpa only [d509, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d509, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d509, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4243 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d503, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4148 p hg
    simpa only [d503, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d503, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d503, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4244 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4243 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4235 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4245 (p : Pattern) (guard : d851 p = 1) : d510 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d510, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4244 p hg
    simpa only [d510, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d510, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d510, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4246 (p : Pattern) (guard : d851 p = 1) : d511 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d511, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4242 p hg
    simpa only [d511, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d511, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4245 p hg
    simpa only [d511, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4247 (p : Pattern) (guard : d851 p = 1) : d520 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d520, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4246 p hg
    simpa only [d520, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d520, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d520, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4248 (p : Pattern) (guard : d851 p = 1) : d521 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d521, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4239 p hg
    simpa only [d521, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d521, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4247 p hg
    simpa only [d521, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4249 (p : Pattern) (guard : d851 p = 1) : d509 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d509, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d509, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d509, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d509, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4250 (p : Pattern) (guard : d851 p = 1) : d510 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d510, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4236 p hg
    simpa only [d510, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d510, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d510, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4251 (p : Pattern) (guard : d851 p = 1) : d511 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d511, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4249 p hg
    simpa only [d511, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d511, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4250 p hg
    simpa only [d511, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4252 (p : Pattern) (guard : d851 p = 1) : d520 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d520, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4251 p hg
    simpa only [d520, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d520, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d520, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4253 (p : Pattern) (guard : d851 p = 1) : d522 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d522, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4252 p hg
    simpa only [d522, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d522, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d522, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4254 (p : Pattern) (guard : d851 p = 1) : d523 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d523, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4248 p hg
    simpa only [d523, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d523, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4253 p hg
    simpa only [d523, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4255 (p : Pattern) (guard : d851 p = 1) : d524 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d524, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d524, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d524, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4254 p hg
    simpa only [d524, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4256 (p : Pattern) (guard : d851 p = 1) : d119 p ≤ (2 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare767 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4257 (p : Pattern) (guard : d851 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare4258 (p : Pattern) (guard : d851 p = 1) : d137 p ≤ (2 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4259 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4258 p hg
    simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4260 (p : Pattern) (guard : d851 p = 1) : d125 p ≤ (2 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare771 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4261 (p : Pattern) (guard : d851 p = 1) : d502 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4260 p hg
    simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4262 (p : Pattern) (guard : d851 p = 1) : d60 p ≤ (2 : Int) + d60 p := by
  omega
theorem compare4263 (p : Pattern) (guard : d851 p = 1) : d143 p ≤ (2 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4260 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4262 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4264 (p : Pattern) (guard : d851 p = 1) : d144 p ≤ (2 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4258 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4263 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4265 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4261 p hg
    simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4264 p hg
    simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4266 (p : Pattern) (guard : d851 p = 1) : d504 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4259 p hg
    simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4267 (p : Pattern) (guard : d851 p = 1) : d505 p ≤ (2 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4268 (p : Pattern) (guard : d851 p = 1) : d119 p ≤ (2 : Int) + d119 p := by
  omega
theorem compare4269 (p : Pattern) (guard : d851 p = 1) : d119 p ≤ (2 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4268 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4270 (p : Pattern) (guard : d851 p = 1) : d505 p ≤ (2 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d505, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4269 p hg
    simpa only [d505, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d505, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d505, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4271 (p : Pattern) (guard : d851 p = 1) : d505 p ≤ (2 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4267 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4270 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4272 (p : Pattern) (guard : d851 p = 1) : d505 p ≤ (2 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4267 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4271 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4273 (p : Pattern) (guard : d851 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare4274 (p : Pattern) (guard : d851 p = 1) : d506 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4261 p hg
    simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4275 (p : Pattern) (guard : d851 p = 1) : d125 p ≤ (2 : Int) + d125 p := by
  omega
theorem compare4276 (p : Pattern) (guard : d851 p = 1) : d125 p ≤ (2 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4260 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4275 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4277 (p : Pattern) (guard : d851 p = 1) : d502 p ≤ (2 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d502, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4269 p hg
    simpa only [d502, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d502, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4276 p hg
    simpa only [d502, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4278 (p : Pattern) (guard : d851 p = 1) : d506 p ≤ (2 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d506, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4277 p hg
    simpa only [d506, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d506, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d506, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4279 (p : Pattern) (guard : d851 p = 1) : d506 p ≤ (2 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4274 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4280 (p : Pattern) (guard : d851 p = 1) : d506 p ≤ (2 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4274 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4279 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4281 (p : Pattern) (guard : d851 p = 1) : d507 p ≤ (2 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d507, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4272 p hg
    simpa only [d507, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d507, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4280 p hg
    simpa only [d507, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4282 (p : Pattern) (guard : d851 p = 1) : d508 p ≤ (2 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d508, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4266 p hg
    simpa only [d508, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d508, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4281 p hg
    simpa only [d508, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4283 (p : Pattern) (guard : d851 p = 1) : d509 p ≤ (2 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4259 p hg
    simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4284 (p : Pattern) (guard : d851 p = 1) : d510 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4285 (p : Pattern) (guard : d851 p = 1) : d511 p ≤ (2 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4283 p hg
    simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4284 p hg
    simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4286 (p : Pattern) (guard : d851 p = 1) : d512 p ≤ (2 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d512, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4271 p hg
    simpa only [d512, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d512, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d512, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4287 (p : Pattern) (guard : d851 p = 1) : d513 p ≤ (2 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d513, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4279 p hg
    simpa only [d513, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d513, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d513, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4288 (p : Pattern) (guard : d851 p = 1) : d514 p ≤ (2 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d514, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4286 p hg
    simpa only [d514, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d514, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4287 p hg
    simpa only [d514, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4289 (p : Pattern) (guard : d851 p = 1) : d515 p ≤ (2 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d515, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4285 p hg
    simpa only [d515, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d515, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4288 p hg
    simpa only [d515, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4290 (p : Pattern) (guard : d851 p = 1) : d516 p ≤ (2 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d516, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4282 p hg
    simpa only [d516, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d516, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4289 p hg
    simpa only [d516, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4291 (p : Pattern) (guard : d851 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare4292 (p : Pattern) (guard : d851 p = 1) : d517 p ≤ (2 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d517, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4289 p hg
    simpa only [d517, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d517, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d517, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4293 (p : Pattern) (guard : d851 p = 1) : d518 p ≤ (2 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d518, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4290 p hg
    simpa only [d518, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d518, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4292 p hg
    simpa only [d518, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4294 (p : Pattern) (guard : d851 p = 1) : d137 p ≤ (2 : Int) + d137 p := by
  omega
theorem compare4295 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (2 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4269 p hg
    simpa only [d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4294 p hg
    simpa only [d501, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4296 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (2 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4259 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4295 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4297 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (2 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4259 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4296 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4298 (p : Pattern) (guard : d851 p = 1) : d144 p ≤ (2 : Int) + d144 p := by
  omega
theorem compare4299 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d503, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4277 p hg
    simpa only [d503, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d503, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4298 p hg
    simpa only [d503, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4300 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (2 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4299 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4301 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (2 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4300 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4302 (p : Pattern) (guard : d851 p = 1) : d504 p ≤ (2 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d504, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4297 p hg
    simpa only [d504, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d504, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4301 p hg
    simpa only [d504, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4303 (p : Pattern) (guard : d851 p = 1) : d519 p ≤ (2 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d519, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4302 p hg
    simpa only [d519, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d519, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d519, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4304 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d501, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d501, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d501, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4294 p hg
    simpa only [d501, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4305 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (2 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4304 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4295 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4306 (p : Pattern) (guard : d851 p = 1) : d509 p ≤ (2 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d509, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4305 p hg
    simpa only [d509, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d509, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d509, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4307 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (2 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d503, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4261 p hg
    simpa only [d503, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d503, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4298 p hg
    simpa only [d503, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4308 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (2 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4307 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4299 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4309 (p : Pattern) (guard : d851 p = 1) : d510 p ≤ (2 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d510, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4308 p hg
    simpa only [d510, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d510, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d510, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4310 (p : Pattern) (guard : d851 p = 1) : d511 p ≤ (2 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d511, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d511, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d511, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4309 p hg
    simpa only [d511, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4311 (p : Pattern) (guard : d851 p = 1) : d520 p ≤ (2 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d520, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d520, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d520, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d520, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4312 (p : Pattern) (guard : d851 p = 1) : d521 p ≤ (2 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d521, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4303 p hg
    simpa only [d521, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d521, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4311 p hg
    simpa only [d521, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4313 (p : Pattern) (guard : d851 p = 1) : d509 p ≤ (2 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d509, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4296 p hg
    simpa only [d509, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d509, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d509, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4314 (p : Pattern) (guard : d851 p = 1) : d510 p ≤ (2 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d510, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4300 p hg
    simpa only [d510, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d510, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d510, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4315 (p : Pattern) (guard : d851 p = 1) : d511 p ≤ (2 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d511, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4313 p hg
    simpa only [d511, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d511, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d511, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4316 (p : Pattern) (guard : d851 p = 1) : d520 p ≤ (2 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d520, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4315 p hg
    simpa only [d520, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d520, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d520, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4317 (p : Pattern) (guard : d851 p = 1) : d522 p ≤ (2 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d522, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4316 p hg
    simpa only [d522, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d522, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d522, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4318 (p : Pattern) (guard : d851 p = 1) : d523 p ≤ (2 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d523, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4312 p hg
    simpa only [d523, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d523, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4317 p hg
    simpa only [d523, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4319 (p : Pattern) (guard : d851 p = 1) : d524 p ≤ (2 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d524, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4293 p hg
    simpa only [d524, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d524, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4318 p hg
    simpa only [d524, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4320 (p : Pattern) (guard : d1053 p = 1) : d119 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1053, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d1053, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1053, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3648 p hg
    simpa only [d1053, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4321 (p : Pattern) (guard : d1053 p = 1) : d501 p ≤ (0 : Int) + d56 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4320 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4081 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4322 (p : Pattern) (guard : d1053 p = 1) : d125 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1053, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4085 p hg
    simpa only [d1053, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1053, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3653 p hg
    simpa only [d1053, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4323 (p : Pattern) (guard : d1053 p = 1) : d502 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d502, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4320 p hg
    simpa only [d502, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d502, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d502, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4324 (p : Pattern) (guard : d1053 p = 1) : d503 p ≤ (0 : Int) + d62 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4323 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4087 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4325 (p : Pattern) (guard : d1053 p = 1) : d504 p ≤ (0 : Int) + d451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d504, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4321 p hg
    simpa only [d504, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d504, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4324 p hg
    simpa only [d504, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4326 (p : Pattern) (guard : d1053 p = 1) : d505 p ≤ (0 : Int) + d452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d505, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4320 p hg
    simpa only [d505, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d505, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d505, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4327 (p : Pattern) (guard : d1053 p = 1) : d506 p ≤ (0 : Int) + d453 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d506, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4323 p hg
    simpa only [d506, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d506, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d506, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4328 (p : Pattern) (guard : d1053 p = 1) : d507 p ≤ (0 : Int) + d454 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d507, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4326 p hg
    simpa only [d507, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d507, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4327 p hg
    simpa only [d507, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4329 (p : Pattern) (guard : d1053 p = 1) : d508 p ≤ (0 : Int) + d455 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d508, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4325 p hg
    simpa only [d508, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d508, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4328 p hg
    simpa only [d508, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4330 (p : Pattern) (guard : d1053 p = 1) : d509 p ≤ (0 : Int) + d456 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d509, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4321 p hg
    simpa only [d509, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d509, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d509, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4331 (p : Pattern) (guard : d1053 p = 1) : d510 p ≤ (0 : Int) + d457 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d510, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4324 p hg
    simpa only [d510, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d510, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d510, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4332 (p : Pattern) (guard : d1053 p = 1) : d511 p ≤ (0 : Int) + d458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d511, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d511, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d511, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4331 p hg
    simpa only [d511, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4333 (p : Pattern) (guard : d1053 p = 1) : d512 p ≤ (0 : Int) + d459 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d512, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4326 p hg
    simpa only [d512, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d512, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d512, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4334 (p : Pattern) (guard : d1053 p = 1) : d513 p ≤ (0 : Int) + d460 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d513, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4327 p hg
    simpa only [d513, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d513, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d513, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4335 (p : Pattern) (guard : d1053 p = 1) : d514 p ≤ (0 : Int) + d461 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d514, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4333 p hg
    simpa only [d514, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d514, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4334 p hg
    simpa only [d514, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4336 (p : Pattern) (guard : d1053 p = 1) : d515 p ≤ (0 : Int) + d462 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d515, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4332 p hg
    simpa only [d515, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d515, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4335 p hg
    simpa only [d515, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4337 (p : Pattern) (guard : d1053 p = 1) : d516 p ≤ (0 : Int) + d463 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d516, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4329 p hg
    simpa only [d516, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d516, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4336 p hg
    simpa only [d516, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4338 (p : Pattern) (guard : d1053 p = 1) : d517 p ≤ (0 : Int) + d464 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d517, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4336 p hg
    simpa only [d517, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d517, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d517, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4339 (p : Pattern) (guard : d1053 p = 1) : d518 p ≤ (0 : Int) + d465 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d518, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4337 p hg
    simpa only [d518, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d518, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4338 p hg
    simpa only [d518, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
