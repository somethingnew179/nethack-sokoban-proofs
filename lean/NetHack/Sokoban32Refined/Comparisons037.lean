/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5180 (p : Pattern) (guard : d857 p = 1) : d104 p ≤ (0 : Int) + d202 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d104, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5167 p hg
    simpa only [d104, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d104, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d104, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5181 (p : Pattern) (guard : d857 p = 1) : d105 p ≤ (0 : Int) + d203 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d105, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5168 p hg
    simpa only [d105, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d105, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5180 p hg
    simpa only [d105, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5182 (p : Pattern) (guard : d857 p = 1) : d106 p ≤ (0 : Int) + d204 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d106, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d106, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d106, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5181 p hg
    simpa only [d106, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5183 (p : Pattern) (guard : d0 p = 1) : d113 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5184 (p : Pattern) (guard : d1072 p = 1) : d114 p ≤ (0 : Int) + d205 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d114, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5182 p hg
    simpa only [d1072, d114, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d114, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d1072, d114, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5185 (p : Pattern) (guard : d1072 p = 1) : d115 p ≤ (0 : Int) + d206 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d115, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5179 p hg
    simpa only [d115, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d115, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5184 p hg
    simpa only [d115, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5186 (p : Pattern) (guard : d1072 p = 1) : d116 p ≤ (0 : Int) + d207 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d116, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d116, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d116, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5185 p hg
    simpa only [d116, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5187 (p : Pattern) (guard : d1072 p = 1) : d67 p ≤ (0 : Int) + d208 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d67, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d1072, d67, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d67, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare427 p hg
    simpa only [d1072, d67, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5188 (p : Pattern) (guard : d1072 p = 1) : d117 p ≤ (0 : Int) + d209 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d117, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d1072, d117, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d117, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare430 p hg
    simpa only [d1072, d117, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5189 (p : Pattern) (guard : d1072 p = 1) : d118 p ≤ (0 : Int) + d210 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d118, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5187 p hg
    simpa only [d118, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d118, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5188 p hg
    simpa only [d118, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5190 (p : Pattern) (guard : d857 p = 1) : d120 p ≤ (0 : Int) + d211 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d120, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d857, d120, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d120, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d857, d120, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5191 (p : Pattern) (guard : d857 p = 1) : d121 p ≤ (0 : Int) + d212 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d121, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d121, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d121, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5190 p hg
    simpa only [d121, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5192 (p : Pattern) (guard : d857 p = 1) : d122 p ≤ (0 : Int) + d213 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d122, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5191 p hg
    simpa only [d122, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d122, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5174 p hg
    simpa only [d122, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5193 (p : Pattern) (guard : d857 p = 1) : d123 p ≤ (0 : Int) + d214 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d123, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5168 p hg
    simpa only [d123, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d123, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5192 p hg
    simpa only [d123, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5194 (p : Pattern) (guard : d857 p = 1) : d124 p ≤ (0 : Int) + d215 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d124, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d124, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d124, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5193 p hg
    simpa only [d124, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5195 (p : Pattern) (guard : d0 p = 1) : d127 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5196 (p : Pattern) (guard : d1072 p = 1) : d128 p ≤ (0 : Int) + d216 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d128, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5194 p hg
    simpa only [d1072, d128, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d128, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5195 p hg
    simpa only [d1072, d128, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5197 (p : Pattern) (guard : d857 p = 1) : d53 p ≤ (0 : Int) + d217 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d53, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d857, d53, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d53, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d857, d53, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5198 (p : Pattern) (guard : d857 p = 1) : d55 p ≤ (0 : Int) + d218 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d55, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d857, d55, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d55, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d857, d55, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5199 (p : Pattern) (guard : d857 p = 1) : d56 p ≤ (0 : Int) + d219 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d56, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5197 p hg
    simpa only [d56, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d56, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d56, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5200 (p : Pattern) (guard : d857 p = 1) : d57 p ≤ (0 : Int) + d220 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d57, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5197 p hg
    simpa only [d57, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d57, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d57, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5201 (p : Pattern) (guard : d857 p = 1) : d81 p ≤ (0 : Int) + d221 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d81, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d81, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d81, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d81, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5202 (p : Pattern) (guard : d857 p = 1) : d82 p ≤ (0 : Int) + d222 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d82, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5200 p hg
    simpa only [d82, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d82, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5201 p hg
    simpa only [d82, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5203 (p : Pattern) (guard : d857 p = 1) : d129 p ≤ (0 : Int) + d223 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d129, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d129, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d129, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5202 p hg
    simpa only [d129, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5204 (p : Pattern) (guard : d1072 p = 1) : d131 p ≤ (0 : Int) + d224 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d131, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5203 p hg
    simpa only [d1072, d131, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d131, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2038 p hg
    simpa only [d1072, d131, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5205 (p : Pattern) (guard : d1072 p = 1) : d132 p ≤ (0 : Int) + d225 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d132, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5196 p hg
    simpa only [d132, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d132, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5204 p hg
    simpa only [d132, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5206 (p : Pattern) (guard : d1072 p = 1) : d133 p ≤ (0 : Int) + d226 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d133, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5189 p hg
    simpa only [d133, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d133, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5205 p hg
    simpa only [d133, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5207 (p : Pattern) (guard : d1072 p = 1) : d134 p ≤ (0 : Int) + d227 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d134, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5186 p hg
    simpa only [d134, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d134, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5206 p hg
    simpa only [d134, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5208 (p : Pattern) (guard : d857 p = 1) : d389 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d389, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d857, d389, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d389, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3066 p hg
    simpa only [d857, d389, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5209 (p : Pattern) (guard : d857 p = 1) : d390 p ≤ (0 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d390, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d857, d390, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d390, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3654 p hg
    simpa only [d857, d390, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5210 (p : Pattern) (guard : d857 p = 1) : d391 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d391, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5208 p hg
    simpa only [d391, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d391, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5209 p hg
    simpa only [d391, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5211 (p : Pattern) (guard : d857 p = 1) : d392 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d392, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5208 p hg
    simpa only [d392, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d392, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d392, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5212 (p : Pattern) (guard : d857 p = 1) : d393 p ≤ (0 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d393, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d857, d393, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d393, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d857, d393, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5213 (p : Pattern) (guard : d857 p = 1) : d394 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d394, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5208 p hg
    simpa only [d394, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d394, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d394, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5214 (p : Pattern) (guard : d857 p = 1) : d395 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d395, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d857, d395, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d395, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3068 p hg
    simpa only [d857, d395, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5215 (p : Pattern) (guard : d857 p = 1) : d396 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d396, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5214 p hg
    simpa only [d396, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d396, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5209 p hg
    simpa only [d396, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5216 (p : Pattern) (guard : d857 p = 1) : d397 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d397, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5213 p hg
    simpa only [d397, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d397, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5215 p hg
    simpa only [d397, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5217 (p : Pattern) (guard : d857 p = 1) : d398 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d398, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5211 p hg
    simpa only [d398, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d398, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5216 p hg
    simpa only [d398, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5218 (p : Pattern) (guard : d0 p = 1) : d408 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5219 (p : Pattern) (guard : d1072 p = 1) : d409 p ≤ (0 : Int) + d184 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d409, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d1072, d409, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d409, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5218 p hg
    simpa only [d1072, d409, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5220 (p : Pattern) (guard : d857 p = 1) : d410 p ≤ (0 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d410, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1450 p hg
    simpa only [d857, d410, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d410, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d857, d410, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5221 (p : Pattern) (guard : d857 p = 1) : d411 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d411, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1453 p hg
    simpa only [d857, d411, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d411, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d857, d411, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5222 (p : Pattern) (guard : d857 p = 1) : d412 p ≤ (0 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d412, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5220 p hg
    simpa only [d412, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d412, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5221 p hg
    simpa only [d412, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5223 (p : Pattern) (guard : d857 p = 1) : d413 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d413, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d413, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d413, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5222 p hg
    simpa only [d413, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5224 (p : Pattern) (guard : d857 p = 1) : d414 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d414, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5211 p hg
    simpa only [d414, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d414, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5223 p hg
    simpa only [d414, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5225 (p : Pattern) (guard : d857 p = 1) : d415 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d415, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d415, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d415, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d415, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5226 (p : Pattern) (guard : d857 p = 1) : d416 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d416, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5211 p hg
    simpa only [d416, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d416, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5225 p hg
    simpa only [d416, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5227 (p : Pattern) (guard : d857 p = 1) : d417 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d417, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5224 p hg
    simpa only [d417, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d417, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d417, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5228 (p : Pattern) (guard : d0 p = 1) : d419 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5229 (p : Pattern) (guard : d1072 p = 1) : d420 p ≤ (0 : Int) + d185 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d420, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d1072, d420, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d420, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5228 p hg
    simpa only [d1072, d420, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5230 (p : Pattern) (guard : d1072 p = 1) : d421 p ≤ (0 : Int) + d186 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d421, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5219 p hg
    simpa only [d421, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d421, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5229 p hg
    simpa only [d421, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5231 (p : Pattern) (guard : d857 p = 1) : d389 p ≤ (0 : Int) + d187 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d389, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d857, d389, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d389, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d857, d389, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5232 (p : Pattern) (guard : d857 p = 1) : d390 p ≤ (0 : Int) + d188 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d390, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d857, d390, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d390, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d857, d390, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5233 (p : Pattern) (guard : d857 p = 1) : d391 p ≤ (0 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d391, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5231 p hg
    simpa only [d391, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d391, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5232 p hg
    simpa only [d391, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5234 (p : Pattern) (guard : d857 p = 1) : d392 p ≤ (0 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d392, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5231 p hg
    simpa only [d392, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d392, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5233 p hg
    simpa only [d392, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5235 (p : Pattern) (guard : d857 p = 1) : d393 p ≤ (0 : Int) + d191 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d393, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d857, d393, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d393, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d857, d393, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5236 (p : Pattern) (guard : d857 p = 1) : d394 p ≤ (0 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d394, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5231 p hg
    simpa only [d394, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d394, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5235 p hg
    simpa only [d394, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5237 (p : Pattern) (guard : d857 p = 1) : d395 p ≤ (0 : Int) + d193 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d395, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d857, d395, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d395, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d857, d395, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5238 (p : Pattern) (guard : d857 p = 1) : d396 p ≤ (0 : Int) + d194 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d396, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5237 p hg
    simpa only [d396, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d396, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5232 p hg
    simpa only [d396, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5239 (p : Pattern) (guard : d857 p = 1) : d397 p ≤ (0 : Int) + d195 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d397, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5236 p hg
    simpa only [d397, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d397, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5238 p hg
    simpa only [d397, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5240 (p : Pattern) (guard : d857 p = 1) : d398 p ≤ (0 : Int) + d196 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d398, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5234 p hg
    simpa only [d398, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d398, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5239 p hg
    simpa only [d398, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5241 (p : Pattern) (guard : d857 p = 1) : d398 p ≤ (0 : Int) + d197 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5240 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5242 (p : Pattern) (guard : d0 p = 1) : d426 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5243 (p : Pattern) (guard : d1072 p = 1) : d427 p ≤ (0 : Int) + d198 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d427, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5241 p hg
    simpa only [d1072, d427, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d427, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5242 p hg
    simpa only [d1072, d427, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5244 (p : Pattern) (guard : d857 p = 1) : d415 p ≤ (0 : Int) + d202 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d415, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5233 p hg
    simpa only [d415, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d415, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1481 p hg
    simpa only [d415, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5245 (p : Pattern) (guard : d857 p = 1) : d416 p ≤ (0 : Int) + d203 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d416, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5234 p hg
    simpa only [d416, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d416, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5244 p hg
    simpa only [d416, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5246 (p : Pattern) (guard : d857 p = 1) : d416 p ≤ (0 : Int) + d204 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5245 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5247 (p : Pattern) (guard : d0 p = 1) : d435 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5248 (p : Pattern) (guard : d1072 p = 1) : d436 p ≤ (0 : Int) + d205 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d436, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5246 p hg
    simpa only [d1072, d436, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d436, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5247 p hg
    simpa only [d1072, d436, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5249 (p : Pattern) (guard : d1072 p = 1) : d437 p ≤ (0 : Int) + d206 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d437, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5243 p hg
    simpa only [d437, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d437, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5248 p hg
    simpa only [d437, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5250 (p : Pattern) (guard : d1072 p = 1) : d438 p ≤ (0 : Int) + d207 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d438, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5230 p hg
    simpa only [d438, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d438, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5249 p hg
    simpa only [d438, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5251 (p : Pattern) (guard : d0 p = 1) : d408 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5252 (p : Pattern) (guard : d1072 p = 1) : d409 p ≤ (0 : Int) + d208 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d409, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d1072, d409, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d409, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5251 p hg
    simpa only [d1072, d409, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5253 (p : Pattern) (guard : d0 p = 1) : d419 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5254 (p : Pattern) (guard : d1072 p = 1) : d439 p ≤ (0 : Int) + d209 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d439, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d1072, d439, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d439, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5253 p hg
    simpa only [d1072, d439, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5255 (p : Pattern) (guard : d1072 p = 1) : d440 p ≤ (0 : Int) + d210 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d440, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5252 p hg
    simpa only [d440, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d440, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5254 p hg
    simpa only [d440, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5256 (p : Pattern) (guard : d857 p = 1) : d441 p ≤ (0 : Int) + d211 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d441, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d857, d441, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d441, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d857, d441, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5257 (p : Pattern) (guard : d857 p = 1) : d442 p ≤ (0 : Int) + d212 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d442, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5231 p hg
    simpa only [d442, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d442, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5256 p hg
    simpa only [d442, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5258 (p : Pattern) (guard : d857 p = 1) : d443 p ≤ (0 : Int) + d213 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d443, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5257 p hg
    simpa only [d443, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d443, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5238 p hg
    simpa only [d443, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5259 (p : Pattern) (guard : d857 p = 1) : d444 p ≤ (0 : Int) + d214 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d444, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5234 p hg
    simpa only [d444, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d444, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5258 p hg
    simpa only [d444, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5260 (p : Pattern) (guard : d857 p = 1) : d445 p ≤ (0 : Int) + d215 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d445, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d445, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d445, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5259 p hg
    simpa only [d445, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5261 (p : Pattern) (guard : d0 p = 1) : d448 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5262 (p : Pattern) (guard : d1072 p = 1) : d449 p ≤ (0 : Int) + d216 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d449, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5260 p hg
    simpa only [d1072, d449, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d449, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5261 p hg
    simpa only [d1072, d449, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5263 (p : Pattern) (guard : d857 p = 1) : d399 p ≤ (0 : Int) + d217 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d399, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d857, d399, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d399, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d857, d399, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5264 (p : Pattern) (guard : d857 p = 1) : d400 p ≤ (0 : Int) + d218 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d400, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d857, d400, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d400, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d857, d400, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5265 (p : Pattern) (guard : d857 p = 1) : d401 p ≤ (0 : Int) + d219 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d401, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5263 p hg
    simpa only [d401, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d401, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5264 p hg
    simpa only [d401, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5266 (p : Pattern) (guard : d857 p = 1) : d402 p ≤ (0 : Int) + d220 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d402, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5263 p hg
    simpa only [d402, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d402, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5265 p hg
    simpa only [d402, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5267 (p : Pattern) (guard : d857 p = 1) : d418 p ≤ (0 : Int) + d221 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d418, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5265 p hg
    simpa only [d418, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d418, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1481 p hg
    simpa only [d418, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5268 (p : Pattern) (guard : d857 p = 1) : d419 p ≤ (0 : Int) + d222 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d419, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5266 p hg
    simpa only [d419, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d419, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5267 p hg
    simpa only [d419, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5269 (p : Pattern) (guard : d857 p = 1) : d450 p ≤ (0 : Int) + d223 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d450, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d450, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d450, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5268 p hg
    simpa only [d450, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5270 (p : Pattern) (guard : d0 p = 1) : d451 p ≤ (0 : Int) + d169 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5271 (p : Pattern) (guard : d1072 p = 1) : d452 p ≤ (0 : Int) + d224 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d452, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5269 p hg
    simpa only [d1072, d452, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d452, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5270 p hg
    simpa only [d1072, d452, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5272 (p : Pattern) (guard : d1072 p = 1) : d453 p ≤ (0 : Int) + d225 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d453, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5262 p hg
    simpa only [d453, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d453, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5271 p hg
    simpa only [d453, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5273 (p : Pattern) (guard : d1072 p = 1) : d454 p ≤ (0 : Int) + d226 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d454, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5255 p hg
    simpa only [d454, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d454, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5272 p hg
    simpa only [d454, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5274 (p : Pattern) (guard : d1072 p = 1) : d455 p ≤ (0 : Int) + d227 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d455, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d455, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d455, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5273 p hg
    simpa only [d455, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5275 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (2 : Int) + d197 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5276 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d3 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4308 p hg
    simpa only [d9, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d9, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5277 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d4 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4308 p hg
    simpa only [d10, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5276 p hg
    simpa only [d10, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5278 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4308 p hg
    simpa only [d11, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d11, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5279 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5277 p hg
    simpa only [d12, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5278 p hg
    simpa only [d12, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5280 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5277 p hg
    simpa only [d13, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d13, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5281 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5279 p hg
    simpa only [d14, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5280 p hg
    simpa only [d14, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5282 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (2 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4602 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5281 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5283 (p : Pattern) (guard : d857 p = 1) : d399 p ≤ (2 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d399, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d857, d399, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d399, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3904 p hg
    simpa only [d857, d399, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5284 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (2 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5276 p hg
    simpa only [d21, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d21, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5285 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (2 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5277 p hg
    simpa only [d22, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5284 p hg
    simpa only [d22, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5286 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5284 p hg
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5287 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5285 p hg
    simpa only [d24, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5286 p hg
    simpa only [d24, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5288 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (2 : Int) + d20 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4610 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5287 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5289 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5290 (p : Pattern) (guard : d857 p = 1) : d400 p ≤ (2 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d400, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5288 p hg
    simpa only [d857, d400, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d400, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5289 p hg
    simpa only [d857, d400, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5291 (p : Pattern) (guard : d857 p = 1) : d401 p ≤ (2 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d401, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5283 p hg
    simpa only [d401, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d401, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d401, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5292 (p : Pattern) (guard : d857 p = 1) : d402 p ≤ (2 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d402, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5283 p hg
    simpa only [d402, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d402, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5291 p hg
    simpa only [d402, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5293 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4308 p hg
    simpa only [d9, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4317 p hg
    simpa only [d9, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5294 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (2 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5293 p hg
    simpa only [d21, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d21, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5295 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (2 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5277 p hg
    simpa only [d22, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5294 p hg
    simpa only [d22, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5296 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d32 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5294 p hg
    simpa only [d23, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d23, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5297 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d33 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5295 p hg
    simpa only [d24, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5296 p hg
    simpa only [d24, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5298 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d33 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5297 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5299 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5300 (p : Pattern) (guard : d857 p = 1) : d403 p ≤ (2 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d403, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5298 p hg
    simpa only [d857, d403, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d403, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5299 p hg
    simpa only [d857, d403, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5301 (p : Pattern) (guard : d857 p = 1) : d404 p ≤ (2 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d404, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5283 p hg
    simpa only [d404, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d404, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5300 p hg
    simpa only [d404, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5302 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (2 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5278 p hg
    simpa only [d39, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d39, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5303 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5279 p hg
    simpa only [d40, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5302 p hg
    simpa only [d40, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5304 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (2 : Int) + d38 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5305 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5306 (p : Pattern) (guard : d857 p = 1) : d405 p ≤ (2 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d405, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5304 p hg
    simpa only [d857, d405, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d405, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5305 p hg
    simpa only [d857, d405, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5307 (p : Pattern) (guard : d857 p = 1) : d406 p ≤ (2 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d406, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5306 p hg
    simpa only [d406, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d406, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d406, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5308 (p : Pattern) (guard : d857 p = 1) : d407 p ≤ (2 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d407, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5301 p hg
    simpa only [d407, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d407, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5307 p hg
    simpa only [d407, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5309 (p : Pattern) (guard : d857 p = 1) : d408 p ≤ (2 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d408, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5292 p hg
    simpa only [d408, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d408, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5308 p hg
    simpa only [d408, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5310 (p : Pattern) (guard : d857 p = 1) : d399 p ≤ (2 : Int) + d187 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d399, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d857, d399, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d399, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3953 p hg
    simpa only [d857, d399, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5311 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5312 (p : Pattern) (guard : d857 p = 1) : d400 p ≤ (2 : Int) + d188 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d400, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5288 p hg
    simpa only [d857, d400, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d400, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5311 p hg
    simpa only [d857, d400, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5313 (p : Pattern) (guard : d857 p = 1) : d401 p ≤ (2 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d401, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5310 p hg
    simpa only [d401, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d401, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5312 p hg
    simpa only [d401, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5314 (p : Pattern) (guard : d857 p = 1) : d402 p ≤ (2 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d402, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5310 p hg
    simpa only [d402, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d402, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d402, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5315 (p : Pattern) (guard : d857 p = 1) : d403 p ≤ (2 : Int) + d191 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d403, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5298 p hg
    simpa only [d857, d403, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d403, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5311 p hg
    simpa only [d857, d403, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5316 (p : Pattern) (guard : d857 p = 1) : d404 p ≤ (2 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d404, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5310 p hg
    simpa only [d404, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d404, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5315 p hg
    simpa only [d404, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5317 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5318 (p : Pattern) (guard : d857 p = 1) : d405 p ≤ (2 : Int) + d193 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d405, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5304 p hg
    simpa only [d857, d405, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d405, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5317 p hg
    simpa only [d857, d405, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5319 (p : Pattern) (guard : d857 p = 1) : d406 p ≤ (2 : Int) + d194 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d406, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5318 p hg
    simpa only [d406, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d406, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5312 p hg
    simpa only [d406, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
