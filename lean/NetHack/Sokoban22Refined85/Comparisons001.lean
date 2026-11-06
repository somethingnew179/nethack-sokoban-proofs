/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare140 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (1 : Int) + d155 p := by
  omega
theorem compare141 (p : Pattern) (guard : d1 p = 1) : d156 p ≤ (1 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d156, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare129 p hg
    simpa only [d156, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d156, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare140 p hg
    simpa only [d156, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare142 (p : Pattern) (guard : d1 p = 1) : d157 p ≤ (1 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d157, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare139 p hg
    simpa only [d157, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d157, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare141 p hg
    simpa only [d157, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare143 (p : Pattern) (guard : d1 p = 1) : d158 p ≤ (1 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d158, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare138 p hg
    simpa only [d158, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d158, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare142 p hg
    simpa only [d158, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare144 (p : Pattern) (guard : d1 p = 1) : d162 p ≤ (1 : Int) + d162 p := by
  omega
theorem compare145 (p : Pattern) (guard : d1 p = 1) : d163 p ≤ (1 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d163, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare142 p hg
    simpa only [d163, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d163, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare144 p hg
    simpa only [d163, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare146 (p : Pattern) (guard : d1 p = 1) : d164 p ≤ (1 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d164, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare143 p hg
    simpa only [d164, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d164, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare145 p hg
    simpa only [d164, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare147 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (1 : Int) + d114 p := by
  omega
theorem compare148 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (1 : Int) + d3 p := by
  change (1 : Int) ≤ (1 : Int) + 3
  decide
theorem compare149 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (1 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare148 p hg
    simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare150 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (1 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare148 p hg
    simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare149 p hg
    simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare151 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (1 : Int) + d117 p := by
  omega
theorem compare152 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (1 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare150 p hg
    simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare151 p hg
    simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare153 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (1 : Int) + d121 p := by
  omega
theorem compare154 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (1 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare150 p hg
    simpa only [d122, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare153 p hg
    simpa only [d122, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare155 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (1 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare152 p hg
    simpa only [d123, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare154 p hg
    simpa only [d123, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare156 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (1 : Int) + d5 p := by
  change (1 : Int) ≤ (1 : Int) + 5
  decide
theorem compare157 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (1 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare156 p hg
    simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare158 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (1 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare156 p hg
    simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare157 p hg
    simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare159 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (1 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare158 p hg
    simpa only [d124, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d124, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare160 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (1 : Int) + d12 p := by
  change (5 : Int) ≤ (1 : Int) + 12
  decide
theorem compare161 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare160 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare162 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare160 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare161 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare163 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare162 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare164 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (1 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare159 p hg
    simpa only [d126, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare163 p hg
    simpa only [d126, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare165 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (1 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare155 p hg
    simpa only [d127, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare164 p hg
    simpa only [d127, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare166 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (1 : Int) + d7 p := by
  change (1 : Int) ≤ (1 : Int) + 7
  decide
theorem compare167 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (1 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare166 p hg
    simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare168 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (1 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare166 p hg
    simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare167 p hg
    simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare169 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (1 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare168 p hg
    simpa only [d124, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d124, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare170 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (1 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare169 p hg
    simpa only [d126, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare163 p hg
    simpa only [d126, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare171 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare172 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (1 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare170 p hg
    simpa only [d129, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare171 p hg
    simpa only [d129, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare173 (p : Pattern) (guard : d1 p = 1) : d130 p ≤ (1 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d130, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare165 p hg
    simpa only [d130, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d130, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare172 p hg
    simpa only [d130, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare174 (p : Pattern) (guard : d1 p = 1) : d131 p ≤ (1 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d131, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare147 p hg
    simpa only [d131, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d131, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare173 p hg
    simpa only [d131, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare175 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (1 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare158 p hg
    simpa only [d122, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare153 p hg
    simpa only [d122, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare176 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (1 : Int) + d5 p := by
  change (3 : Int) ≤ (1 : Int) + 5
  decide
theorem compare177 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (1 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare176 p hg
    simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare178 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (1 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare176 p hg
    simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare177 p hg
    simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare179 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (1 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare178 p hg
    simpa only [d139, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d139, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare180 (p : Pattern) (guard : d1 p = 1) : d140 p ≤ (1 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d140, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare175 p hg
    simpa only [d140, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d140, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare179 p hg
    simpa only [d140, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare181 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (1 : Int) + d7 p := by
  change (5 : Int) ≤ (1 : Int) + 7
  decide
theorem compare182 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (1 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare181 p hg
    simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare183 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (1 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare181 p hg
    simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare182 p hg
    simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare184 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (1 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare183 p hg
    simpa only [d125, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d125, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare185 (p : Pattern) (guard : d1 p = 1) : d141 p ≤ (1 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d141, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare184 p hg
    simpa only [d141, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d141, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d141, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare186 (p : Pattern) (guard : d1 p = 1) : d142 p ≤ (1 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d142, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare180 p hg
    simpa only [d142, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d142, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare185 p hg
    simpa only [d142, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare187 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (1 : Int) + d9 p := by
  change (5 : Int) ≤ (1 : Int) + 9
  decide
theorem compare188 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (1 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare187 p hg
    simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare189 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (1 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare187 p hg
    simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare188 p hg
    simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare190 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (1 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare189 p hg
    simpa only [d125, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d125, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare191 (p : Pattern) (guard : d1 p = 1) : d143 p ≤ (1 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare190 p hg
    simpa only [d143, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d143, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare192 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (1 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d144, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare191 p hg
    simpa only [d144, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d144, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d144, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare193 (p : Pattern) (guard : d1 p = 1) : d145 p ≤ (1 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d145, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare186 p hg
    simpa only [d145, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d145, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare192 p hg
    simpa only [d145, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare194 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (1 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare129 p hg
    simpa only [d146, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare193 p hg
    simpa only [d146, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare195 (p : Pattern) (guard : d1 p = 1) : d147 p ≤ (1 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d147, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare174 p hg
    simpa only [d147, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d147, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare194 p hg
    simpa only [d147, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare196 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (1 : Int) + d105 p := by
  omega
theorem compare197 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (1 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare150 p hg
    simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare198 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (1 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare150 p hg
    simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare197 p hg
    simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare199 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (1 : Int) + d11 p := by
  change (5 : Int) ≤ (1 : Int) + 11
  decide
theorem compare200 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (1 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare201 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (1 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d107, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d107, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare202 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (1 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d108, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d108, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare203 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d109, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare202 p hg
    simpa only [d109, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare204 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (1 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare198 p hg
    simpa only [d110, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d110, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare205 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (1 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare196 p hg
    simpa only [d111, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare204 p hg
    simpa only [d111, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare206 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (1 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare158 p hg
    simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare207 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (1 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare158 p hg
    simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare206 p hg
    simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare208 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (1 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare207 p hg
    simpa only [d110, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d110, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare209 (p : Pattern) (guard : d1 p = 1) : d112 p ≤ (1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare210 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (1 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d113, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d113, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare211 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (1 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare205 p hg
    simpa only [d114, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare210 p hg
    simpa only [d114, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare212 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (1 : Int) + d7 p := by
  change (3 : Int) ≤ (1 : Int) + 7
  decide
theorem compare213 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (1 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare212 p hg
    simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare214 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (1 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare212 p hg
    simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare213 p hg
    simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare215 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (1 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare214 p hg
    simpa only [d117, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d117, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare216 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (1 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare214 p hg
    simpa only [d132, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d132, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare217 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (1 : Int) + d12 p := by
  change (7 : Int) ≤ (1 : Int) + 12
  decide
theorem compare218 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare219 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare220 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare219 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare221 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare219 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare220 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare222 (p : Pattern) (guard : d1 p = 1) : d149 p ≤ (1 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d149, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare216 p hg
    simpa only [d149, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d149, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d149, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare223 (p : Pattern) (guard : d1 p = 1) : d150 p ≤ (1 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d150, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d150, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d150, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d150, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare224 (p : Pattern) (guard : d1 p = 1) : d151 p ≤ (1 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d151, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d151, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d151, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d151, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare225 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (1 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d152, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d152, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d152, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare224 p hg
    simpa only [d152, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare226 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (1 : Int) + d132 p := by
  omega
theorem compare227 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (1 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare198 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare226 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare228 (p : Pattern) (guard : d1 p = 1) : d135 p ≤ (1 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d135, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare227 p hg
    simpa only [d135, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d135, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare125 p hg
    simpa only [d135, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare229 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (1 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare183 p hg
    simpa only [d108, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d108, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare230 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare183 p hg
    simpa only [d109, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare229 p hg
    simpa only [d109, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare231 (p : Pattern) (guard : d1 p = 1) : d136 p ≤ (1 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d136, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare230 p hg
    simpa only [d136, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d136, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare97 p hg
    simpa only [d136, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare232 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (1 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare231 p hg
    simpa only [d137, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d137, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare233 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (1 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d138, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d138, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare234 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (1 : Int) + d9 p := by
  change (7 : Int) ≤ (1 : Int) + 9
  decide
theorem compare235 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (1 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare234 p hg
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare236 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (1 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare234 p hg
    simpa only [d120, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare235 p hg
    simpa only [d120, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare237 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (1 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d121, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d121, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare238 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (1 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d148, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d148, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare239 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (1 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare238 p hg
    simpa only [d153, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d153, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare240 (p : Pattern) (guard : d1 p = 1) : d154 p ≤ (1 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d154, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare239 p hg
    simpa only [d154, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d154, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d154, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare241 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (1 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare240 p hg
    simpa only [d155, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d155, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare242 (p : Pattern) (guard : d1 p = 1) : d156 p ≤ (1 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d156, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare233 p hg
    simpa only [d156, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d156, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare241 p hg
    simpa only [d156, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare243 (p : Pattern) (guard : d1 p = 1) : d157 p ≤ (1 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d157, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare225 p hg
    simpa only [d157, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d157, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare242 p hg
    simpa only [d157, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare244 (p : Pattern) (guard : d1 p = 1) : d158 p ≤ (1 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d158, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare195 p hg
    simpa only [d158, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d158, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare243 p hg
    simpa only [d158, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare245 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (1 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare189 p hg
    simpa only [d108, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d108, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare246 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare189 p hg
    simpa only [d109, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare245 p hg
    simpa only [d109, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare247 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (1 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare198 p hg
    simpa only [d110, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare246 p hg
    simpa only [d110, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare248 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (1 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare196 p hg
    simpa only [d111, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare247 p hg
    simpa only [d111, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare249 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (1 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare207 p hg
    simpa only [d110, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare246 p hg
    simpa only [d110, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare250 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (1 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare249 p hg
    simpa only [d113, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d113, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare251 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (1 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare248 p hg
    simpa only [d114, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare250 p hg
    simpa only [d114, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare252 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (1 : Int) + d11 p := by
  change (7 : Int) ≤ (1 : Int) + 11
  decide
theorem compare253 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (1 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare252 p hg
    simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare254 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (1 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare252 p hg
    simpa only [d120, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare253 p hg
    simpa only [d120, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare255 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (1 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare254 p hg
    simpa only [d121, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d121, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare256 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (1 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare254 p hg
    simpa only [d148, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare255 p hg
    simpa only [d148, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare257 (p : Pattern) (guard : d1 p = 1) : d149 p ≤ (1 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d149, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare216 p hg
    simpa only [d149, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d149, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare256 p hg
    simpa only [d149, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare258 (p : Pattern) (guard : d1 p = 1) : d150 p ≤ (1 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d150, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare257 p hg
    simpa only [d150, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d150, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d150, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare259 (p : Pattern) (guard : d1 p = 1) : d151 p ≤ (1 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d151, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare258 p hg
    simpa only [d151, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d151, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d151, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare260 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (1 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d152, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare251 p hg
    simpa only [d152, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d152, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare259 p hg
    simpa only [d152, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare261 (p : Pattern) (guard : d1 p = 1) : d157 p ≤ (1 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d157, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare260 p hg
    simpa only [d157, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d157, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare242 p hg
    simpa only [d157, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare262 (p : Pattern) (guard : d1 p = 1) : d165 p ≤ (1 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d165, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare261 p hg
    simpa only [d165, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d165, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d165, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare263 (p : Pattern) (guard : d1 p = 1) : d166 p ≤ (1 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d166, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare244 p hg
    simpa only [d166, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d166, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare262 p hg
    simpa only [d166, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare264 (p : Pattern) (guard : d1 p = 1) : d167 p ≤ (1 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d167, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare146 p hg
    simpa only [d167, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d167, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare263 p hg
    simpa only [d167, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare265 (p : Pattern) (guard : d1 p = 1) : d168 p ≤ (1 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d168, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d168, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d168, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare264 p hg
    simpa only [d168, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare266 (p : Pattern) (guard : d1 p = 1) : d169 p ≤ (1 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d169, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare121 p hg
    simpa only [d169, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d169, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare265 p hg
    simpa only [d169, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare267 (p : Pattern) (guard : d0 p = 1) : d266 p ≤ (1 : Int) + d266 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare268 (p : Pattern) (guard : d4038 p = 1) : d267 p ≤ (1 : Int) + d266 p := by
  cases selected : p 48 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4038, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare266 p hg
    simpa only [d4038, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4038, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare267 p hg
    simpa only [d4038, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare269 (p : Pattern) (guard : d0 p = 1) : d169 p ≤ (1 : Int) + d168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare270 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d1 p := by
  change (0 : Int) ≤ (1 : Int) + 1
  decide
theorem compare271 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (1 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare270 p hg
    simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare272 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare270 p hg
    simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare271 p hg
    simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare273 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (1 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare274 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (1 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare273 p hg
    simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare275 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d5 p := by
  change (4 : Int) ≤ (1 : Int) + 5
  decide
theorem compare276 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (1 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare275 p hg
    simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare277 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare275 p hg
    simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare276 p hg
    simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare278 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (1 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare277 p hg
    simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare279 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare277 p hg
    simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare278 p hg
    simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
