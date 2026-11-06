/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare140 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (1 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare121 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare139 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare141 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (1 : Int) + d47 p := by
  omega
theorem compare142 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (1 : Int) + d15 p := by
  omega
theorem compare143 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (1 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare142 p hg
    simpa only [d48, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare110 p hg
    simpa only [d48, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare144 (p : Pattern) (guard : d1 p = 1) : d49 p ≤ (1 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d49, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d49, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d49, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d49, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare145 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (1 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare143 p hg
    simpa only [d50, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare144 p hg
    simpa only [d50, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare146 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (1 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare141 p hg
    simpa only [d51, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare145 p hg
    simpa only [d51, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare147 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (1 : Int) + d57 p := by
  omega
theorem compare148 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d53 p := by
  omega
theorem compare149 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (1 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42 p hg
    simpa only [d58, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d58, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare150 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (1 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare110 p hg
    simpa only [d59, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare149 p hg
    simpa only [d59, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare151 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (1 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare148 p hg
    simpa only [d60, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare150 p hg
    simpa only [d60, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare152 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (1 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare114 p hg
    simpa only [d61, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d61, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare153 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (1 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare152 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare154 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (1 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d54, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d54, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare155 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (1 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare154 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare156 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (1 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare153 p hg
    simpa only [d63, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare155 p hg
    simpa only [d63, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare157 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (1 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare151 p hg
    simpa only [d64, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare156 p hg
    simpa only [d64, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare158 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (1 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare147 p hg
    simpa only [d65, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare157 p hg
    simpa only [d65, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare159 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (1 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare146 p hg
    simpa only [d66, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare158 p hg
    simpa only [d66, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare160 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (1 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare140 p hg
    simpa only [d67, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare159 p hg
    simpa only [d67, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare161 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (1 : Int) + d84 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare162 (p : Pattern) (guard : d829 p = 1) : d118 p ≤ (1 : Int) + d84 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare160 p hg
    simpa only [d829, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare161 p hg
    simpa only [d829, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare163 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (1 : Int) + d20 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare164 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (1 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare163 p hg
    simpa only [d120, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare149 p hg
    simpa only [d120, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare165 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (1 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d121, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare164 p hg
    simpa only [d121, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare166 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (1 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare129 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare152 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare167 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (1 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare135 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare154 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare168 (p : Pattern) (guard : d1 p = 1) : d93 p ≤ (1 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d93, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare166 p hg
    simpa only [d93, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d93, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare167 p hg
    simpa only [d93, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare169 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (1 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare165 p hg
    simpa only [d122, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare168 p hg
    simpa only [d122, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare170 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (1 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33 p hg
    simpa only [d123, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare169 p hg
    simpa only [d123, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare171 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (1 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare139 p hg
    simpa only [d124, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare170 p hg
    simpa only [d124, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare172 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (1 : Int) + d100 p := by
  omega
theorem compare173 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (1 : Int) + d99 p := by
  omega
theorem compare174 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare175 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (1 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare174 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare176 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (1 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare92 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare177 (p : Pattern) (guard : d1 p = 1) : d72 p ≤ (1 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare175 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare176 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare178 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (1 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d101, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare173 p hg
    simpa only [d101, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d101, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare177 p hg
    simpa only [d101, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare179 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (1 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare172 p hg
    simpa only [d102, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare178 p hg
    simpa only [d102, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare180 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (1 : Int) + d110 p := by
  omega
theorem compare181 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d109 p := by
  omega
theorem compare182 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (1 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare174 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare92 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare183 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (1 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare181 p hg
    simpa only [d125, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare182 p hg
    simpa only [d125, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare184 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (1 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare180 p hg
    simpa only [d126, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare183 p hg
    simpa only [d126, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare185 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (1 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare179 p hg
    simpa only [d127, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare184 p hg
    simpa only [d127, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare186 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (1 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare171 p hg
    simpa only [d128, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare185 p hg
    simpa only [d128, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare187 (p : Pattern) (guard : d0 p = 1) : d131 p ≤ (1 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare188 (p : Pattern) (guard : d829 p = 1) : d132 p ≤ (1 : Int) + d114 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare186 p hg
    simpa only [d829, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare187 p hg
    simpa only [d829, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare189 (p : Pattern) (guard : d829 p = 1) : d133 p ≤ (1 : Int) + d831 p := by
  cases selected : p 86 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d133, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare162 p hg
    simpa only [d133, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d133, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare188 p hg
    simpa only [d133, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare190 (p : Pattern) (guard : d830 p = 1) : d134 p ≤ (1 : Int) + d831 p := by
  cases selected : p 80 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d830, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare189 p hg
    simpa only [d830, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare191 (p : Pattern) (guard : d1 p = 1) : d85 p ≤ (0 : Int) + d85 p := by
  omega
theorem compare192 (p : Pattern) (guard : d0 p = 1) : d115 p ≤ (0 : Int) + d166 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare193 (p : Pattern) (guard : d833 p = 1) : d116 p ≤ (0 : Int) + d174 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d833, d116, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare191 p hg
    simpa only [d833, d116, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d833, d116, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare192 p hg
    simpa only [d833, d116, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare194 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (0 : Int) + d118 p := by
  omega
theorem compare195 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d171 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare196 (p : Pattern) (guard : d833 p = 1) : d133 p ≤ (0 : Int) + d175 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d833, d133, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare194 p hg
    simpa only [d833, d133, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d833, d133, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare195 p hg
    simpa only [d833, d133, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare197 (p : Pattern) (guard : d833 p = 1) : d134 p ≤ (0 : Int) + d176 p := by
  cases selected : p 80 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d134, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare193 p hg
    simpa only [d134, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d833 p = 1 := by simpa only [d134, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare196 p hg
    simpa only [d134, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare198 (p : Pattern) (guard : d0 p = 1) : d85 p ≤ (0 : Int) + d837 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare199 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d8 p := by
  omega
theorem compare200 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) ≤ (0 : Int) + 1
  decide
theorem compare201 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare202 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare203 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare202 p hg
    simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare204 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare205 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare204 p hg
    simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare206 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare207 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare205 p hg
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare206 p hg
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare208 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare207 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare209 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d15 p := by
  omega
theorem compare210 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d15 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare211 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d20 p := by
  omega
theorem compare212 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare202 p hg
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare213 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare212 p hg
    simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare214 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare212 p hg
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare215 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare213 p hg
    simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare214 p hg
    simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare216 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare217 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (0 : Int) + d25 p := by
  omega
theorem compare218 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (0 : Int) + d25 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare216 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare219 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare210 p hg
    simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d27, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare220 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare210 p hg
    simpa only [d28, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare219 p hg
    simpa only [d28, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare221 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d33 p := by
  omega
theorem compare222 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d2 p := by
  change (1 : Int) ≤ (0 : Int) + 2
  decide
theorem compare223 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare224 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare225 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare224 p hg
    simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare226 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare224 p hg
    simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare227 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare225 p hg
    simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare226 p hg
    simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare228 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare227 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare229 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (0 : Int) + d34 p := by
  omega
theorem compare230 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d34 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare229 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare231 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare210 p hg
    simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare230 p hg
    simpa only [d36, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare232 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (0 : Int) + d38 p := by
  omega
theorem compare233 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare204 p hg
    simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare234 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (0 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare205 p hg
    simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare233 p hg
    simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare235 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (0 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare234 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare236 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (0 : Int) + d41 p := by
  omega
theorem compare237 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (0 : Int) + d41 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare235 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare238 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d43, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d43, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare239 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare231 p hg
    simpa only [d44, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare238 p hg
    simpa only [d44, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare240 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare220 p hg
    simpa only [d45, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare239 p hg
    simpa only [d45, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare241 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (0 : Int) + d52 p := by
  omega
theorem compare242 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d86, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare241 p hg
    simpa only [d86, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare243 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d54 p := by
  omega
theorem compare244 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare216 p hg
    simpa only [d87, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare243 p hg
    simpa only [d87, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare245 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare242 p hg
    simpa only [d88, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare244 p hg
    simpa only [d88, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare246 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare242 p hg
    simpa only [d89, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare245 p hg
    simpa only [d89, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare247 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (0 : Int) + d58 p := by
  omega
theorem compare248 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (0 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d90, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare247 p hg
    simpa only [d90, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare249 (p : Pattern) (guard : d1 p = 1) : d91 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare242 p hg
    simpa only [d91, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare248 p hg
    simpa only [d91, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare250 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d61 p := by
  omega
theorem compare251 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (0 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d92, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare235 p hg
    simpa only [d92, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d92, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare250 p hg
    simpa only [d92, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare252 (p : Pattern) (guard : d1 p = 1) : d93 p ≤ (0 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d93, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare251 p hg
    simpa only [d93, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d93, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare244 p hg
    simpa only [d93, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare253 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d94, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare249 p hg
    simpa only [d94, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d94, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare252 p hg
    simpa only [d94, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare254 (p : Pattern) (guard : d1 p = 1) : d95 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d95, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare246 p hg
    simpa only [d95, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d95, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare253 p hg
    simpa only [d95, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare255 (p : Pattern) (guard : d1 p = 1) : d96 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d96, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare240 p hg
    simpa only [d96, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d96, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare254 p hg
    simpa only [d96, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare256 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare257 (p : Pattern) (guard : d835 p = 1) : d103 p ≤ (0 : Int) + d66 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare255 p hg
    simpa only [d835, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare256 p hg
    simpa only [d835, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare258 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (0 : Int) + d75 p := by
  omega
theorem compare259 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare219 p hg
    simpa only [d76, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare258 p hg
    simpa only [d76, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare260 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare220 p hg
    simpa only [d77, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare259 p hg
    simpa only [d77, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare261 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare245 p hg
    simpa only [d104, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare258 p hg
    simpa only [d104, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare262 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare246 p hg
    simpa only [d105, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare261 p hg
    simpa only [d105, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare263 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare260 p hg
    simpa only [d106, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare262 p hg
    simpa only [d106, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare264 (p : Pattern) (guard : d0 p = 1) : d113 p ≤ (0 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare265 (p : Pattern) (guard : d835 p = 1) : d114 p ≤ (0 : Int) + d83 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare263 p hg
    simpa only [d835, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare264 p hg
    simpa only [d835, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare266 (p : Pattern) (guard : d835 p = 1) : d115 p ≤ (0 : Int) + d837 p := by
  cases selected : p 106 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d115, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare257 p hg
    simpa only [d115, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d115, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare265 p hg
    simpa only [d115, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare267 (p : Pattern) (guard : d836 p = 1) : d116 p ≤ (0 : Int) + d837 p := by
  cases selected : p 86 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare198 p hg
    simpa only [d836, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare266 p hg
    simpa only [d836, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare268 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (0 : Int) + d837 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare269 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (0 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d119, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d119, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare270 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare269 p hg
    simpa only [d120, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare247 p hg
    simpa only [d120, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare271 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare242 p hg
    simpa only [d121, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare270 p hg
    simpa only [d121, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare272 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare271 p hg
    simpa only [d122, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare252 p hg
    simpa only [d122, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare273 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare246 p hg
    simpa only [d123, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d123, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare274 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare240 p hg
    simpa only [d124, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare273 p hg
    simpa only [d124, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare275 (p : Pattern) (guard : d0 p = 1) : d127 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare276 (p : Pattern) (guard : d835 p = 1) : d128 p ≤ (0 : Int) + d66 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare274 p hg
    simpa only [d835, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare275 p hg
    simpa only [d835, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare277 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (0 : Int) + d82 p := by
  omega
theorem compare278 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare260 p hg
    simpa only [d129, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare277 p hg
    simpa only [d129, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare279 (p : Pattern) (guard : d0 p = 1) : d130 p ≤ (0 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban32Refined
