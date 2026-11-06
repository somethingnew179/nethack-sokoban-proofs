/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7000 (p : Pattern) (guard : d1247 p = 1) : d582 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6959 p hg
    simpa only [d1247, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6999 p hg
    simpa only [d1247, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7001 (p : Pattern) (guard : d1171 p = 1) : d583 p ≤ (0 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6960 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6961 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7002 (p : Pattern) (guard : d1171 p = 1) : d584 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7001 p hg
    simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7003 (p : Pattern) (guard : d1171 p = 1) : d585 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7002 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6996 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7004 (p : Pattern) (guard : d0 p = 1) : d586 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7005 (p : Pattern) (guard : d1246 p = 1) : d587 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d587, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7003 p hg
    simpa only [d1246, d587, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d587, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7004 p hg
    simpa only [d1246, d587, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7006 (p : Pattern) (guard : d1247 p = 1) : d588 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d588, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6959 p hg
    simpa only [d1247, d588, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d588, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7005 p hg
    simpa only [d1247, d588, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7007 (p : Pattern) (guard : d1247 p = 1) : d589 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d589, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7000 p hg
    simpa only [d589, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d589, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7006 p hg
    simpa only [d589, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7008 (p : Pattern) (guard : d1171 p = 1) : d557 p ≤ (0 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6995 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7009 (p : Pattern) (guard : d1246 p = 1) : d590 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d590, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7008 p hg
    simpa only [d1246, d590, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d590, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1246, d590, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7010 (p : Pattern) (guard : d1247 p = 1) : d591 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6977 p hg
    simpa only [d1247, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7009 p hg
    simpa only [d1247, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7011 (p : Pattern) (guard : d1171 p = 1) : d564 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d564, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d564, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d564, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d564, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7012 (p : Pattern) (guard : d1171 p = 1) : d565 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d565, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6995 p hg
    simpa only [d565, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d565, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7011 p hg
    simpa only [d565, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7013 (p : Pattern) (guard : d1171 p = 1) : d566 p ≤ (0 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6984 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7012 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7014 (p : Pattern) (guard : d1246 p = 1) : d592 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d592, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7013 p hg
    simpa only [d1246, d592, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d592, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1246, d592, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7015 (p : Pattern) (guard : d1247 p = 1) : d593 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6982 p hg
    simpa only [d1247, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7014 p hg
    simpa only [d1247, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7016 (p : Pattern) (guard : d1247 p = 1) : d594 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d594, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7010 p hg
    simpa only [d594, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d594, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7015 p hg
    simpa only [d594, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7017 (p : Pattern) (guard : d1247 p = 1) : d595 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d595, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7007 p hg
    simpa only [d595, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d595, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7016 p hg
    simpa only [d595, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7018 (p : Pattern) (guard : d1247 p = 1) : d596 p ≤ (0 : Int) + d302 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d596, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6991 p hg
    simpa only [d596, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d596, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7017 p hg
    simpa only [d596, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7019 (p : Pattern) (guard : d0 p = 1) : d601 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7020 (p : Pattern) (guard : d1243 p = 1) : d602 p ≤ (0 : Int) + d303 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d602, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6423 p hg
    simpa only [d1243, d602, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d602, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7019 p hg
    simpa only [d1243, d602, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7021 (p : Pattern) (guard : d1171 p = 1) : d603 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7001 p hg
    simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6983 p hg
    simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7022 (p : Pattern) (guard : d1171 p = 1) : d604 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d604, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6967 p hg
    simpa only [d604, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d604, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6985 p hg
    simpa only [d604, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7023 (p : Pattern) (guard : d1171 p = 1) : d605 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7021 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7022 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7024 (p : Pattern) (guard : d0 p = 1) : d601 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7025 (p : Pattern) (guard : d1246 p = 1) : d606 p ≤ (0 : Int) + d304 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d606, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7023 p hg
    simpa only [d1246, d606, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d606, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7024 p hg
    simpa only [d1246, d606, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7026 (p : Pattern) (guard : d1247 p = 1) : d607 p ≤ (0 : Int) + d305 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d607, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7020 p hg
    simpa only [d1247, d607, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d607, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7025 p hg
    simpa only [d1247, d607, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7027 (p : Pattern) (guard : d1247 p = 1) : d608 p ≤ (0 : Int) + d306 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d608, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6975 p hg
    simpa only [d608, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d608, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7026 p hg
    simpa only [d608, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7028 (p : Pattern) (guard : d0 p = 1) : d580 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7029 (p : Pattern) (guard : d1243 p = 1) : d609 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d609, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6431 p hg
    simpa only [d1243, d609, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d609, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7028 p hg
    simpa only [d1243, d609, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7030 (p : Pattern) (guard : d1171 p = 1) : d576 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6962 p hg
    simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7031 (p : Pattern) (guard : d1171 p = 1) : d577 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6962 p hg
    simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7030 p hg
    simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7032 (p : Pattern) (guard : d1171 p = 1) : d578 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d578, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6970 p hg
    simpa only [d578, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d578, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d578, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7033 (p : Pattern) (guard : d1171 p = 1) : d579 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d579, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6970 p hg
    simpa only [d579, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d579, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7032 p hg
    simpa only [d579, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7034 (p : Pattern) (guard : d1171 p = 1) : d580 p ≤ (0 : Int) + d98 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7031 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7033 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7035 (p : Pattern) (guard : d1246 p = 1) : d580 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7034 p hg
    simpa only [d1246, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7028 p hg
    simpa only [d1246, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7036 (p : Pattern) (guard : d1247 p = 1) : d610 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7029 p hg
    simpa only [d1247, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7035 p hg
    simpa only [d1247, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7037 (p : Pattern) (guard : d1247 p = 1) : d611 p ≤ (0 : Int) + d308 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d611, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7027 p hg
    simpa only [d611, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d611, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7036 p hg
    simpa only [d611, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7038 (p : Pattern) (guard : d1243 p = 1) : d613 p ≤ (0 : Int) + d304 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d613, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6444 p hg
    simpa only [d1243, d613, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d613, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7024 p hg
    simpa only [d1243, d613, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7039 (p : Pattern) (guard : d1171 p = 1) : d598 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6961 p hg
    simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6983 p hg
    simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7040 (p : Pattern) (guard : d1171 p = 1) : d600 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d600, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d600, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d600, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7011 p hg
    simpa only [d600, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7041 (p : Pattern) (guard : d1171 p = 1) : d601 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7040 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7042 (p : Pattern) (guard : d1246 p = 1) : d614 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d614, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7041 p hg
    simpa only [d1246, d614, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d614, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1246, d614, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7043 (p : Pattern) (guard : d1247 p = 1) : d615 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d615, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7038 p hg
    simpa only [d1247, d615, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d615, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7042 p hg
    simpa only [d1247, d615, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7044 (p : Pattern) (guard : d1247 p = 1) : d616 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d616, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7006 p hg
    simpa only [d616, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d616, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7043 p hg
    simpa only [d616, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7045 (p : Pattern) (guard : d1246 p = 1) : d617 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d617, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7034 p hg
    simpa only [d1246, d617, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d617, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1246, d617, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7046 (p : Pattern) (guard : d1247 p = 1) : d618 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7029 p hg
    simpa only [d1247, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7045 p hg
    simpa only [d1247, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7047 (p : Pattern) (guard : d1243 p = 1) : d619 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d619, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d1243, d619, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d619, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1243, d619, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7048 (p : Pattern) (guard : d1171 p = 1) : d586 p ≤ (0 : Int) + d97 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7030 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7032 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7049 (p : Pattern) (guard : d1246 p = 1) : d620 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d620, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7048 p hg
    simpa only [d1246, d620, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d620, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1246, d620, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7050 (p : Pattern) (guard : d1247 p = 1) : d621 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7047 p hg
    simpa only [d1247, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7049 p hg
    simpa only [d1247, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7051 (p : Pattern) (guard : d1247 p = 1) : d622 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d622, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7046 p hg
    simpa only [d622, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d622, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7050 p hg
    simpa only [d622, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7052 (p : Pattern) (guard : d1247 p = 1) : d623 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d623, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7044 p hg
    simpa only [d623, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d623, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7051 p hg
    simpa only [d623, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7053 (p : Pattern) (guard : d1247 p = 1) : d624 p ≤ (0 : Int) + d315 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d624, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7037 p hg
    simpa only [d624, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d624, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7052 p hg
    simpa only [d624, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7054 (p : Pattern) (guard : d1247 p = 1) : d625 p ≤ (0 : Int) + d316 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d625, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7018 p hg
    simpa only [d625, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d625, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7053 p hg
    simpa only [d625, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7055 (p : Pattern) (guard : d1171 p = 1) : d626 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7002 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6972 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7056 (p : Pattern) (guard : d0 p = 1) : d549 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7057 (p : Pattern) (guard : d1246 p = 1) : d627 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d627, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7055 p hg
    simpa only [d1246, d627, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d627, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7056 p hg
    simpa only [d1246, d627, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7058 (p : Pattern) (guard : d1247 p = 1) : d628 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d628, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6959 p hg
    simpa only [d1247, d628, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d628, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7057 p hg
    simpa only [d1247, d628, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7059 (p : Pattern) (guard : d1247 p = 1) : d629 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d629, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6975 p hg
    simpa only [d629, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d629, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7058 p hg
    simpa only [d629, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7060 (p : Pattern) (guard : d1247 p = 1) : d630 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d630, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7059 p hg
    simpa only [d630, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d630, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6990 p hg
    simpa only [d630, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7061 (p : Pattern) (guard : d1243 p = 1) : d632 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d632, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6467 p hg
    simpa only [d1243, d632, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d632, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7056 p hg
    simpa only [d1243, d632, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7062 (p : Pattern) (guard : d1171 p = 1) : d543 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6961 p hg
    simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7063 (p : Pattern) (guard : d1171 p = 1) : d549 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7062 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6996 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7064 (p : Pattern) (guard : d1246 p = 1) : d633 p ≤ (0 : Int) + d317 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d633, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7063 p hg
    simpa only [d1246, d633, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d633, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1246, d633, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7065 (p : Pattern) (guard : d1247 p = 1) : d634 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d634, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7061 p hg
    simpa only [d1247, d634, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d634, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7064 p hg
    simpa only [d1247, d634, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7066 (p : Pattern) (guard : d1247 p = 1) : d635 p ≤ (0 : Int) + d319 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d635, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7006 p hg
    simpa only [d635, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d635, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7065 p hg
    simpa only [d635, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7067 (p : Pattern) (guard : d1247 p = 1) : d636 p ≤ (0 : Int) + d320 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d636, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7066 p hg
    simpa only [d636, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d636, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7016 p hg
    simpa only [d636, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7068 (p : Pattern) (guard : d1247 p = 1) : d637 p ≤ (0 : Int) + d321 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d637, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7060 p hg
    simpa only [d637, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d637, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7067 p hg
    simpa only [d637, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7069 (p : Pattern) (guard : d1171 p = 1) : d638 p ≤ (0 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6967 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7070 (p : Pattern) (guard : d1171 p = 1) : d639 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d639, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7069 p hg
    simpa only [d639, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d639, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6985 p hg
    simpa only [d639, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7071 (p : Pattern) (guard : d1171 p = 1) : d640 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7070 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7072 (p : Pattern) (guard : d0 p = 1) : d601 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7073 (p : Pattern) (guard : d1246 p = 1) : d641 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d641, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7071 p hg
    simpa only [d1246, d641, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d641, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7072 p hg
    simpa only [d1246, d641, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7074 (p : Pattern) (guard : d1247 p = 1) : d642 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d642, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7038 p hg
    simpa only [d1247, d642, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d642, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7073 p hg
    simpa only [d1247, d642, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7075 (p : Pattern) (guard : d1247 p = 1) : d643 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d643, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7058 p hg
    simpa only [d643, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d643, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7074 p hg
    simpa only [d643, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7076 (p : Pattern) (guard : d1246 p = 1) : d586 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7048 p hg
    simpa only [d1246, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1246, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7077 (p : Pattern) (guard : d1247 p = 1) : d644 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7047 p hg
    simpa only [d1247, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7076 p hg
    simpa only [d1247, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7078 (p : Pattern) (guard : d1247 p = 1) : d645 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d645, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7036 p hg
    simpa only [d645, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d645, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7077 p hg
    simpa only [d645, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7079 (p : Pattern) (guard : d1247 p = 1) : d646 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d646, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7075 p hg
    simpa only [d646, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d646, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7078 p hg
    simpa only [d646, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7080 (p : Pattern) (guard : d1247 p = 1) : d647 p ≤ (0 : Int) + d322 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d647, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7065 p hg
    simpa only [d647, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d647, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7015 p hg
    simpa only [d647, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7081 (p : Pattern) (guard : d1247 p = 1) : d648 p ≤ (0 : Int) + d323 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d648, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7050 p hg
    simpa only [d648, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d648, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3637 p hg
    simpa only [d648, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7082 (p : Pattern) (guard : d1247 p = 1) : d649 p ≤ (0 : Int) + d324 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d649, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7080 p hg
    simpa only [d649, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d649, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7081 p hg
    simpa only [d649, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7083 (p : Pattern) (guard : d1247 p = 1) : d650 p ≤ (0 : Int) + d325 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d650, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7079 p hg
    simpa only [d650, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d650, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7082 p hg
    simpa only [d650, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7084 (p : Pattern) (guard : d1247 p = 1) : d651 p ≤ (0 : Int) + d326 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d651, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7068 p hg
    simpa only [d651, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d651, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7083 p hg
    simpa only [d651, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7085 (p : Pattern) (guard : d1247 p = 1) : d652 p ≤ (0 : Int) + d327 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d652, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7054 p hg
    simpa only [d652, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d652, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7084 p hg
    simpa only [d652, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7086 (p : Pattern) (guard : d1167 p = 1) : d7 p ≤ (0 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6242 p hg
    simpa only [d1167, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7087 (p : Pattern) (guard : d1167 p = 1) : d7 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7086 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2788 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7088 (p : Pattern) (guard : d1167 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d1167, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d1167, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7089 (p : Pattern) (guard : d1167 p = 1) : d13 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7088 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2792 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7090 (p : Pattern) (guard : d1167 p = 1) : d653 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7087 p hg
    simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7089 p hg
    simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7091 (p : Pattern) (guard : d1167 p = 1) : d654 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7087 p hg
    simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7090 p hg
    simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7092 (p : Pattern) (guard : d0 p = 1) : d654 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7093 (p : Pattern) (guard : d1174 p = 1) : d654 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d1174, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7092 p hg
    simpa only [d1174, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7094 (p : Pattern) (guard : d0 p = 1) : d653 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7095 (p : Pattern) (guard : d1174 p = 1) : d653 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7090 p hg
    simpa only [d1174, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1174, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7096 (p : Pattern) (guard : d1167 p = 1) : d655 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7087 p hg
    simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2816 p hg
    simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7097 (p : Pattern) (guard : d1167 p = 1) : d656 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7090 p hg
    simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7096 p hg
    simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7098 (p : Pattern) (guard : d0 p = 1) : d656 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7099 (p : Pattern) (guard : d1174 p = 1) : d656 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7097 p hg
    simpa only [d1174, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d1174, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7100 (p : Pattern) (guard : d1174 p = 1) : d657 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d657, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7095 p hg
    simpa only [d657, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d657, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7099 p hg
    simpa only [d657, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7101 (p : Pattern) (guard : d1174 p = 1) : d658 p ≤ (0 : Int) + d297 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d658, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7093 p hg
    simpa only [d658, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d658, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7100 p hg
    simpa only [d658, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7102 (p : Pattern) (guard : d0 p = 1) : d660 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7103 (p : Pattern) (guard : d1174 p = 1) : d661 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d661, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d1174, d661, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d661, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7102 p hg
    simpa only [d1174, d661, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7104 (p : Pattern) (guard : d1174 p = 1) : d662 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7093 p hg
    simpa only [d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7103 p hg
    simpa only [d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7105 (p : Pattern) (guard : d0 p = 1) : d659 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7106 (p : Pattern) (guard : d1174 p = 1) : d663 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d663, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d1174, d663, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d663, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7105 p hg
    simpa only [d1174, d663, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7107 (p : Pattern) (guard : d1174 p = 1) : d664 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d664, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7093 p hg
    simpa only [d664, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d664, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7106 p hg
    simpa only [d664, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7108 (p : Pattern) (guard : d1174 p = 1) : d665 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d665, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7104 p hg
    simpa only [d665, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d665, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7107 p hg
    simpa only [d665, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7109 (p : Pattern) (guard : d0 p = 1) : d659 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7110 (p : Pattern) (guard : d1174 p = 1) : d666 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d666, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7090 p hg
    simpa only [d1174, d666, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d666, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1174, d666, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7111 (p : Pattern) (guard : d1174 p = 1) : d667 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7095 p hg
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7110 p hg
    simpa only [d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7112 (p : Pattern) (guard : d1174 p = 1) : d668 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d668, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7097 p hg
    simpa only [d1174, d668, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d668, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1174, d668, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7113 (p : Pattern) (guard : d1174 p = 1) : d669 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7099 p hg
    simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7112 p hg
    simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7114 (p : Pattern) (guard : d1174 p = 1) : d670 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d670, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7111 p hg
    simpa only [d670, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d670, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7113 p hg
    simpa only [d670, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7115 (p : Pattern) (guard : d1174 p = 1) : d671 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d671, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7108 p hg
    simpa only [d671, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d671, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7114 p hg
    simpa only [d671, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7116 (p : Pattern) (guard : d1174 p = 1) : d672 p ≤ (0 : Int) + d302 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d672, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7101 p hg
    simpa only [d672, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d672, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7115 p hg
    simpa only [d672, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7117 (p : Pattern) (guard : d1167 p = 1) : d673 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7087 p hg
    simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7096 p hg
    simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7118 (p : Pattern) (guard : d0 p = 1) : d673 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7119 (p : Pattern) (guard : d1174 p = 1) : d673 p ≤ (0 : Int) + d303 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d1174, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7118 p hg
    simpa only [d1174, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7120 (p : Pattern) (guard : d0 p = 1) : d673 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7121 (p : Pattern) (guard : d1174 p = 1) : d673 p ≤ (0 : Int) + d304 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d1174, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7120 p hg
    simpa only [d1174, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7122 (p : Pattern) (guard : d1174 p = 1) : d673 p ≤ (0 : Int) + d305 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7119 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7123 (p : Pattern) (guard : d1174 p = 1) : d674 p ≤ (0 : Int) + d306 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d674, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7093 p hg
    simpa only [d674, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d674, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7122 p hg
    simpa only [d674, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7124 (p : Pattern) (guard : d1167 p = 1) : d659 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7089 p hg
    simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2816 p hg
    simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7125 (p : Pattern) (guard : d1167 p = 1) : d660 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7089 p hg
    simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7124 p hg
    simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7126 (p : Pattern) (guard : d0 p = 1) : d660 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7127 (p : Pattern) (guard : d1174 p = 1) : d660 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7125 p hg
    simpa only [d1174, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1174, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7128 (p : Pattern) (guard : d1174 p = 1) : d675 p ≤ (0 : Int) + d308 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d675, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7123 p hg
    simpa only [d675, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d675, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7127 p hg
    simpa only [d675, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7129 (p : Pattern) (guard : d1174 p = 1) : d676 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d676, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d1174, d676, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d676, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1174, d676, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7130 (p : Pattern) (guard : d1174 p = 1) : d677 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d677, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d677, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d677, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d677, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7131 (p : Pattern) (guard : d1174 p = 1) : d678 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d678, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7107 p hg
    simpa only [d678, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d678, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7130 p hg
    simpa only [d678, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7132 (p : Pattern) (guard : d1174 p = 1) : d679 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d679, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7125 p hg
    simpa only [d1174, d679, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d679, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1174, d679, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7133 (p : Pattern) (guard : d1174 p = 1) : d680 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7127 p hg
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7132 p hg
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7134 (p : Pattern) (guard : d1174 p = 1) : d659 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7124 p hg
    simpa only [d1174, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1174, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7135 (p : Pattern) (guard : d1174 p = 1) : d681 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d681, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7124 p hg
    simpa only [d1174, d681, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d681, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1174, d681, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7136 (p : Pattern) (guard : d1174 p = 1) : d682 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7134 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7135 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7137 (p : Pattern) (guard : d1174 p = 1) : d683 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d683, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7133 p hg
    simpa only [d683, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d683, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7136 p hg
    simpa only [d683, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7138 (p : Pattern) (guard : d1174 p = 1) : d684 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d684, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7131 p hg
    simpa only [d684, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d684, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7137 p hg
    simpa only [d684, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7139 (p : Pattern) (guard : d1174 p = 1) : d685 p ≤ (0 : Int) + d315 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d685, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7128 p hg
    simpa only [d685, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d685, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7138 p hg
    simpa only [d685, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
