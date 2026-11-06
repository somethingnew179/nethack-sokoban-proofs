/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare980 (p : Pattern) (guard : d0 p = 1) : d69 p ≤ (0 : Int) + d281 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare981 (p : Pattern) (guard : d768 p = 1) : d70 p ≤ (0 : Int) + d282 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d70, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d768, d70, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d70, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare980 p hg
    simpa only [d768, d70, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare982 (p : Pattern) (guard : d0 p = 1) : d240 p ≤ (0 : Int) + d283 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare983 (p : Pattern) (guard : d768 p = 1) : d241 p ≤ (0 : Int) + d284 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d241, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d768, d241, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d241, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare982 p hg
    simpa only [d768, d241, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare984 (p : Pattern) (guard : d768 p = 1) : d242 p ≤ (0 : Int) + d285 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d242, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare981 p hg
    simpa only [d242, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d242, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare983 p hg
    simpa only [d242, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare985 (p : Pattern) (guard : d768 p = 1) : d243 p ≤ (0 : Int) + d286 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d243, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare979 p hg
    simpa only [d243, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d243, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare984 p hg
    simpa only [d243, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare986 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare987 (p : Pattern) (guard : d768 p = 1) : d66 p ≤ (0 : Int) + d287 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d66, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d768, d66, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d66, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare986 p hg
    simpa only [d768, d66, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare988 (p : Pattern) (guard : d768 p = 1) : d244 p ≤ (0 : Int) + d288 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d244, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare984 p hg
    simpa only [d244, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d244, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d244, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare989 (p : Pattern) (guard : d768 p = 1) : d245 p ≤ (0 : Int) + d289 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d245, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare985 p hg
    simpa only [d245, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d245, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare988 p hg
    simpa only [d245, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare990 (p : Pattern) (guard : d0 p = 1) : d246 p ≤ (0 : Int) + d295 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare991 (p : Pattern) (guard : d768 p = 1) : d247 p ≤ (0 : Int) + d296 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d247, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d768, d247, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d247, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare990 p hg
    simpa only [d768, d247, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare992 (p : Pattern) (guard : d768 p = 1) : d248 p ≤ (0 : Int) + d297 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d248, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare991 p hg
    simpa only [d248, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d248, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d248, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare993 (p : Pattern) (guard : d0 p = 1) : d249 p ≤ (0 : Int) + d300 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare994 (p : Pattern) (guard : d768 p = 1) : d250 p ≤ (0 : Int) + d301 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d250, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d768, d250, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d250, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare993 p hg
    simpa only [d768, d250, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare995 (p : Pattern) (guard : d768 p = 1) : d251 p ≤ (0 : Int) + d302 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d251, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare994 p hg
    simpa only [d251, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d251, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d251, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare996 (p : Pattern) (guard : d768 p = 1) : d252 p ≤ (0 : Int) + d303 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d252, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare992 p hg
    simpa only [d252, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d252, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare995 p hg
    simpa only [d252, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare997 (p : Pattern) (guard : d0 p = 1) : d253 p ≤ (0 : Int) + d304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare998 (p : Pattern) (guard : d768 p = 1) : d254 p ≤ (0 : Int) + d305 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d254, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d768, d254, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d254, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare997 p hg
    simpa only [d768, d254, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare999 (p : Pattern) (guard : d768 p = 1) : d255 p ≤ (0 : Int) + d306 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d255, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare998 p hg
    simpa only [d255, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d255, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d255, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1000 (p : Pattern) (guard : d768 p = 1) : d256 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d256, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare999 p hg
    simpa only [d256, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d256, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d256, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1001 (p : Pattern) (guard : d768 p = 1) : d257 p ≤ (0 : Int) + d308 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d257, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare996 p hg
    simpa only [d257, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d257, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1000 p hg
    simpa only [d257, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1002 (p : Pattern) (guard : d768 p = 1) : d258 p ≤ (0 : Int) + d309 p := by
  cases selected : p 108 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d258, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare989 p hg
    simpa only [d258, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d258, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1001 p hg
    simpa only [d258, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1003 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (1 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1004 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (1 : Int) + d7 p := by
  omega
theorem compare1005 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d0 p := by
  omega
theorem compare1006 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (1 : Int) + d0 p := by
  change (1 : Int) ≤ (1 : Int) + 0
  decide
theorem compare1007 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (1 : Int) + d0 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1005 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1006 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1008 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  omega
theorem compare1009 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (1 : Int) + d2 p := by
  change (3 : Int) ≤ (1 : Int) + 2
  decide
theorem compare1010 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (1 : Int) + d2 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1008 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1009 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1011 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (1 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1007 p hg
    simpa only [d10, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1010 p hg
    simpa only [d10, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1012 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (1 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1007 p hg
    simpa only [d11, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1011 p hg
    simpa only [d11, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1013 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1004 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1012 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1014 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (1 : Int) + d56 p := by
  omega
theorem compare1015 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d4 p := by
  omega
theorem compare1016 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (1 : Int) + d4 p := by
  change (5 : Int) ≤ (1 : Int) + 4
  decide
theorem compare1017 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (1 : Int) + d4 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1015 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1016 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1018 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (1 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1010 p hg
    simpa only [d59, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1017 p hg
    simpa only [d59, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1019 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (1 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1010 p hg
    simpa only [d60, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1018 p hg
    simpa only [d60, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1020 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (1 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1012 p hg
    simpa only [d61, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1019 p hg
    simpa only [d61, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1021 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (1 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1014 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1020 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1022 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (1 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1013 p hg
    simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1021 p hg
    simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1023 (p : Pattern) (guard : d767 p = 1) : d64 p ≤ (1 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d767, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1003 p hg
    simpa only [d767, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d767, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1022 p hg
    simpa only [d767, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1024 (p : Pattern) (guard : d0 p = 1) : d179 p ≤ (1 : Int) + d179 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1025 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (1 : Int) + d55 p := by
  omega
theorem compare1026 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (1 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1025 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1019 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1027 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1013 p hg
    simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1028 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (1 : Int) + d120 p := by
  omega
theorem compare1029 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (1 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1012 p hg
    simpa only [d125, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1019 p hg
    simpa only [d125, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1030 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (1 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1012 p hg
    simpa only [d126, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1029 p hg
    simpa only [d126, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1031 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (1 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1028 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1030 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1032 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (1 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1031 p hg
    simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1033 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (1 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1027 p hg
    simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1032 p hg
    simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1034 (p : Pattern) (guard : d1 p = 1) : d237 p ≤ (1 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1027 p hg
    simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1033 p hg
    simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1035 (p : Pattern) (guard : d767 p = 1) : d238 p ≤ (1 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d767, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1024 p hg
    simpa only [d767, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d767, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1034 p hg
    simpa only [d767, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1036 (p : Pattern) (guard : d767 p = 1) : d239 p ≤ (1 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1023 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1035 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1037 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (1 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1038 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (1 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1022 p hg
    simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1039 (p : Pattern) (guard : d767 p = 1) : d70 p ≤ (1 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d767, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1037 p hg
    simpa only [d767, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d767, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1038 p hg
    simpa only [d767, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1040 (p : Pattern) (guard : d0 p = 1) : d181 p ≤ (1 : Int) + d181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1041 (p : Pattern) (guard : d1 p = 1) : d240 p ≤ (1 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1033 p hg
    simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1042 (p : Pattern) (guard : d767 p = 1) : d241 p ≤ (1 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d767, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1040 p hg
    simpa only [d767, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d767, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1041 p hg
    simpa only [d767, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1043 (p : Pattern) (guard : d767 p = 1) : d242 p ≤ (1 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1039 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1042 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1044 (p : Pattern) (guard : d767 p = 1) : d243 p ≤ (1 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1036 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1043 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1045 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (1 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1046 (p : Pattern) (guard : d767 p = 1) : d66 p ≤ (1 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d767, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1045 p hg
    simpa only [d767, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d767, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d767, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1047 (p : Pattern) (guard : d767 p = 1) : d244 p ≤ (1 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1043 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1046 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1048 (p : Pattern) (guard : d767 p = 1) : d245 p ≤ (1 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1047 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1049 (p : Pattern) (guard : d0 p = 1) : d186 p ≤ (1 : Int) + d186 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1050 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (1 : Int) + d137 p := by
  omega
theorem compare1051 (p : Pattern) (guard : d1 p = 1) : d143 p ≤ (1 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1029 p hg
    simpa only [d143, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1019 p hg
    simpa only [d143, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1052 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (1 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1050 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1051 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1053 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (1 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1031 p hg
    simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1052 p hg
    simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1054 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (1 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1022 p hg
    simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1053 p hg
    simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1055 (p : Pattern) (guard : d1 p = 1) : d246 p ≤ (1 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1022 p hg
    simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1056 (p : Pattern) (guard : d767 p = 1) : d247 p ≤ (1 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d767, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1049 p hg
    simpa only [d767, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d767, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1055 p hg
    simpa only [d767, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1057 (p : Pattern) (guard : d767 p = 1) : d248 p ≤ (1 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1056 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1046 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1058 (p : Pattern) (guard : d0 p = 1) : d188 p ≤ (1 : Int) + d188 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1059 (p : Pattern) (guard : d1 p = 1) : d145 p ≤ (1 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1013 p hg
    simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1052 p hg
    simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1060 (p : Pattern) (guard : d1 p = 1) : d147 p ≤ (1 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1059 p hg
    simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1053 p hg
    simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1061 (p : Pattern) (guard : d1 p = 1) : d249 p ≤ (1 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1060 p hg
    simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1062 (p : Pattern) (guard : d767 p = 1) : d250 p ≤ (1 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d767, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1058 p hg
    simpa only [d767, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d767, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1061 p hg
    simpa only [d767, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1063 (p : Pattern) (guard : d767 p = 1) : d251 p ≤ (1 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1062 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1046 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1064 (p : Pattern) (guard : d767 p = 1) : d252 p ≤ (1 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1057 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1063 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1065 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (1 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1066 (p : Pattern) (guard : d1 p = 1) : d253 p ≤ (1 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1067 (p : Pattern) (guard : d767 p = 1) : d254 p ≤ (1 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d767, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1065 p hg
    simpa only [d767, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d767, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1066 p hg
    simpa only [d767, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1068 (p : Pattern) (guard : d767 p = 1) : d255 p ≤ (1 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1067 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1046 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1069 (p : Pattern) (guard : d767 p = 1) : d256 p ≤ (1 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1068 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1046 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1070 (p : Pattern) (guard : d767 p = 1) : d257 p ≤ (1 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1064 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1069 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1071 (p : Pattern) (guard : d767 p = 1) : d258 p ≤ (1 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1048 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1070 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1072 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1073 (p : Pattern) (guard : d768 p = 1) : d64 p ≤ (0 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d768, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1072 p hg
    simpa only [d768, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1074 (p : Pattern) (guard : d0 p = 1) : d237 p ≤ (0 : Int) + d179 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1075 (p : Pattern) (guard : d768 p = 1) : d238 p ≤ (0 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d768, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1074 p hg
    simpa only [d768, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1076 (p : Pattern) (guard : d768 p = 1) : d239 p ≤ (0 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1073 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1075 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1077 (p : Pattern) (guard : d0 p = 1) : d69 p ≤ (0 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1078 (p : Pattern) (guard : d768 p = 1) : d70 p ≤ (0 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d768, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1077 p hg
    simpa only [d768, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1079 (p : Pattern) (guard : d0 p = 1) : d240 p ≤ (0 : Int) + d181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1080 (p : Pattern) (guard : d768 p = 1) : d241 p ≤ (0 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d768, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1079 p hg
    simpa only [d768, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1081 (p : Pattern) (guard : d768 p = 1) : d242 p ≤ (0 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1078 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1080 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1082 (p : Pattern) (guard : d768 p = 1) : d243 p ≤ (0 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1076 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1081 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1083 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1084 (p : Pattern) (guard : d768 p = 1) : d66 p ≤ (0 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d768, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1083 p hg
    simpa only [d768, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1085 (p : Pattern) (guard : d768 p = 1) : d244 p ≤ (0 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1081 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1084 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1086 (p : Pattern) (guard : d768 p = 1) : d245 p ≤ (0 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1082 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1085 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1087 (p : Pattern) (guard : d0 p = 1) : d246 p ≤ (0 : Int) + d186 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1088 (p : Pattern) (guard : d768 p = 1) : d247 p ≤ (0 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d768, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1087 p hg
    simpa only [d768, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1089 (p : Pattern) (guard : d768 p = 1) : d248 p ≤ (0 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1088 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1084 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1090 (p : Pattern) (guard : d0 p = 1) : d249 p ≤ (0 : Int) + d188 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1091 (p : Pattern) (guard : d768 p = 1) : d250 p ≤ (0 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d768, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1090 p hg
    simpa only [d768, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1092 (p : Pattern) (guard : d768 p = 1) : d251 p ≤ (0 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1091 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1084 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1093 (p : Pattern) (guard : d768 p = 1) : d252 p ≤ (0 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1089 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1092 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1094 (p : Pattern) (guard : d0 p = 1) : d253 p ≤ (0 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1095 (p : Pattern) (guard : d768 p = 1) : d254 p ≤ (0 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d768, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1094 p hg
    simpa only [d768, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1096 (p : Pattern) (guard : d768 p = 1) : d255 p ≤ (0 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1095 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1084 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1097 (p : Pattern) (guard : d768 p = 1) : d256 p ≤ (0 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1096 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1084 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1098 (p : Pattern) (guard : d768 p = 1) : d257 p ≤ (0 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1093 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1097 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1099 (p : Pattern) (guard : d768 p = 1) : d258 p ≤ (0 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1098 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1100 (p : Pattern) (guard : d0 p = 1) : d267 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1101 (p : Pattern) (guard : d768 p = 1) : d268 p ≤ (0 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1100 p hg
    simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1102 (p : Pattern) (guard : d0 p = 1) : d278 p ≤ (0 : Int) + d179 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1103 (p : Pattern) (guard : d768 p = 1) : d279 p ≤ (0 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1102 p hg
    simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1104 (p : Pattern) (guard : d768 p = 1) : d280 p ≤ (0 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d280, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1101 p hg
    simpa only [d280, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d280, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1103 p hg
    simpa only [d280, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1105 (p : Pattern) (guard : d0 p = 1) : d281 p ≤ (0 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1106 (p : Pattern) (guard : d768 p = 1) : d282 p ≤ (0 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1105 p hg
    simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1107 (p : Pattern) (guard : d0 p = 1) : d283 p ≤ (0 : Int) + d181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1108 (p : Pattern) (guard : d768 p = 1) : d284 p ≤ (0 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1107 p hg
    simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1109 (p : Pattern) (guard : d768 p = 1) : d285 p ≤ (0 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d285, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1106 p hg
    simpa only [d285, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d285, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1108 p hg
    simpa only [d285, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1110 (p : Pattern) (guard : d768 p = 1) : d286 p ≤ (0 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d286, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1104 p hg
    simpa only [d286, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d286, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1109 p hg
    simpa only [d286, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1111 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1112 (p : Pattern) (guard : d768 p = 1) : d287 p ≤ (0 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1111 p hg
    simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1113 (p : Pattern) (guard : d768 p = 1) : d288 p ≤ (0 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d288, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1109 p hg
    simpa only [d288, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d288, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d288, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1114 (p : Pattern) (guard : d768 p = 1) : d289 p ≤ (0 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d289, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1110 p hg
    simpa only [d289, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d289, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1113 p hg
    simpa only [d289, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1115 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d186 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1116 (p : Pattern) (guard : d768 p = 1) : d296 p ≤ (0 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1115 p hg
    simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1117 (p : Pattern) (guard : d768 p = 1) : d297 p ≤ (0 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d297, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1116 p hg
    simpa only [d297, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d297, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d297, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1118 (p : Pattern) (guard : d0 p = 1) : d300 p ≤ (0 : Int) + d188 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1119 (p : Pattern) (guard : d768 p = 1) : d301 p ≤ (0 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1118 p hg
    simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
