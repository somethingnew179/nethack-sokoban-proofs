/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons313
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43960 (p : Pattern) (guard : d8111 p = 1) : d125 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d125, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35308 p hg
    simpa only [d8111, d125, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d125, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d125, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43961 (p : Pattern) (guard : d8117 p = 1) : d141 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d141, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43960 p hg
    simpa only [d8117, d141, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d141, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34902 p hg
    simpa only [d8117, d141, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43962 (p : Pattern) (guard : d8118 p = 1) : d1585 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1585, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43959 p hg
    simpa only [d8118, d1585, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1585, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43961 p hg
    simpa only [d8118, d1585, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43963 (p : Pattern) (guard : d8124 p = 1) : d1586 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1586, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43962 p hg
    simpa only [d8124, d1586, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1586, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35248 p hg
    simpa only [d8124, d1586, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43964 (p : Pattern) (guard : d8130 p = 1) : d1592 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1592, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43963 p hg
    simpa only [d8130, d1592, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1592, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43943 p hg
    simpa only [d8130, d1592, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43965 (p : Pattern) (guard : d8131 p = 1) : d1593 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1593, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43956 p hg
    simpa only [d8131, d1593, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1593, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43964 p hg
    simpa only [d8131, d1593, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43966 (p : Pattern) (guard : d8118 p = 1) : d1595 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1595, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43898 p hg
    simpa only [d8118, d1595, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1595, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1595, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43967 (p : Pattern) (guard : d8124 p = 1) : d1596 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1596, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43966 p hg
    simpa only [d8124, d1596, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1596, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1596, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43968 (p : Pattern) (guard : d8130 p = 1) : d1597 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1597, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43967 p hg
    simpa only [d8130, d1597, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1597, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d1597, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43969 (p : Pattern) (guard : d8136 p = 1) : d1598 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1598, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43968 p hg
    simpa only [d8136, d1598, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1598, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d8136, d1598, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43970 (p : Pattern) (guard : d8137 p = 1) : d1599 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1599, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43965 p hg
    simpa only [d8137, d1599, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1599, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43969 p hg
    simpa only [d8137, d1599, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43971 (p : Pattern) (guard : d8138 p = 1) : d1600 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1600, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43946 p hg
    simpa only [d8138, d1600, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1600, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43970 p hg
    simpa only [d8138, d1600, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43972 (p : Pattern) (guard : d8107 p = 1) : d1601 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1601, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43889 p hg
    simpa only [d8107, d1601, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1601, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43957 p hg
    simpa only [d8107, d1601, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43973 (p : Pattern) (guard : d8112 p = 1) : d126 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d126, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43936 p hg
    simpa only [d8112, d126, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d126, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43960 p hg
    simpa only [d8112, d126, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43974 (p : Pattern) (guard : d8113 p = 1) : d1602 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1602, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43972 p hg
    simpa only [d8113, d1602, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1602, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43973 p hg
    simpa only [d8113, d1602, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43975 (p : Pattern) (guard : d8118 p = 1) : d129 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d129, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43948 p hg
    simpa only [d8118, d129, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d129, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35196 p hg
    simpa only [d8118, d129, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43976 (p : Pattern) (guard : d8119 p = 1) : d1603 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1603, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43974 p hg
    simpa only [d8119, d1603, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1603, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43975 p hg
    simpa only [d8119, d1603, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43977 (p : Pattern) (guard : d8112 p = 1) : d124 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43902 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35319 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43978 (p : Pattern) (guard : d8118 p = 1) : d1577 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1577, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43977 p hg
    simpa only [d8118, d1577, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1577, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35320 p hg
    simpa only [d8118, d1577, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43979 (p : Pattern) (guard : d8124 p = 1) : d1578 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1578, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43978 p hg
    simpa only [d8124, d1578, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1578, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35322 p hg
    simpa only [d8124, d1578, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43980 (p : Pattern) (guard : d8125 p = 1) : d1604 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1604, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43976 p hg
    simpa only [d8125, d1604, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1604, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43979 p hg
    simpa only [d8125, d1604, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43981 (p : Pattern) (guard : d8106 p = 1) : d124 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35328 p hg
    simpa only [d8106, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43982 (p : Pattern) (guard : d8111 p = 1) : d139 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d139, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35334 p hg
    simpa only [d8111, d139, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d139, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d139, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43983 (p : Pattern) (guard : d8112 p = 1) : d1584 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1584, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43981 p hg
    simpa only [d8112, d1584, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1584, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43982 p hg
    simpa only [d8112, d1584, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43984 (p : Pattern) (guard : d8111 p = 1) : d125 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d125, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35341 p hg
    simpa only [d8111, d125, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d125, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d125, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43985 (p : Pattern) (guard : d8117 p = 1) : d141 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d141, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43984 p hg
    simpa only [d8117, d141, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d141, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34902 p hg
    simpa only [d8117, d141, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43986 (p : Pattern) (guard : d8118 p = 1) : d1585 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1585, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43983 p hg
    simpa only [d8118, d1585, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1585, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43985 p hg
    simpa only [d8118, d1585, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43987 (p : Pattern) (guard : d8117 p = 1) : d143 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d143, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43960 p hg
    simpa only [d8117, d143, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d143, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35246 p hg
    simpa only [d8117, d143, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43988 (p : Pattern) (guard : d8123 p = 1) : d144 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d144, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43987 p hg
    simpa only [d8123, d144, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d144, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d144, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43989 (p : Pattern) (guard : d8124 p = 1) : d1586 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1586, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43986 p hg
    simpa only [d8124, d1586, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1586, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43988 p hg
    simpa only [d8124, d1586, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43990 (p : Pattern) (guard : d8117 p = 1) : d1584 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35319 p hg
    simpa only [d8117, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d8117, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43991 (p : Pattern) (guard : d8123 p = 1) : d1585 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43990 p hg
    simpa only [d8123, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35349 p hg
    simpa only [d8123, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43992 (p : Pattern) (guard : d8129 p = 1) : d1586 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43991 p hg
    simpa only [d8129, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13566 p hg
    simpa only [d8129, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43993 (p : Pattern) (guard : d8130 p = 1) : d1586 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43989 p hg
    simpa only [d8130, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43992 p hg
    simpa only [d8130, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43994 (p : Pattern) (guard : d8131 p = 1) : d1605 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1605, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43980 p hg
    simpa only [d8131, d1605, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1605, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43993 p hg
    simpa only [d8131, d1605, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43995 (p : Pattern) (guard : d8112 p = 1) : d124 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43919 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35319 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43996 (p : Pattern) (guard : d8118 p = 1) : d1577 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1577, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43995 p hg
    simpa only [d8118, d1577, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1577, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35320 p hg
    simpa only [d8118, d1577, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43997 (p : Pattern) (guard : d8124 p = 1) : d1578 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1578, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43996 p hg
    simpa only [d8124, d1578, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1578, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35322 p hg
    simpa only [d8124, d1578, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43998 (p : Pattern) (guard : d8117 p = 1) : d1053 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35242 p hg
    simpa only [d8117, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8222 p hg
    simpa only [d8117, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43999 (p : Pattern) (guard : d8123 p = 1) : d1054 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43998 p hg
    simpa only [d8123, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44000 (p : Pattern) (guard : d8129 p = 1) : d1589 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43999 p hg
    simpa only [d8129, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44001 (p : Pattern) (guard : d8130 p = 1) : d1590 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1590, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43997 p hg
    simpa only [d8130, d1590, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1590, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44000 p hg
    simpa only [d8130, d1590, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44002 (p : Pattern) (guard : d8117 p = 1) : d1584 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1584, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35739 p hg
    simpa only [d8117, d1584, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1584, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d8117, d1584, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44003 (p : Pattern) (guard : d8123 p = 1) : d1585 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1585, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44002 p hg
    simpa only [d8123, d1585, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1585, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35349 p hg
    simpa only [d8123, d1585, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44004 (p : Pattern) (guard : d8129 p = 1) : d1586 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1586, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44003 p hg
    simpa only [d8129, d1586, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1586, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13566 p hg
    simpa only [d8129, d1586, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44005 (p : Pattern) (guard : d8135 p = 1) : d1592 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1592, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44004 p hg
    simpa only [d8135, d1592, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1592, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11992 p hg
    simpa only [d8135, d1592, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44006 (p : Pattern) (guard : d8136 p = 1) : d1593 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1593, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44001 p hg
    simpa only [d8136, d1593, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1593, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44005 p hg
    simpa only [d8136, d1593, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44007 (p : Pattern) (guard : d8137 p = 1) : d1606 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1606, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43994 p hg
    simpa only [d8137, d1606, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1606, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44006 p hg
    simpa only [d8137, d1606, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44008 (p : Pattern) (guard : d8112 p = 1) : d124 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43936 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35739 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44009 (p : Pattern) (guard : d8118 p = 1) : d1577 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1577, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44008 p hg
    simpa only [d8118, d1577, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1577, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35320 p hg
    simpa only [d8118, d1577, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44010 (p : Pattern) (guard : d8124 p = 1) : d1578 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1578, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44009 p hg
    simpa only [d8124, d1578, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1578, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35322 p hg
    simpa only [d8124, d1578, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44011 (p : Pattern) (guard : d8130 p = 1) : d1590 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1590, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44010 p hg
    simpa only [d8130, d1590, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1590, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44000 p hg
    simpa only [d8130, d1590, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44012 (p : Pattern) (guard : d8111 p = 1) : d124 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d124, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35736 p hg
    simpa only [d8111, d124, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d124, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d124, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44013 (p : Pattern) (guard : d8117 p = 1) : d1584 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1584, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44012 p hg
    simpa only [d8117, d1584, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1584, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d8117, d1584, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44014 (p : Pattern) (guard : d8123 p = 1) : d1585 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1585, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44013 p hg
    simpa only [d8123, d1585, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1585, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35349 p hg
    simpa only [d8123, d1585, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44015 (p : Pattern) (guard : d8129 p = 1) : d1586 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1586, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44014 p hg
    simpa only [d8129, d1586, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1586, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13566 p hg
    simpa only [d8129, d1586, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44016 (p : Pattern) (guard : d8135 p = 1) : d1592 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1592, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44015 p hg
    simpa only [d8135, d1592, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1592, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11992 p hg
    simpa only [d8135, d1592, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44017 (p : Pattern) (guard : d8136 p = 1) : d1593 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1593, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44011 p hg
    simpa only [d8136, d1593, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1593, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44016 p hg
    simpa only [d8136, d1593, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44018 (p : Pattern) (guard : d8142 p = 1) : d1607 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1607, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44017 p hg
    simpa only [d8142, d1607, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1607, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1607, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44019 (p : Pattern) (guard : d8143 p = 1) : d1608 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1608, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44007 p hg
    simpa only [d8143, d1608, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1608, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44018 p hg
    simpa only [d8143, d1608, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44020 (p : Pattern) (guard : d8144 p = 1) : d1609 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1609, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43971 p hg
    simpa only [d8144, d1609, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1609, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44019 p hg
    simpa only [d8144, d1609, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44021 (p : Pattern) (guard : d8145 p = 1) : d1610 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d1610, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43885 p hg
    simpa only [d8145, d1610, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d1610, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44020 p hg
    simpa only [d8145, d1610, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44022 (p : Pattern) (guard : d8146 p = 1) : d1611 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43812 p hg
    simpa only [d8146, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44021 p hg
    simpa only [d8146, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44023 (p : Pattern) (guard : d8096 p = 1) : d1553 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1553, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35383 p hg
    simpa only [d8096, d1553, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1553, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43886 p hg
    simpa only [d8096, d1553, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44024 (p : Pattern) (guard : d8101 p = 1) : d1507 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35388 p hg
    simpa only [d8101, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43888 p hg
    simpa only [d8101, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44025 (p : Pattern) (guard : d8102 p = 1) : d1554 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1554, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44023 p hg
    simpa only [d8102, d1554, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1554, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44024 p hg
    simpa only [d8102, d1554, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44026 (p : Pattern) (guard : d8106 p = 1) : d43 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35395 p hg
    simpa only [d8106, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44027 (p : Pattern) (guard : d8107 p = 1) : d47 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43861 p hg
    simpa only [d8107, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44026 p hg
    simpa only [d8107, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44028 (p : Pattern) (guard : d8108 p = 1) : d1555 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1555, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44025 p hg
    simpa only [d8108, d1555, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1555, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44027 p hg
    simpa only [d8108, d1555, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44029 (p : Pattern) (guard : d8107 p = 1) : d47 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d47, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43768 p hg
    simpa only [d8107, d47, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d47, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43864 p hg
    simpa only [d8107, d47, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44030 (p : Pattern) (guard : d8112 p = 1) : d49 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d49, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43710 p hg
    simpa only [d8112, d49, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d49, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d49, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44031 (p : Pattern) (guard : d8113 p = 1) : d50 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44029 p hg
    simpa only [d8113, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44030 p hg
    simpa only [d8113, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44032 (p : Pattern) (guard : d8114 p = 1) : d1556 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1556, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44028 p hg
    simpa only [d8114, d1556, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1556, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44031 p hg
    simpa only [d8114, d1556, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44033 (p : Pattern) (guard : d8120 p = 1) : d1557 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1557, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44032 p hg
    simpa only [d8120, d1557, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1557, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43875 p hg
    simpa only [d8120, d1557, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44034 (p : Pattern) (guard : d8101 p = 1) : d1505 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35413 p hg
    simpa only [d8101, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43907 p hg
    simpa only [d8101, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44035 (p : Pattern) (guard : d8106 p = 1) : d66 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d66, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35419 p hg
    simpa only [d8106, d66, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d66, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d66, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44036 (p : Pattern) (guard : d8107 p = 1) : d1558 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1558, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44034 p hg
    simpa only [d8107, d1558, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1558, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44035 p hg
    simpa only [d8107, d1558, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44037 (p : Pattern) (guard : d8106 p = 1) : d43 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35425 p hg
    simpa only [d8106, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44038 (p : Pattern) (guard : d8111 p = 1) : d48 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35431 p hg
    simpa only [d8111, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44039 (p : Pattern) (guard : d8112 p = 1) : d68 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d68, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44037 p hg
    simpa only [d8112, d68, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d68, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44038 p hg
    simpa only [d8112, d68, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44040 (p : Pattern) (guard : d8113 p = 1) : d1559 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1559, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44036 p hg
    simpa only [d8113, d1559, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1559, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44039 p hg
    simpa only [d8113, d1559, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44041 (p : Pattern) (guard : d8111 p = 1) : d70 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d70, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35439 p hg
    simpa only [d8111, d70, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d70, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d70, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44042 (p : Pattern) (guard : d8112 p = 1) : d71 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d71, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44026 p hg
    simpa only [d8112, d71, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d71, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44041 p hg
    simpa only [d8112, d71, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44043 (p : Pattern) (guard : d8118 p = 1) : d74 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d74, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44042 p hg
    simpa only [d8118, d74, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d74, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d74, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44044 (p : Pattern) (guard : d8119 p = 1) : d1560 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1560, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44040 p hg
    simpa only [d8119, d1560, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1560, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44043 p hg
    simpa only [d8119, d1560, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44045 (p : Pattern) (guard : d8125 p = 1) : d1561 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1561, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44044 p hg
    simpa only [d8125, d1561, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1561, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43880 p hg
    simpa only [d8125, d1561, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44046 (p : Pattern) (guard : d8126 p = 1) : d1562 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1562, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44033 p hg
    simpa only [d8126, d1562, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1562, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44045 p hg
    simpa only [d8126, d1562, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44047 (p : Pattern) (guard : d8107 p = 1) : d46 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43768 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43877 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44048 (p : Pattern) (guard : d8112 p = 1) : d47 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43803 p hg
    simpa only [d8112, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8112, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44049 (p : Pattern) (guard : d8113 p = 1) : d1511 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44047 p hg
    simpa only [d8113, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44048 p hg
    simpa only [d8113, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44050 (p : Pattern) (guard : d8119 p = 1) : d1512 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44049 p hg
    simpa only [d8119, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35580 p hg
    simpa only [d8119, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44051 (p : Pattern) (guard : d8125 p = 1) : d1524 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1524, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44050 p hg
    simpa only [d8125, d1524, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1524, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43788 p hg
    simpa only [d8125, d1524, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44052 (p : Pattern) (guard : d8106 p = 1) : d46 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35465 p hg
    simpa only [d8106, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44053 (p : Pattern) (guard : d8112 p = 1) : d1518 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44052 p hg
    simpa only [d8112, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35610 p hg
    simpa only [d8112, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44054 (p : Pattern) (guard : d8118 p = 1) : d1519 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44053 p hg
    simpa only [d8118, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d8118, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44055 (p : Pattern) (guard : d8124 p = 1) : d1520 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44054 p hg
    simpa only [d8124, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44056 (p : Pattern) (guard : d8130 p = 1) : d1526 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1526, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44055 p hg
    simpa only [d8130, d1526, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1526, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43795 p hg
    simpa only [d8130, d1526, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44057 (p : Pattern) (guard : d8131 p = 1) : d1527 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1527, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44051 p hg
    simpa only [d8131, d1527, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1527, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44056 p hg
    simpa only [d8131, d1527, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44058 (p : Pattern) (guard : d8132 p = 1) : d1563 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1563, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44046 p hg
    simpa only [d8132, d1563, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1563, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44057 p hg
    simpa only [d8132, d1563, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44059 (p : Pattern) (guard : d8107 p = 1) : d46 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43861 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44052 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44060 (p : Pattern) (guard : d8112 p = 1) : d47 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43877 p hg
    simpa only [d8112, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8112, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44061 (p : Pattern) (guard : d8113 p = 1) : d1511 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44059 p hg
    simpa only [d8113, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44060 p hg
    simpa only [d8113, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44062 (p : Pattern) (guard : d8118 p = 1) : d50 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44048 p hg
    simpa only [d8118, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34871 p hg
    simpa only [d8118, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44063 (p : Pattern) (guard : d8119 p = 1) : d1512 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44061 p hg
    simpa only [d8119, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44062 p hg
    simpa only [d8119, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44064 (p : Pattern) (guard : d8112 p = 1) : d176 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d8112, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43785 p hg
    simpa only [d8112, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44065 (p : Pattern) (guard : d8118 p = 1) : d177 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44064 p hg
    simpa only [d8118, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44066 (p : Pattern) (guard : d8124 p = 1) : d1523 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44065 p hg
    simpa only [d8124, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44067 (p : Pattern) (guard : d8125 p = 1) : d1524 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44063 p hg
    simpa only [d8125, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44066 p hg
    simpa only [d8125, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44068 (p : Pattern) (guard : d8106 p = 1) : d46 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35483 p hg
    simpa only [d8106, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44069 (p : Pattern) (guard : d8111 p = 1) : d66 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35628 p hg
    simpa only [d8111, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44070 (p : Pattern) (guard : d8112 p = 1) : d1518 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44068 p hg
    simpa only [d8112, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44069 p hg
    simpa only [d8112, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44071 (p : Pattern) (guard : d8111 p = 1) : d43 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35490 p hg
    simpa only [d8111, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44072 (p : Pattern) (guard : d8117 p = 1) : d68 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44071 p hg
    simpa only [d8117, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34899 p hg
    simpa only [d8117, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44073 (p : Pattern) (guard : d8118 p = 1) : d1519 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44070 p hg
    simpa only [d8118, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44072 p hg
    simpa only [d8118, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44074 (p : Pattern) (guard : d8124 p = 1) : d1520 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44073 p hg
    simpa only [d8124, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44075 (p : Pattern) (guard : d8130 p = 1) : d1526 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44074 p hg
    simpa only [d8130, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43795 p hg
    simpa only [d8130, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44076 (p : Pattern) (guard : d8131 p = 1) : d1527 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44067 p hg
    simpa only [d8131, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44075 p hg
    simpa only [d8131, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44077 (p : Pattern) (guard : d8112 p = 1) : d1534 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1534, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43710 p hg
    simpa only [d8112, d1534, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1534, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34690 p hg
    simpa only [d8112, d1534, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44078 (p : Pattern) (guard : d8118 p = 1) : d1535 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1535, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44077 p hg
    simpa only [d8118, d1535, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1535, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d1535, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44079 (p : Pattern) (guard : d8123 p = 1) : d1536 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8123, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44080 (p : Pattern) (guard : d8124 p = 1) : d1537 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1537, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44078 p hg
    simpa only [d8124, d1537, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1537, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44079 p hg
    simpa only [d8124, d1537, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44081 (p : Pattern) (guard : d8129 p = 1) : d1538 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44079 p hg
    simpa only [d8129, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44082 (p : Pattern) (guard : d8130 p = 1) : d1539 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1539, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44080 p hg
    simpa only [d8130, d1539, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1539, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44081 p hg
    simpa only [d8130, d1539, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44083 (p : Pattern) (guard : d8135 p = 1) : d1540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44081 p hg
    simpa only [d8135, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44084 (p : Pattern) (guard : d8136 p = 1) : d1541 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1541, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44082 p hg
    simpa only [d8136, d1541, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1541, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44083 p hg
    simpa only [d8136, d1541, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44085 (p : Pattern) (guard : d8137 p = 1) : d1564 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1564, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44076 p hg
    simpa only [d8137, d1564, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1564, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44084 p hg
    simpa only [d8137, d1564, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44086 (p : Pattern) (guard : d8138 p = 1) : d1565 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1565, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44058 p hg
    simpa only [d8138, d1565, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1565, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44085 p hg
    simpa only [d8138, d1565, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44087 (p : Pattern) (guard : d8107 p = 1) : d1529 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44024 p hg
    simpa only [d8107, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44068 p hg
    simpa only [d8107, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44088 (p : Pattern) (guard : d8112 p = 1) : d47 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44052 p hg
    simpa only [d8112, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44071 p hg
    simpa only [d8112, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44089 (p : Pattern) (guard : d8113 p = 1) : d1530 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44087 p hg
    simpa only [d8113, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44088 p hg
    simpa only [d8113, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44090 (p : Pattern) (guard : d8118 p = 1) : d50 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44060 p hg
    simpa only [d8118, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34871 p hg
    simpa only [d8118, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44091 (p : Pattern) (guard : d8119 p = 1) : d1531 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44089 p hg
    simpa only [d8119, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44090 p hg
    simpa only [d8119, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44092 (p : Pattern) (guard : d8112 p = 1) : d66 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43741 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44093 (p : Pattern) (guard : d8118 p = 1) : d1612 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1612, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44092 p hg
    simpa only [d8118, d1612, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1612, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41453 p hg
    simpa only [d8118, d1612, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44094 (p : Pattern) (guard : d8124 p = 1) : d1613 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1613, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44093 p hg
    simpa only [d8124, d1613, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1613, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d8124, d1613, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44095 (p : Pattern) (guard : d8125 p = 1) : d1614 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1614, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44091 p hg
    simpa only [d8125, d1614, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1614, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44094 p hg
    simpa only [d8125, d1614, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44096 (p : Pattern) (guard : d8106 p = 1) : d46 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35512 p hg
    simpa only [d8106, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44097 (p : Pattern) (guard : d8111 p = 1) : d66 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35518 p hg
    simpa only [d8111, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44098 (p : Pattern) (guard : d8112 p = 1) : d1518 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44096 p hg
    simpa only [d8112, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44097 p hg
    simpa only [d8112, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44099 (p : Pattern) (guard : d8111 p = 1) : d43 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35525 p hg
    simpa only [d8111, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
