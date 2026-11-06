/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons086
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12180 (p : Pattern) (guard : d4208 p = 1) : d1564 p ≤ (2 : Int) + d4730 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12179 p hg
    simpa only [d4208, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12141 p hg
    simpa only [d4208, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12181 (p : Pattern) (guard : d4208 p = 1) : d1565 p ≤ (2 : Int) + d4968 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1565, d4968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12176 p hg
    simpa only [d1565, d4968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1565, d4968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12180 p hg
    simpa only [d1565, d4968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12182 (p : Pattern) (guard : d0 p = 1) : d1531 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12183 (p : Pattern) (guard : d4207 p = 1) : d1566 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12182 p hg
    simpa only [d4207, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12104 p hg
    simpa only [d4207, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12184 (p : Pattern) (guard : d4207 p = 1) : d1567 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1567, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12183 p hg
    simpa only [d1567, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1567, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12147 p hg
    simpa only [d1567, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12185 (p : Pattern) (guard : d4208 p = 1) : d1568 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12184 p hg
    simpa only [d4208, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12123 p hg
    simpa only [d4208, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12186 (p : Pattern) (guard : d4208 p = 1) : d1569 p ≤ (2 : Int) + d4969 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1569, d4969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12185 p hg
    simpa only [d1569, d4969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1569, d4969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12168 p hg
    simpa only [d1569, d4969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12187 (p : Pattern) (guard : d4208 p = 1) : d1570 p ≤ (2 : Int) + d4970 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1570, d4970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12181 p hg
    simpa only [d1570, d4970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1570, d4970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12186 p hg
    simpa only [d1570, d4970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12188 (p : Pattern) (guard : d4208 p = 1) : d1571 p ≤ (2 : Int) + d4970 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12170 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12187 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12189 (p : Pattern) (guard : d0 p = 1) : d1576 p ≤ (2 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12190 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12191 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d124, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4206, d124, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d124, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12190 p hg
    simpa only [d4206, d124, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12192 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12193 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d125, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d4206, d125, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d125, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12192 p hg
    simpa only [d4206, d125, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12194 (p : Pattern) (guard : d4206 p = 1) : d126 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d126, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12191 p hg
    simpa only [d126, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d126, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12193 p hg
    simpa only [d126, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12195 (p : Pattern) (guard : d4206 p = 1) : d1577 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1577, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12191 p hg
    simpa only [d1577, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1577, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12194 p hg
    simpa only [d1577, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12196 (p : Pattern) (guard : d4206 p = 1) : d128 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d128, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12113 p hg
    simpa only [d128, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d128, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d128, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12197 (p : Pattern) (guard : d4206 p = 1) : d129 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d129, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12194 p hg
    simpa only [d129, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d129, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12196 p hg
    simpa only [d129, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12198 (p : Pattern) (guard : d4206 p = 1) : d1578 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1578, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12195 p hg
    simpa only [d1578, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1578, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12197 p hg
    simpa only [d1578, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12199 (p : Pattern) (guard : d4207 p = 1) : d1579 p ≤ (2 : Int) + d114 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12189 p hg
    simpa only [d4207, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12198 p hg
    simpa only [d4207, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12200 (p : Pattern) (guard : d0 p = 1) : d1583 p ≤ (2 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12201 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d117 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12202 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d139, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d4206, d139, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d139, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12201 p hg
    simpa only [d4206, d139, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12203 (p : Pattern) (guard : d4206 p = 1) : d1584 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1584, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12191 p hg
    simpa only [d1584, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1584, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12202 p hg
    simpa only [d1584, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12204 (p : Pattern) (guard : d4206 p = 1) : d141 p ≤ (2 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d141, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12193 p hg
    simpa only [d141, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d141, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12113 p hg
    simpa only [d141, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12205 (p : Pattern) (guard : d4206 p = 1) : d1585 p ≤ (2 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1585, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12203 p hg
    simpa only [d1585, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1585, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12204 p hg
    simpa only [d1585, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12206 (p : Pattern) (guard : d4206 p = 1) : d143 p ≤ (2 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d143, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12193 p hg
    simpa only [d143, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d143, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12117 p hg
    simpa only [d143, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12207 (p : Pattern) (guard : d4206 p = 1) : d144 p ≤ (2 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d144, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12206 p hg
    simpa only [d144, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d144, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d144, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12208 (p : Pattern) (guard : d4206 p = 1) : d1586 p ≤ (2 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1586, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12205 p hg
    simpa only [d1586, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1586, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12207 p hg
    simpa only [d1586, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12209 (p : Pattern) (guard : d4207 p = 1) : d1587 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12200 p hg
    simpa only [d4207, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12208 p hg
    simpa only [d4207, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12210 (p : Pattern) (guard : d4207 p = 1) : d1588 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1588, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12199 p hg
    simpa only [d1588, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1588, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12209 p hg
    simpa only [d1588, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12211 (p : Pattern) (guard : d0 p = 1) : d1593 p ≤ (2 : Int) + d4736 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12212 (p : Pattern) (guard : d4208 p = 1) : d1594 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12210 p hg
    simpa only [d4208, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12211 p hg
    simpa only [d4208, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12213 (p : Pattern) (guard : d0 p = 1) : d1578 p ≤ (2 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12214 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d10 p := by
  change (3 : Int) ≤ (2 : Int) + 10
  decide
theorem compare12215 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12214 p hg
    simpa only [d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12216 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12214 p hg
    simpa only [d116, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12215 p hg
    simpa only [d116, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12217 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d139, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12216 p hg
    simpa only [d4206, d139, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d139, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12112 p hg
    simpa only [d4206, d139, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12218 (p : Pattern) (guard : d4206 p = 1) : d229 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4931 p hg
    simpa only [d4206, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4206, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12219 (p : Pattern) (guard : d4206 p = 1) : d1053 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1053, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12217 p hg
    simpa only [d1053, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1053, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12218 p hg
    simpa only [d1053, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12220 (p : Pattern) (guard : d4206 p = 1) : d1054 p ≤ (2 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1054, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12219 p hg
    simpa only [d1054, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1054, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1054, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12221 (p : Pattern) (guard : d4206 p = 1) : d1589 p ≤ (2 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1589, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12220 p hg
    simpa only [d1589, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1589, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1589, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12222 (p : Pattern) (guard : d4207 p = 1) : d1590 p ≤ (2 : Int) + d160 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12213 p hg
    simpa only [d4207, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12221 p hg
    simpa only [d4207, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12223 (p : Pattern) (guard : d0 p = 1) : d1586 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12224 (p : Pattern) (guard : d4206 p = 1) : d230 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12218 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12225 (p : Pattern) (guard : d4206 p = 1) : d231 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12224 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12226 (p : Pattern) (guard : d4206 p = 1) : d1591 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12225 p hg
    simpa only [d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12227 (p : Pattern) (guard : d4207 p = 1) : d1592 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12223 p hg
    simpa only [d4207, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12226 p hg
    simpa only [d4207, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12228 (p : Pattern) (guard : d4207 p = 1) : d1593 p ≤ (2 : Int) + d4737 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1593, d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12222 p hg
    simpa only [d1593, d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1593, d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12227 p hg
    simpa only [d1593, d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12229 (p : Pattern) (guard : d0 p = 1) : d1598 p ≤ (2 : Int) + d4737 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12230 (p : Pattern) (guard : d4208 p = 1) : d1599 p ≤ (2 : Int) + d4737 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12228 p hg
    simpa only [d4208, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12229 p hg
    simpa only [d4208, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12231 (p : Pattern) (guard : d4208 p = 1) : d1600 p ≤ (2 : Int) + d4971 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1600, d4971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12212 p hg
    simpa only [d1600, d4971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1600, d4971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12230 p hg
    simpa only [d1600, d4971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12232 (p : Pattern) (guard : d0 p = 1) : d1603 p ≤ (2 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12233 (p : Pattern) (guard : d4207 p = 1) : d1604 p ≤ (2 : Int) + d114 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12232 p hg
    simpa only [d4207, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12198 p hg
    simpa only [d4207, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12234 (p : Pattern) (guard : d0 p = 1) : d1586 p ≤ (2 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12235 (p : Pattern) (guard : d4207 p = 1) : d1586 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12234 p hg
    simpa only [d4207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12208 p hg
    simpa only [d4207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12236 (p : Pattern) (guard : d4207 p = 1) : d1605 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1605, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12233 p hg
    simpa only [d1605, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1605, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12235 p hg
    simpa only [d1605, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12237 (p : Pattern) (guard : d4208 p = 1) : d1606 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12236 p hg
    simpa only [d4208, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12211 p hg
    simpa only [d4208, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12238 (p : Pattern) (guard : d0 p = 1) : d1578 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12239 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12240 (p : Pattern) (guard : d4206 p = 1) : d1053 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12239 p hg
    simpa only [d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12218 p hg
    simpa only [d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12241 (p : Pattern) (guard : d4206 p = 1) : d1054 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12240 p hg
    simpa only [d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12242 (p : Pattern) (guard : d4206 p = 1) : d1589 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12241 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12243 (p : Pattern) (guard : d4207 p = 1) : d1590 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12238 p hg
    simpa only [d4207, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12242 p hg
    simpa only [d4207, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12244 (p : Pattern) (guard : d4207 p = 1) : d1593 p ≤ (2 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12243 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12227 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12245 (p : Pattern) (guard : d4208 p = 1) : d1607 p ≤ (2 : Int) + d12 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12244 p hg
    simpa only [d4208, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4208, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12246 (p : Pattern) (guard : d4208 p = 1) : d1608 p ≤ (2 : Int) + d4972 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1608, d4972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12237 p hg
    simpa only [d1608, d4972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1608, d4972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12245 p hg
    simpa only [d1608, d4972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12247 (p : Pattern) (guard : d4208 p = 1) : d1609 p ≤ (2 : Int) + d4973 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1609, d4973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12231 p hg
    simpa only [d1609, d4973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1609, d4973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12246 p hg
    simpa only [d1609, d4973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12248 (p : Pattern) (guard : d4208 p = 1) : d1610 p ≤ (2 : Int) + d4974 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1610, d4974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12170 p hg
    simpa only [d1610, d4974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1610, d4974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12247 p hg
    simpa only [d1610, d4974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12249 (p : Pattern) (guard : d4208 p = 1) : d1611 p ≤ (2 : Int) + d4975 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1611, d4975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12188 p hg
    simpa only [d1611, d4975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1611, d4975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12248 p hg
    simpa only [d1611, d4975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12250 (p : Pattern) (guard : d0 p = 1) : d1531 p ≤ (2 : Int) + d189 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12251 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4691 p hg
    simpa only [d4206, d66, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12092 p hg
    simpa only [d4206, d66, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12252 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d35 p := by
  omega
theorem compare12253 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d36 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12254 (p : Pattern) (guard : d4206 p = 1) : d173 p ≤ (2 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d173, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12252 p hg
    simpa only [d4206, d173, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d173, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12253 p hg
    simpa only [d4206, d173, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12255 (p : Pattern) (guard : d4206 p = 1) : d176 p ≤ (2 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d176, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12108 p hg
    simpa only [d176, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d176, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12254 p hg
    simpa only [d176, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12256 (p : Pattern) (guard : d4206 p = 1) : d1612 p ≤ (2 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1612, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12251 p hg
    simpa only [d1612, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1612, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12255 p hg
    simpa only [d1612, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12257 (p : Pattern) (guard : d4206 p = 1) : d177 p ≤ (2 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d177, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12255 p hg
    simpa only [d177, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d177, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12118 p hg
    simpa only [d177, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12258 (p : Pattern) (guard : d4206 p = 1) : d1613 p ≤ (2 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1613, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12256 p hg
    simpa only [d1613, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1613, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12257 p hg
    simpa only [d1613, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12259 (p : Pattern) (guard : d4207 p = 1) : d1614 p ≤ (2 : Int) + d189 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12250 p hg
    simpa only [d4207, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12258 p hg
    simpa only [d4207, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12260 (p : Pattern) (guard : d0 p = 1) : d1520 p ≤ (2 : Int) + d200 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12261 (p : Pattern) (guard : d4206 p = 1) : d43 p ≤ (2 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d43, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4867 p hg
    simpa only [d4206, d43, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d43, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12107 p hg
    simpa only [d4206, d43, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12262 (p : Pattern) (guard : d4206 p = 1) : d1615 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12108 p hg
    simpa only [d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12261 p hg
    simpa only [d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12263 (p : Pattern) (guard : d4206 p = 1) : d173 p ≤ (2 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d173, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4699 p hg
    simpa only [d4206, d173, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d173, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12094 p hg
    simpa only [d4206, d173, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12264 (p : Pattern) (guard : d4206 p = 1) : d181 p ≤ (2 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d181, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12263 p hg
    simpa only [d181, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d181, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12117 p hg
    simpa only [d181, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12265 (p : Pattern) (guard : d4206 p = 1) : d1616 p ≤ (2 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1616, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12262 p hg
    simpa only [d1616, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1616, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12264 p hg
    simpa only [d1616, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12266 (p : Pattern) (guard : d4206 p = 1) : d183 p ≤ (2 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d183, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12254 p hg
    simpa only [d183, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d183, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d183, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12267 (p : Pattern) (guard : d4206 p = 1) : d184 p ≤ (2 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d184, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12266 p hg
    simpa only [d184, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d184, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d184, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12268 (p : Pattern) (guard : d4206 p = 1) : d1617 p ≤ (2 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1617, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12265 p hg
    simpa only [d1617, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1617, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12267 p hg
    simpa only [d1617, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12269 (p : Pattern) (guard : d4207 p = 1) : d1618 p ≤ (2 : Int) + d200 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12260 p hg
    simpa only [d4207, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12268 p hg
    simpa only [d4207, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12270 (p : Pattern) (guard : d4207 p = 1) : d1619 p ≤ (2 : Int) + d4745 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1619, d4745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12259 p hg
    simpa only [d1619, d4745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1619, d4745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12269 p hg
    simpa only [d1619, d4745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12271 (p : Pattern) (guard : d0 p = 1) : d1634 p ≤ (2 : Int) + d4745 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12272 (p : Pattern) (guard : d4208 p = 1) : d1635 p ≤ (2 : Int) + d4745 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12270 p hg
    simpa only [d4208, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12271 p hg
    simpa only [d4208, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12273 (p : Pattern) (guard : d0 p = 1) : d1621 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12274 (p : Pattern) (guard : d4206 p = 1) : d43 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4713 p hg
    simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12275 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d12 p := by
  change (8 : Int) ≤ (2 : Int) + 12
  decide
theorem compare12276 (p : Pattern) (guard : d1 p = 1) : d190 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12277 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12276 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12278 (p : Pattern) (guard : d4206 p = 1) : d1622 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12277 p hg
    simpa only [d4206, d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4206, d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12279 (p : Pattern) (guard : d4206 p = 1) : d1623 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12274 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12278 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12280 (p : Pattern) (guard : d4206 p = 1) : d1624 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12279 p hg
    simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12281 (p : Pattern) (guard : d4206 p = 1) : d1625 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12280 p hg
    simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12282 (p : Pattern) (guard : d4207 p = 1) : d1626 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12273 p hg
    simpa only [d4207, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12281 p hg
    simpa only [d4207, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12283 (p : Pattern) (guard : d0 p = 1) : d1629 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12284 (p : Pattern) (guard : d4206 p = 1) : d1630 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12278 p hg
    simpa only [d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12285 (p : Pattern) (guard : d4206 p = 1) : d1631 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12284 p hg
    simpa only [d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12286 (p : Pattern) (guard : d4206 p = 1) : d1632 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12285 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12287 (p : Pattern) (guard : d4207 p = 1) : d1633 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12283 p hg
    simpa only [d4207, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12286 p hg
    simpa only [d4207, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12288 (p : Pattern) (guard : d4207 p = 1) : d1634 p ≤ (2 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12282 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12287 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12289 (p : Pattern) (guard : d4208 p = 1) : d1636 p ≤ (2 : Int) + d12 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12288 p hg
    simpa only [d4208, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4208, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12290 (p : Pattern) (guard : d4208 p = 1) : d1637 p ≤ (2 : Int) + d4976 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1637, d4976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12272 p hg
    simpa only [d1637, d4976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1637, d4976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12289 p hg
    simpa only [d1637, d4976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12291 (p : Pattern) (guard : d4208 p = 1) : d1638 p ≤ (2 : Int) + d4977 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1638, d4977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12181 p hg
    simpa only [d1638, d4977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1638, d4977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12290 p hg
    simpa only [d1638, d4977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12292 (p : Pattern) (guard : d4208 p = 1) : d1639 p ≤ (2 : Int) + d4978 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1639, d4978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12170 p hg
    simpa only [d1639, d4978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1639, d4978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12291 p hg
    simpa only [d1639, d4978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12293 (p : Pattern) (guard : d0 p = 1) : d1641 p ≤ (2 : Int) + d214 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12294 (p : Pattern) (guard : d4206 p = 1) : d215 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d215, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12193 p hg
    simpa only [d215, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d215, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d215, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12295 (p : Pattern) (guard : d4206 p = 1) : d1642 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1642, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12203 p hg
    simpa only [d1642, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1642, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12294 p hg
    simpa only [d1642, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12296 (p : Pattern) (guard : d4206 p = 1) : d217 p ≤ (2 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d217, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12294 p hg
    simpa only [d217, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d217, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d217, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12297 (p : Pattern) (guard : d4206 p = 1) : d1643 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1643, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12295 p hg
    simpa only [d1643, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1643, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12296 p hg
    simpa only [d1643, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12298 (p : Pattern) (guard : d4207 p = 1) : d1644 p ≤ (2 : Int) + d214 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12293 p hg
    simpa only [d4207, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12297 p hg
    simpa only [d4207, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12299 (p : Pattern) (guard : d4207 p = 1) : d1645 p ≤ (2 : Int) + d4751 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1645, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12199 p hg
    simpa only [d1645, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1645, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12298 p hg
    simpa only [d1645, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12300 (p : Pattern) (guard : d0 p = 1) : d1647 p ≤ (2 : Int) + d4751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12301 (p : Pattern) (guard : d4208 p = 1) : d1648 p ≤ (2 : Int) + d4751 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12299 p hg
    simpa only [d4208, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12300 p hg
    simpa only [d4208, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12302 (p : Pattern) (guard : d0 p = 1) : d1643 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12303 (p : Pattern) (guard : d4207 p = 1) : d1646 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12302 p hg
    simpa only [d4207, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12226 p hg
    simpa only [d4207, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12304 (p : Pattern) (guard : d4207 p = 1) : d1647 p ≤ (2 : Int) + d4737 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1647, d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12222 p hg
    simpa only [d1647, d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1647, d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12303 p hg
    simpa only [d1647, d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12305 (p : Pattern) (guard : d4208 p = 1) : d1649 p ≤ (2 : Int) + d4737 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12304 p hg
    simpa only [d4208, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12229 p hg
    simpa only [d4208, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12306 (p : Pattern) (guard : d4208 p = 1) : d1650 p ≤ (2 : Int) + d4979 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1650, d4979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12301 p hg
    simpa only [d1650, d4979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1650, d4979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12305 p hg
    simpa only [d1650, d4979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12307 (p : Pattern) (guard : d0 p = 1) : d1603 p ≤ (2 : Int) + d243 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12308 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d139, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d4206, d139, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d139, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12190 p hg
    simpa only [d4206, d139, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12309 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d125, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d4206, d125, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d125, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12201 p hg
    simpa only [d4206, d125, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12310 (p : Pattern) (guard : d4206 p = 1) : d215 p ≤ (2 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d215, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12309 p hg
    simpa only [d215, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d215, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12130 p hg
    simpa only [d215, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12311 (p : Pattern) (guard : d4206 p = 1) : d1651 p ≤ (2 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1651, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12308 p hg
    simpa only [d1651, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1651, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12310 p hg
    simpa only [d1651, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12312 (p : Pattern) (guard : d4206 p = 1) : d229 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d229, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d4206, d229, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d229, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12192 p hg
    simpa only [d4206, d229, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12313 (p : Pattern) (guard : d4206 p = 1) : d230 p ≤ (2 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d230, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12312 p hg
    simpa only [d230, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d230, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12130 p hg
    simpa only [d230, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12314 (p : Pattern) (guard : d4206 p = 1) : d231 p ≤ (2 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d231, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12313 p hg
    simpa only [d231, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d231, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d231, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12315 (p : Pattern) (guard : d4206 p = 1) : d1652 p ≤ (2 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1652, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12311 p hg
    simpa only [d1652, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1652, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12314 p hg
    simpa only [d1652, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12316 (p : Pattern) (guard : d4207 p = 1) : d1653 p ≤ (2 : Int) + d243 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12307 p hg
    simpa only [d4207, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12315 p hg
    simpa only [d4207, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12317 (p : Pattern) (guard : d0 p = 1) : d1643 p ≤ (2 : Int) + d246 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12318 (p : Pattern) (guard : d4206 p = 1) : d230 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d230, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12312 p hg
    simpa only [d230, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d230, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d230, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12319 (p : Pattern) (guard : d4206 p = 1) : d1654 p ≤ (2 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1654, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12309 p hg
    simpa only [d1654, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1654, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12318 p hg
    simpa only [d1654, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
