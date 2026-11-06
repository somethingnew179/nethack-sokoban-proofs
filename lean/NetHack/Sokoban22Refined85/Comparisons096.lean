/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons095
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13440 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (2 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12202 p hg
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13439 p hg
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13441 (p : Pattern) (guard : d4206 p = 1) : d1651 p ≤ (2 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1651, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13440 p hg
    simpa only [d1651, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1651, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13428 p hg
    simpa only [d1651, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13442 (p : Pattern) (guard : d4206 p = 1) : d231 p ≤ (2 : Int) + d231 p := by
  omega
theorem compare13443 (p : Pattern) (guard : d4206 p = 1) : d1652 p ≤ (2 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1652, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13441 p hg
    simpa only [d1652, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1652, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13442 p hg
    simpa only [d1652, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13444 (p : Pattern) (guard : d4206 p = 1) : d1653 p ≤ (2 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1653, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13378 p hg
    simpa only [d1653, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1653, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13443 p hg
    simpa only [d1653, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13445 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (2 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d125, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d4206, d125, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d125, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12320 p hg
    simpa only [d4206, d125, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13446 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (2 : Int) + d125 p := by
  omega
theorem compare13447 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (2 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13445 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13446 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13448 (p : Pattern) (guard : d4206 p = 1) : d230 p ≤ (2 : Int) + d230 p := by
  omega
theorem compare13449 (p : Pattern) (guard : d4206 p = 1) : d1654 p ≤ (2 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1654, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13447 p hg
    simpa only [d1654, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1654, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13448 p hg
    simpa only [d1654, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13450 (p : Pattern) (guard : d4206 p = 1) : d237 p ≤ (2 : Int) + d237 p := by
  omega
theorem compare13451 (p : Pattern) (guard : d4206 p = 1) : d1655 p ≤ (2 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1655, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13449 p hg
    simpa only [d1655, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1655, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13450 p hg
    simpa only [d1655, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13452 (p : Pattern) (guard : d4206 p = 1) : d1656 p ≤ (2 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1656, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12297 p hg
    simpa only [d1656, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1656, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13451 p hg
    simpa only [d1656, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13453 (p : Pattern) (guard : d4206 p = 1) : d1657 p ≤ (2 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1657, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13444 p hg
    simpa only [d1657, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1657, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13452 p hg
    simpa only [d1657, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13454 (p : Pattern) (guard : d4206 p = 1) : d1658 p ≤ (2 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1658, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12202 p hg
    simpa only [d1658, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1658, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12117 p hg
    simpa only [d1658, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13455 (p : Pattern) (guard : d4206 p = 1) : d1659 p ≤ (2 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1659, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12191 p hg
    simpa only [d1659, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1659, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13454 p hg
    simpa only [d1659, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13456 (p : Pattern) (guard : d4206 p = 1) : d1660 p ≤ (2 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1660, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13455 p hg
    simpa only [d1660, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1660, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12207 p hg
    simpa only [d1660, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13457 (p : Pattern) (guard : d4206 p = 1) : d1661 p ≤ (2 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1661, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13456 p hg
    simpa only [d1661, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1661, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13366 p hg
    simpa only [d1661, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13458 (p : Pattern) (guard : d4206 p = 1) : d1651 p ≤ (2 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1651, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12202 p hg
    simpa only [d1651, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1651, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12294 p hg
    simpa only [d1651, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13459 (p : Pattern) (guard : d4206 p = 1) : d1652 p ≤ (2 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1652, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13458 p hg
    simpa only [d1652, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1652, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13365 p hg
    simpa only [d1652, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13460 (p : Pattern) (guard : d4206 p = 1) : d237 p ≤ (2 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d237, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12102 p hg
    simpa only [d237, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d237, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d237, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13461 (p : Pattern) (guard : d4206 p = 1) : d1662 p ≤ (2 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1662, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13460 p hg
    simpa only [d1662, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1662, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1662, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13462 (p : Pattern) (guard : d4206 p = 1) : d1663 p ≤ (2 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1663, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13459 p hg
    simpa only [d1663, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1663, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13461 p hg
    simpa only [d1663, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13463 (p : Pattern) (guard : d4206 p = 1) : d1664 p ≤ (2 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1664, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13457 p hg
    simpa only [d1664, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1664, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13462 p hg
    simpa only [d1664, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13464 (p : Pattern) (guard : d4206 p = 1) : d1665 p ≤ (2 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1665, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13453 p hg
    simpa only [d1665, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1665, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13463 p hg
    simpa only [d1665, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13465 (p : Pattern) (guard : d4206 p = 1) : d1666 p ≤ (2 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1666, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12202 p hg
    simpa only [d1666, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1666, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12100 p hg
    simpa only [d1666, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13466 (p : Pattern) (guard : d4206 p = 1) : d1667 p ≤ (2 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1667, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12191 p hg
    simpa only [d1667, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1667, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13465 p hg
    simpa only [d1667, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13467 (p : Pattern) (guard : d4206 p = 1) : d1668 p ≤ (2 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1668, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12193 p hg
    simpa only [d1668, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1668, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12100 p hg
    simpa only [d1668, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13468 (p : Pattern) (guard : d4206 p = 1) : d1669 p ≤ (2 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1669, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13467 p hg
    simpa only [d1669, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1669, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1669, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13469 (p : Pattern) (guard : d4206 p = 1) : d1670 p ≤ (2 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1670, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13466 p hg
    simpa only [d1670, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1670, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13468 p hg
    simpa only [d1670, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13470 (p : Pattern) (guard : d4206 p = 1) : d1671 p ≤ (2 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1671, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13359 p hg
    simpa only [d1671, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1671, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12117 p hg
    simpa only [d1671, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13471 (p : Pattern) (guard : d4206 p = 1) : d1672 p ≤ (2 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1672, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13470 p hg
    simpa only [d1672, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1672, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1672, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13472 (p : Pattern) (guard : d4206 p = 1) : d1673 p ≤ (2 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1673, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13471 p hg
    simpa only [d1673, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1673, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1673, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13473 (p : Pattern) (guard : d4206 p = 1) : d1674 p ≤ (2 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1674, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13469 p hg
    simpa only [d1674, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1674, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13472 p hg
    simpa only [d1674, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13474 (p : Pattern) (guard : d4206 p = 1) : d1675 p ≤ (2 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1675, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13473 p hg
    simpa only [d1675, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1675, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13462 p hg
    simpa only [d1675, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13475 (p : Pattern) (guard : d4206 p = 1) : d1676 p ≤ (2 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1676, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13474 p hg
    simpa only [d1676, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1676, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1676, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13476 (p : Pattern) (guard : d4206 p = 1) : d1677 p ≤ (2 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1677, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13464 p hg
    simpa only [d1677, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1677, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13475 p hg
    simpa only [d1677, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13477 (p : Pattern) (guard : d4206 p = 1) : d1678 p ≤ (2 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1678, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13438 p hg
    simpa only [d1678, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1678, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13476 p hg
    simpa only [d1678, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13478 (p : Pattern) (guard : d4206 p = 1) : d1679 p ≤ (2 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1679, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13309 p hg
    simpa only [d1679, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1679, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13477 p hg
    simpa only [d1679, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13479 (p : Pattern) (guard : d4206 p = 1) : d1680 p ≤ (2 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1680, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13425 p hg
    simpa only [d1680, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1680, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13478 p hg
    simpa only [d1680, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13480 (p : Pattern) (guard : d4206 p = 1) : d1681 p ≤ (2 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1681, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13387 p hg
    simpa only [d1681, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1681, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13479 p hg
    simpa only [d1681, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13481 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (0 : Int) + d362 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13482 (p : Pattern) (guard : d4763 p = 1) : d1510 p ≤ (0 : Int) + d790 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1510, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11867 p hg
    simpa only [d4763, d1510, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1510, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13481 p hg
    simpa only [d4763, d1510, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13483 (p : Pattern) (guard : d0 p = 1) : d1512 p ≤ (0 : Int) + d792 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13484 (p : Pattern) (guard : d4764 p = 1) : d1513 p ≤ (0 : Int) + d793 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1513, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13482 p hg
    simpa only [d4764, d1513, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1513, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13483 p hg
    simpa only [d4764, d1513, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13485 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (0 : Int) + d387 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13486 (p : Pattern) (guard : d4763 p = 1) : d1517 p ≤ (0 : Int) + d794 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1517, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11881 p hg
    simpa only [d4763, d1517, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1517, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13485 p hg
    simpa only [d4763, d1517, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13487 (p : Pattern) (guard : d0 p = 1) : d1520 p ≤ (0 : Int) + d800 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13488 (p : Pattern) (guard : d4764 p = 1) : d1521 p ≤ (0 : Int) + d801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1521, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13486 p hg
    simpa only [d4764, d1521, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1521, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13487 p hg
    simpa only [d4764, d1521, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13489 (p : Pattern) (guard : d4764 p = 1) : d1522 p ≤ (0 : Int) + d802 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1522, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13484 p hg
    simpa only [d1522, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1522, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13488 p hg
    simpa only [d1522, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13490 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13491 (p : Pattern) (guard : d4763 p = 1) : d1512 p ≤ (0 : Int) + d803 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1512, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11891 p hg
    simpa only [d4763, d1512, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1512, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13490 p hg
    simpa only [d4763, d1512, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13492 (p : Pattern) (guard : d0 p = 1) : d1523 p ≤ (0 : Int) + d805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13493 (p : Pattern) (guard : d4764 p = 1) : d1524 p ≤ (0 : Int) + d806 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1524, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13491 p hg
    simpa only [d4764, d1524, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1524, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13492 p hg
    simpa only [d4764, d1524, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13494 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13495 (p : Pattern) (guard : d4763 p = 1) : d1520 p ≤ (0 : Int) + d807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1520, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11896 p hg
    simpa only [d4763, d1520, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1520, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13494 p hg
    simpa only [d4763, d1520, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13496 (p : Pattern) (guard : d0 p = 1) : d1525 p ≤ (0 : Int) + d811 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13497 (p : Pattern) (guard : d4764 p = 1) : d1526 p ≤ (0 : Int) + d812 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1526, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13495 p hg
    simpa only [d4764, d1526, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1526, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13496 p hg
    simpa only [d4764, d1526, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13498 (p : Pattern) (guard : d4764 p = 1) : d1527 p ≤ (0 : Int) + d813 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1527, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13493 p hg
    simpa only [d1527, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1527, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13497 p hg
    simpa only [d1527, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13499 (p : Pattern) (guard : d4764 p = 1) : d1528 p ≤ (0 : Int) + d814 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1528, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13489 p hg
    simpa only [d1528, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1528, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13498 p hg
    simpa only [d1528, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13500 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13501 (p : Pattern) (guard : d4763 p = 1) : d1531 p ≤ (0 : Int) + d815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1531, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11903 p hg
    simpa only [d4763, d1531, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1531, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13500 p hg
    simpa only [d4763, d1531, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13502 (p : Pattern) (guard : d4764 p = 1) : d1532 p ≤ (0 : Int) + d816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1532, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13501 p hg
    simpa only [d4764, d1532, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1532, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13492 p hg
    simpa only [d4764, d1532, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13503 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13504 (p : Pattern) (guard : d4763 p = 1) : d1520 p ≤ (0 : Int) + d817 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1520, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11896 p hg
    simpa only [d4763, d1520, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1520, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13503 p hg
    simpa only [d4763, d1520, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13505 (p : Pattern) (guard : d4764 p = 1) : d1526 p ≤ (0 : Int) + d818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1526, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13504 p hg
    simpa only [d4764, d1526, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1526, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13496 p hg
    simpa only [d4764, d1526, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13506 (p : Pattern) (guard : d4764 p = 1) : d1533 p ≤ (0 : Int) + d819 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1533, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13502 p hg
    simpa only [d1533, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1533, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13505 p hg
    simpa only [d1533, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13507 (p : Pattern) (guard : d0 p = 1) : d1536 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13508 (p : Pattern) (guard : d4763 p = 1) : d1537 p ≤ (0 : Int) + d820 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1537, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11909 p hg
    simpa only [d4763, d1537, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1537, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13507 p hg
    simpa only [d4763, d1537, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13509 (p : Pattern) (guard : d0 p = 1) : d1538 p ≤ (0 : Int) + d93 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13510 (p : Pattern) (guard : d4764 p = 1) : d1539 p ≤ (0 : Int) + d821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1539, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13508 p hg
    simpa only [d4764, d1539, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1539, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13509 p hg
    simpa only [d4764, d1539, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13511 (p : Pattern) (guard : d4763 p = 1) : d1538 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11910 p hg
    simpa only [d4763, d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4763, d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13512 (p : Pattern) (guard : d4764 p = 1) : d1540 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13511 p hg
    simpa only [d4764, d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4764, d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13513 (p : Pattern) (guard : d4764 p = 1) : d1541 p ≤ (0 : Int) + d822 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1541, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13510 p hg
    simpa only [d1541, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1541, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13512 p hg
    simpa only [d1541, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13514 (p : Pattern) (guard : d4764 p = 1) : d1542 p ≤ (0 : Int) + d823 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1542, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13506 p hg
    simpa only [d1542, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1542, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13513 p hg
    simpa only [d1542, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13515 (p : Pattern) (guard : d4764 p = 1) : d1543 p ≤ (0 : Int) + d824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1543, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13499 p hg
    simpa only [d1543, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1543, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13514 p hg
    simpa only [d1543, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13516 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13517 (p : Pattern) (guard : d4763 p = 1) : d1546 p ≤ (0 : Int) + d825 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1546, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11920 p hg
    simpa only [d4763, d1546, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1546, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13516 p hg
    simpa only [d4763, d1546, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13518 (p : Pattern) (guard : d0 p = 1) : d1512 p ≤ (0 : Int) + d826 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13519 (p : Pattern) (guard : d4764 p = 1) : d1547 p ≤ (0 : Int) + d827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1547, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13517 p hg
    simpa only [d4764, d1547, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1547, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13518 p hg
    simpa only [d4764, d1547, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13520 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13521 (p : Pattern) (guard : d4763 p = 1) : d1520 p ≤ (0 : Int) + d828 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1520, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11896 p hg
    simpa only [d4763, d1520, d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1520, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13520 p hg
    simpa only [d4763, d1520, d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13522 (p : Pattern) (guard : d4764 p = 1) : d1520 p ≤ (0 : Int) + d829 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13521 p hg
    simpa only [d4764, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13487 p hg
    simpa only [d4764, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13523 (p : Pattern) (guard : d4764 p = 1) : d1548 p ≤ (0 : Int) + d830 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1548, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13519 p hg
    simpa only [d1548, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1548, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13522 p hg
    simpa only [d1548, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13524 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13525 (p : Pattern) (guard : d4763 p = 1) : d1512 p ≤ (0 : Int) + d831 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1512, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11891 p hg
    simpa only [d4763, d1512, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1512, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13524 p hg
    simpa only [d4763, d1512, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13526 (p : Pattern) (guard : d4764 p = 1) : d1524 p ≤ (0 : Int) + d832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1524, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13525 p hg
    simpa only [d4764, d1524, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1524, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13492 p hg
    simpa only [d4764, d1524, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13527 (p : Pattern) (guard : d4764 p = 1) : d1527 p ≤ (0 : Int) + d833 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1527, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13526 p hg
    simpa only [d1527, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1527, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13497 p hg
    simpa only [d1527, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13528 (p : Pattern) (guard : d4764 p = 1) : d1549 p ≤ (0 : Int) + d834 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1549, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13523 p hg
    simpa only [d1549, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1549, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13527 p hg
    simpa only [d1549, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13529 (p : Pattern) (guard : d4764 p = 1) : d1550 p ≤ (0 : Int) + d835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1550, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13527 p hg
    simpa only [d1550, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1550, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d1550, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13530 (p : Pattern) (guard : d4764 p = 1) : d1551 p ≤ (0 : Int) + d836 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1551, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13528 p hg
    simpa only [d1551, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1551, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13529 p hg
    simpa only [d1551, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13531 (p : Pattern) (guard : d4764 p = 1) : d1552 p ≤ (0 : Int) + d837 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1552, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13515 p hg
    simpa only [d1552, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1552, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13530 p hg
    simpa only [d1552, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13532 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (0 : Int) + d372 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13533 (p : Pattern) (guard : d4763 p = 1) : d1556 p ≤ (0 : Int) + d838 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1556, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11937 p hg
    simpa only [d4763, d1556, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1556, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13532 p hg
    simpa only [d4763, d1556, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13534 (p : Pattern) (guard : d4764 p = 1) : d1557 p ≤ (0 : Int) + d839 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1557, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13533 p hg
    simpa only [d4764, d1557, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1557, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13518 p hg
    simpa only [d4764, d1557, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13535 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13536 (p : Pattern) (guard : d4763 p = 1) : d1560 p ≤ (0 : Int) + d840 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1560, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11942 p hg
    simpa only [d4763, d1560, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1560, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13535 p hg
    simpa only [d4763, d1560, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13537 (p : Pattern) (guard : d4764 p = 1) : d1561 p ≤ (0 : Int) + d841 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1561, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13536 p hg
    simpa only [d4764, d1561, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1561, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13487 p hg
    simpa only [d4764, d1561, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13538 (p : Pattern) (guard : d4764 p = 1) : d1562 p ≤ (0 : Int) + d842 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1562, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13534 p hg
    simpa only [d1562, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1562, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13537 p hg
    simpa only [d1562, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13539 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13540 (p : Pattern) (guard : d4763 p = 1) : d1512 p ≤ (0 : Int) + d843 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1512, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11891 p hg
    simpa only [d4763, d1512, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1512, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13539 p hg
    simpa only [d4763, d1512, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13541 (p : Pattern) (guard : d4764 p = 1) : d1524 p ≤ (0 : Int) + d844 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1524, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13540 p hg
    simpa only [d4764, d1524, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1524, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13492 p hg
    simpa only [d4764, d1524, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13542 (p : Pattern) (guard : d4764 p = 1) : d1527 p ≤ (0 : Int) + d845 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1527, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13541 p hg
    simpa only [d1527, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1527, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13497 p hg
    simpa only [d1527, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13543 (p : Pattern) (guard : d4764 p = 1) : d1563 p ≤ (0 : Int) + d846 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1563, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13538 p hg
    simpa only [d1563, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1563, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13542 p hg
    simpa only [d1563, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13544 (p : Pattern) (guard : d4764 p = 1) : d1564 p ≤ (0 : Int) + d847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1564, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13498 p hg
    simpa only [d1564, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1564, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13513 p hg
    simpa only [d1564, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13545 (p : Pattern) (guard : d4764 p = 1) : d1565 p ≤ (0 : Int) + d848 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1565, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13543 p hg
    simpa only [d1565, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1565, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13544 p hg
    simpa only [d1565, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13546 (p : Pattern) (guard : d4764 p = 1) : d1566 p ≤ (0 : Int) + d849 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1566, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13501 p hg
    simpa only [d4764, d1566, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1566, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13518 p hg
    simpa only [d4764, d1566, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13547 (p : Pattern) (guard : d4764 p = 1) : d1520 p ≤ (0 : Int) + d850 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13504 p hg
    simpa only [d4764, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13487 p hg
    simpa only [d4764, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13548 (p : Pattern) (guard : d4764 p = 1) : d1567 p ≤ (0 : Int) + d851 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1567, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13546 p hg
    simpa only [d1567, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1567, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13547 p hg
    simpa only [d1567, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13549 (p : Pattern) (guard : d4764 p = 1) : d1568 p ≤ (0 : Int) + d852 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1568, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13548 p hg
    simpa only [d1568, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1568, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13527 p hg
    simpa only [d1568, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13550 (p : Pattern) (guard : d4764 p = 1) : d1569 p ≤ (0 : Int) + d853 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1569, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13549 p hg
    simpa only [d1569, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1569, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13529 p hg
    simpa only [d1569, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13551 (p : Pattern) (guard : d4764 p = 1) : d1570 p ≤ (0 : Int) + d854 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1570, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13545 p hg
    simpa only [d1570, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1570, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13550 p hg
    simpa only [d1570, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13552 (p : Pattern) (guard : d4764 p = 1) : d1571 p ≤ (0 : Int) + d855 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1571, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13531 p hg
    simpa only [d1571, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1571, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13551 p hg
    simpa only [d1571, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13553 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d372 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13554 (p : Pattern) (guard : d4763 p = 1) : d1576 p ≤ (0 : Int) + d856 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1576, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11967 p hg
    simpa only [d4763, d1576, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1576, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13553 p hg
    simpa only [d4763, d1576, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13555 (p : Pattern) (guard : d0 p = 1) : d1578 p ≤ (0 : Int) + d858 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13556 (p : Pattern) (guard : d4764 p = 1) : d1579 p ≤ (0 : Int) + d859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1579, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13554 p hg
    simpa only [d4764, d1579, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1579, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13555 p hg
    simpa only [d4764, d1579, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13557 (p : Pattern) (guard : d0 p = 1) : d144 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13558 (p : Pattern) (guard : d4763 p = 1) : d1583 p ≤ (0 : Int) + d860 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1583, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11978 p hg
    simpa only [d4763, d1583, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1583, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13557 p hg
    simpa only [d4763, d1583, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13559 (p : Pattern) (guard : d0 p = 1) : d1586 p ≤ (0 : Int) + d865 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13560 (p : Pattern) (guard : d4764 p = 1) : d1587 p ≤ (0 : Int) + d866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1587, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13558 p hg
    simpa only [d4764, d1587, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1587, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13559 p hg
    simpa only [d4764, d1587, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13561 (p : Pattern) (guard : d4764 p = 1) : d1588 p ≤ (0 : Int) + d867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1588, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13556 p hg
    simpa only [d1588, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1588, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13560 p hg
    simpa only [d1588, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13562 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13563 (p : Pattern) (guard : d4763 p = 1) : d1578 p ≤ (0 : Int) + d868 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1578, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11985 p hg
    simpa only [d4763, d1578, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1578, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13562 p hg
    simpa only [d4763, d1578, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13564 (p : Pattern) (guard : d0 p = 1) : d1589 p ≤ (0 : Int) + d870 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13565 (p : Pattern) (guard : d4764 p = 1) : d1590 p ≤ (0 : Int) + d871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1590, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13563 p hg
    simpa only [d4764, d1590, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1590, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13564 p hg
    simpa only [d4764, d1590, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13566 (p : Pattern) (guard : d0 p = 1) : d144 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13567 (p : Pattern) (guard : d4763 p = 1) : d1586 p ≤ (0 : Int) + d872 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1586, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11990 p hg
    simpa only [d4763, d1586, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1586, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13566 p hg
    simpa only [d4763, d1586, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13568 (p : Pattern) (guard : d0 p = 1) : d1591 p ≤ (0 : Int) + d875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13569 (p : Pattern) (guard : d4764 p = 1) : d1592 p ≤ (0 : Int) + d876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1592, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13567 p hg
    simpa only [d4764, d1592, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1592, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13568 p hg
    simpa only [d4764, d1592, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13570 (p : Pattern) (guard : d4764 p = 1) : d1593 p ≤ (0 : Int) + d877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1593, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13565 p hg
    simpa only [d1593, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1593, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13569 p hg
    simpa only [d1593, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13571 (p : Pattern) (guard : d4764 p = 1) : d1594 p ≤ (0 : Int) + d878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1594, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13561 p hg
    simpa only [d1594, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1594, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13570 p hg
    simpa only [d1594, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13572 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13573 (p : Pattern) (guard : d4763 p = 1) : d1578 p ≤ (0 : Int) + d879 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1578, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11985 p hg
    simpa only [d4763, d1578, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1578, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13572 p hg
    simpa only [d4763, d1578, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13574 (p : Pattern) (guard : d4764 p = 1) : d1590 p ≤ (0 : Int) + d880 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1590, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13573 p hg
    simpa only [d4764, d1590, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1590, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13564 p hg
    simpa only [d4764, d1590, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13575 (p : Pattern) (guard : d4764 p = 1) : d1593 p ≤ (0 : Int) + d881 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1593, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13574 p hg
    simpa only [d1593, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1593, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13569 p hg
    simpa only [d1593, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13576 (p : Pattern) (guard : d4763 p = 1) : d1596 p ≤ (0 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11999 p hg
    simpa only [d4763, d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4763, d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13577 (p : Pattern) (guard : d4764 p = 1) : d1597 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13576 p hg
    simpa only [d4764, d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4764, d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13578 (p : Pattern) (guard : d4764 p = 1) : d1598 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13577 p hg
    simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13579 (p : Pattern) (guard : d4764 p = 1) : d1599 p ≤ (0 : Int) + d882 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1599, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13575 p hg
    simpa only [d1599, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1599, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13578 p hg
    simpa only [d1599, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
