/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons108
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15260 (p : Pattern) (guard : d0 p = 1) : d1687 p ≤ (0 : Int) + d324 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15261 (p : Pattern) (guard : d4967 p = 1) : d1688 p ≤ (0 : Int) + d1504 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1688, d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15259 p hg
    simpa only [d4967, d1688, d1504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1688, d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15260 p hg
    simpa only [d4967, d1688, d1504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15262 (p : Pattern) (guard : d0 p = 1) : d333 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15263 (p : Pattern) (guard : d4474 p = 1) : d1689 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15262 p hg
    simpa only [d4474, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15264 (p : Pattern) (guard : d0 p = 1) : d1687 p ≤ (0 : Int) + d336 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15265 (p : Pattern) (guard : d4967 p = 1) : d1690 p ≤ (0 : Int) + d1505 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1690, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15263 p hg
    simpa only [d4967, d1690, d1505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1690, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15264 p hg
    simpa only [d4967, d1690, d1505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15266 (p : Pattern) (guard : d4967 p = 1) : d1691 p ≤ (0 : Int) + d1506 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1691, d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15261 p hg
    simpa only [d1691, d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1691, d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15265 p hg
    simpa only [d1691, d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15267 (p : Pattern) (guard : d0 p = 1) : d1687 p ≤ (0 : Int) + d343 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15268 (p : Pattern) (guard : d4967 p = 1) : d1692 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1692, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1692, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1692, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15267 p hg
    simpa only [d4967, d1692, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15269 (p : Pattern) (guard : d0 p = 1) : d1697 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15270 (p : Pattern) (guard : d4967 p = 1) : d1698 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1698, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d4967, d1698, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1698, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15269 p hg
    simpa only [d4967, d1698, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15271 (p : Pattern) (guard : d4967 p = 1) : d1699 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1699, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15268 p hg
    simpa only [d1699, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1699, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15270 p hg
    simpa only [d1699, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15272 (p : Pattern) (guard : d4967 p = 1) : d1700 p ≤ (0 : Int) + d1509 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1700, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15266 p hg
    simpa only [d1700, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1700, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15271 p hg
    simpa only [d1700, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15273 (p : Pattern) (guard : d0 p = 1) : d1687 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15274 (p : Pattern) (guard : d4967 p = 1) : d1692 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1692, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1692, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1692, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15273 p hg
    simpa only [d4967, d1692, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15275 (p : Pattern) (guard : d4967 p = 1) : d1699 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1699, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15274 p hg
    simpa only [d1699, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1699, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15270 p hg
    simpa only [d1699, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15276 (p : Pattern) (guard : d0 p = 1) : d1705 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15277 (p : Pattern) (guard : d4967 p = 1) : d1706 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1706, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5668 p hg
    simpa only [d4967, d1706, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1706, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15276 p hg
    simpa only [d4967, d1706, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15278 (p : Pattern) (guard : d4967 p = 1) : d1707 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1707, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15277 p hg
    simpa only [d1707, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1707, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1707, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15279 (p : Pattern) (guard : d4967 p = 1) : d1708 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1708, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15275 p hg
    simpa only [d1708, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1708, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15278 p hg
    simpa only [d1708, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15280 (p : Pattern) (guard : d4967 p = 1) : d1709 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1709, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15272 p hg
    simpa only [d1709, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1709, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15279 p hg
    simpa only [d1709, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15281 (p : Pattern) (guard : d0 p = 1) : d1718 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15282 (p : Pattern) (guard : d4967 p = 1) : d1719 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1719, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1719, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1719, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d4967, d1719, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15283 (p : Pattern) (guard : d0 p = 1) : d1725 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15284 (p : Pattern) (guard : d4967 p = 1) : d1726 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1726, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1726, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1726, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d4967, d1726, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15285 (p : Pattern) (guard : d4967 p = 1) : d1727 p ≤ (0 : Int) + d46 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15282 p hg
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15284 p hg
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15286 (p : Pattern) (guard : d0 p = 1) : d1730 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15287 (p : Pattern) (guard : d4967 p = 1) : d1731 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1731, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1731, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1731, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d4967, d1731, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15288 (p : Pattern) (guard : d4967 p = 1) : d1732 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1732, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d4967, d1732, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1732, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d1732, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15289 (p : Pattern) (guard : d4967 p = 1) : d1733 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1733, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15287 p hg
    simpa only [d1733, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1733, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15288 p hg
    simpa only [d1733, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15290 (p : Pattern) (guard : d4967 p = 1) : d1734 p ≤ (0 : Int) + d1511 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1734, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15285 p hg
    simpa only [d1734, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1734, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15289 p hg
    simpa only [d1734, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15291 (p : Pattern) (guard : d4967 p = 1) : d1735 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1735, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1735, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1735, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d1735, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15292 (p : Pattern) (guard : d4967 p = 1) : d1736 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1736, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15291 p hg
    simpa only [d1736, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1736, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15288 p hg
    simpa only [d1736, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15293 (p : Pattern) (guard : d4967 p = 1) : d527 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d527, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5668 p hg
    simpa only [d4967, d527, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d527, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d527, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15294 (p : Pattern) (guard : d4967 p = 1) : d528 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d528, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15293 p hg
    simpa only [d528, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d528, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d528, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15295 (p : Pattern) (guard : d4967 p = 1) : d1737 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1737, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15292 p hg
    simpa only [d1737, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1737, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15294 p hg
    simpa only [d1737, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15296 (p : Pattern) (guard : d4967 p = 1) : d1738 p ≤ (0 : Int) + d1512 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1738, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15290 p hg
    simpa only [d1738, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1738, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15295 p hg
    simpa only [d1738, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15297 (p : Pattern) (guard : d4967 p = 1) : d1739 p ≤ (0 : Int) + d1513 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1739, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15280 p hg
    simpa only [d1739, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1739, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15296 p hg
    simpa only [d1739, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15298 (p : Pattern) (guard : d0 p = 1) : d335 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15299 (p : Pattern) (guard : d4474 p = 1) : d1740 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15298 p hg
    simpa only [d4474, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15300 (p : Pattern) (guard : d0 p = 1) : d1687 p ≤ (0 : Int) + d359 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15301 (p : Pattern) (guard : d4967 p = 1) : d1741 p ≤ (0 : Int) + d1514 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1741, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15299 p hg
    simpa only [d4967, d1741, d1514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1741, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15300 p hg
    simpa only [d4967, d1741, d1514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15302 (p : Pattern) (guard : d0 p = 1) : d1746 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15303 (p : Pattern) (guard : d4967 p = 1) : d1747 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1747, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d1747, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1747, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15302 p hg
    simpa only [d4967, d1747, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15304 (p : Pattern) (guard : d4967 p = 1) : d1748 p ≤ (0 : Int) + d1515 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1748, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15301 p hg
    simpa only [d1748, d1515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1748, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15303 p hg
    simpa only [d1748, d1515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15305 (p : Pattern) (guard : d4967 p = 1) : d1749 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1749, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15270 p hg
    simpa only [d1749, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1749, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15277 p hg
    simpa only [d1749, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15306 (p : Pattern) (guard : d4967 p = 1) : d1750 p ≤ (0 : Int) + d1516 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1750, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15304 p hg
    simpa only [d1750, d1516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1750, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15305 p hg
    simpa only [d1750, d1516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15307 (p : Pattern) (guard : d0 p = 1) : d1753 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15308 (p : Pattern) (guard : d4967 p = 1) : d1754 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1754, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5685 p hg
    simpa only [d4967, d1754, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1754, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15307 p hg
    simpa only [d4967, d1754, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15309 (p : Pattern) (guard : d4967 p = 1) : d1755 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1755, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15270 p hg
    simpa only [d1755, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1755, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15308 p hg
    simpa only [d1755, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15310 (p : Pattern) (guard : d4967 p = 1) : d1756 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1756, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d4967, d1756, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1756, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d4967, d1756, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15311 (p : Pattern) (guard : d4967 p = 1) : d1757 p ≤ (0 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1757, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15310 p hg
    simpa only [d1757, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1757, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1757, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15312 (p : Pattern) (guard : d4967 p = 1) : d1758 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1758, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15309 p hg
    simpa only [d1758, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1758, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15311 p hg
    simpa only [d1758, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15313 (p : Pattern) (guard : d4967 p = 1) : d1759 p ≤ (0 : Int) + d1517 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1759, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15306 p hg
    simpa only [d1759, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1759, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15312 p hg
    simpa only [d1759, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15314 (p : Pattern) (guard : d4967 p = 1) : d1760 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1760, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d1760, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1760, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d1760, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15315 (p : Pattern) (guard : d4967 p = 1) : d1761 p ≤ (0 : Int) + d1518 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1761, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15284 p hg
    simpa only [d1761, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1761, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15314 p hg
    simpa only [d1761, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15316 (p : Pattern) (guard : d4967 p = 1) : d1762 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1762, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15288 p hg
    simpa only [d1762, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1762, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15293 p hg
    simpa only [d1762, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15317 (p : Pattern) (guard : d4967 p = 1) : d1763 p ≤ (0 : Int) + d1519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1763, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15315 p hg
    simpa only [d1763, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1763, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15316 p hg
    simpa only [d1763, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15318 (p : Pattern) (guard : d4967 p = 1) : d277 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5685 p hg
    simpa only [d4967, d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15319 (p : Pattern) (guard : d4967 p = 1) : d1764 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1764, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15288 p hg
    simpa only [d1764, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1764, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15318 p hg
    simpa only [d1764, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15320 (p : Pattern) (guard : d4967 p = 1) : d538 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d538, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d4967, d538, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d538, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d538, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15321 (p : Pattern) (guard : d4967 p = 1) : d539 p ≤ (0 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d539, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15320 p hg
    simpa only [d539, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d539, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d539, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15322 (p : Pattern) (guard : d4967 p = 1) : d1765 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1765, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15319 p hg
    simpa only [d1765, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1765, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15321 p hg
    simpa only [d1765, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15323 (p : Pattern) (guard : d4967 p = 1) : d1766 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1766, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15317 p hg
    simpa only [d1766, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1766, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15322 p hg
    simpa only [d1766, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15324 (p : Pattern) (guard : d4967 p = 1) : d1767 p ≤ (0 : Int) + d1521 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1767, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15313 p hg
    simpa only [d1767, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1767, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15323 p hg
    simpa only [d1767, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15325 (p : Pattern) (guard : d4967 p = 1) : d1768 p ≤ (0 : Int) + d1522 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1768, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15297 p hg
    simpa only [d1768, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1768, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15324 p hg
    simpa only [d1768, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15326 (p : Pattern) (guard : d0 p = 1) : d1773 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15327 (p : Pattern) (guard : d4967 p = 1) : d1774 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1774, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1774, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1774, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15326 p hg
    simpa only [d4967, d1774, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15328 (p : Pattern) (guard : d0 p = 1) : d1782 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15329 (p : Pattern) (guard : d4967 p = 1) : d1783 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1783, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1783, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1783, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15328 p hg
    simpa only [d4967, d1783, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15330 (p : Pattern) (guard : d4967 p = 1) : d1784 p ≤ (0 : Int) + d46 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15327 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15329 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15331 (p : Pattern) (guard : d0 p = 1) : d1789 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15332 (p : Pattern) (guard : d4967 p = 1) : d1790 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1790, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1790, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1790, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15331 p hg
    simpa only [d4967, d1790, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15333 (p : Pattern) (guard : d0 p = 1) : d1798 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15334 (p : Pattern) (guard : d4967 p = 1) : d1799 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1799, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d4967, d1799, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1799, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15333 p hg
    simpa only [d4967, d1799, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15335 (p : Pattern) (guard : d4967 p = 1) : d1800 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1800, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15332 p hg
    simpa only [d1800, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1800, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15334 p hg
    simpa only [d1800, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15336 (p : Pattern) (guard : d4967 p = 1) : d1801 p ≤ (0 : Int) + d1511 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1801, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15330 p hg
    simpa only [d1801, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1801, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15335 p hg
    simpa only [d1801, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15337 (p : Pattern) (guard : d0 p = 1) : d1804 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15338 (p : Pattern) (guard : d4967 p = 1) : d1805 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1805, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5668 p hg
    simpa only [d4967, d1805, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1805, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15337 p hg
    simpa only [d4967, d1805, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15339 (p : Pattern) (guard : d4967 p = 1) : d1806 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1806, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15338 p hg
    simpa only [d1806, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1806, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1806, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15340 (p : Pattern) (guard : d4967 p = 1) : d1807 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1807, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15335 p hg
    simpa only [d1807, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1807, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15339 p hg
    simpa only [d1807, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15341 (p : Pattern) (guard : d4967 p = 1) : d1808 p ≤ (0 : Int) + d1512 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1808, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15336 p hg
    simpa only [d1808, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1808, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15340 p hg
    simpa only [d1808, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15342 (p : Pattern) (guard : d4967 p = 1) : d1809 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1809, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d1809, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1809, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d4967, d1809, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15343 (p : Pattern) (guard : d4967 p = 1) : d1810 p ≤ (0 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1810, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d4967, d1810, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1810, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d4967, d1810, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15344 (p : Pattern) (guard : d4967 p = 1) : d1811 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1811, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15342 p hg
    simpa only [d1811, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1811, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15343 p hg
    simpa only [d1811, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15345 (p : Pattern) (guard : d4967 p = 1) : d1812 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1812, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15344 p hg
    simpa only [d1812, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1812, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15311 p hg
    simpa only [d1812, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15346 (p : Pattern) (guard : d4967 p = 1) : d1813 p ≤ (0 : Int) + d1523 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1813, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15345 p hg
    simpa only [d1813, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1813, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1813, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15347 (p : Pattern) (guard : d4967 p = 1) : d1814 p ≤ (0 : Int) + d1524 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1814, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15341 p hg
    simpa only [d1814, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1814, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15346 p hg
    simpa only [d1814, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15348 (p : Pattern) (guard : d4967 p = 1) : d1815 p ≤ (0 : Int) + d1518 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1815, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15329 p hg
    simpa only [d1815, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1815, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15342 p hg
    simpa only [d1815, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15349 (p : Pattern) (guard : d4967 p = 1) : d1816 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1816, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15334 p hg
    simpa only [d1816, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1816, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15338 p hg
    simpa only [d1816, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15350 (p : Pattern) (guard : d4967 p = 1) : d1817 p ≤ (0 : Int) + d1519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1817, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15348 p hg
    simpa only [d1817, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1817, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15349 p hg
    simpa only [d1817, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15351 (p : Pattern) (guard : d4967 p = 1) : d1818 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1818, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15334 p hg
    simpa only [d1818, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1818, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15308 p hg
    simpa only [d1818, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15352 (p : Pattern) (guard : d4967 p = 1) : d1819 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1819, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15351 p hg
    simpa only [d1819, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1819, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15311 p hg
    simpa only [d1819, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15353 (p : Pattern) (guard : d4967 p = 1) : d1820 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1820, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15350 p hg
    simpa only [d1820, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1820, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15352 p hg
    simpa only [d1820, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15354 (p : Pattern) (guard : d4967 p = 1) : d1821 p ≤ (0 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1821, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15343 p hg
    simpa only [d1821, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1821, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1821, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15355 (p : Pattern) (guard : d4967 p = 1) : d1822 p ≤ (0 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1822, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15354 p hg
    simpa only [d1822, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1822, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1822, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15356 (p : Pattern) (guard : d4967 p = 1) : d1823 p ≤ (0 : Int) + d1525 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1823, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15355 p hg
    simpa only [d1823, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1823, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1823, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15357 (p : Pattern) (guard : d4967 p = 1) : d1824 p ≤ (0 : Int) + d1526 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1824, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15353 p hg
    simpa only [d1824, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1824, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15356 p hg
    simpa only [d1824, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15358 (p : Pattern) (guard : d4967 p = 1) : d1825 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1825, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15347 p hg
    simpa only [d1825, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1825, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15357 p hg
    simpa only [d1825, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15359 (p : Pattern) (guard : d4967 p = 1) : d1826 p ≤ (0 : Int) + d1528 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1826, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15325 p hg
    simpa only [d1826, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1826, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15358 p hg
    simpa only [d1826, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15360 (p : Pattern) (guard : d0 p = 1) : d1773 p ≤ (0 : Int) + d343 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15361 (p : Pattern) (guard : d4967 p = 1) : d1774 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1774, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1774, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1774, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15360 p hg
    simpa only [d4967, d1774, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15362 (p : Pattern) (guard : d4967 p = 1) : d1784 p ≤ (0 : Int) + d1529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1784, d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15361 p hg
    simpa only [d1784, d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1784, d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15329 p hg
    simpa only [d1784, d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15363 (p : Pattern) (guard : d4967 p = 1) : d1801 p ≤ (0 : Int) + d1530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1801, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15362 p hg
    simpa only [d1801, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1801, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15335 p hg
    simpa only [d1801, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15364 (p : Pattern) (guard : d4967 p = 1) : d1808 p ≤ (0 : Int) + d1531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1808, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15363 p hg
    simpa only [d1808, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1808, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15340 p hg
    simpa only [d1808, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15365 (p : Pattern) (guard : d4967 p = 1) : d1814 p ≤ (0 : Int) + d1532 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1814, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15364 p hg
    simpa only [d1814, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1814, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15346 p hg
    simpa only [d1814, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15366 (p : Pattern) (guard : d4967 p = 1) : d1825 p ≤ (0 : Int) + d1533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1825, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15365 p hg
    simpa only [d1825, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1825, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15357 p hg
    simpa only [d1825, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15367 (p : Pattern) (guard : d4967 p = 1) : d1827 p ≤ (0 : Int) + d1534 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1827, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15338 p hg
    simpa only [d1827, d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1827, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15310 p hg
    simpa only [d1827, d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15368 (p : Pattern) (guard : d4967 p = 1) : d1828 p ≤ (0 : Int) + d1535 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1828, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15367 p hg
    simpa only [d1828, d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1828, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15311 p hg
    simpa only [d1828, d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15369 (p : Pattern) (guard : d4967 p = 1) : d1829 p ≤ (0 : Int) + d1536 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1829, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15311 p hg
    simpa only [d1829, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1829, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1829, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15370 (p : Pattern) (guard : d4967 p = 1) : d1830 p ≤ (0 : Int) + d1537 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1830, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15368 p hg
    simpa only [d1830, d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1830, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15369 p hg
    simpa only [d1830, d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15371 (p : Pattern) (guard : d4967 p = 1) : d1831 p ≤ (0 : Int) + d1538 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1831, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15369 p hg
    simpa only [d1831, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1831, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1831, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15372 (p : Pattern) (guard : d4967 p = 1) : d1832 p ≤ (0 : Int) + d1539 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1832, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15370 p hg
    simpa only [d1832, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1832, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15371 p hg
    simpa only [d1832, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15373 (p : Pattern) (guard : d4967 p = 1) : d1833 p ≤ (0 : Int) + d1540 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1833, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15371 p hg
    simpa only [d1833, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1833, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1833, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15374 (p : Pattern) (guard : d4967 p = 1) : d1834 p ≤ (0 : Int) + d1541 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1834, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15372 p hg
    simpa only [d1834, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1834, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15373 p hg
    simpa only [d1834, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15375 (p : Pattern) (guard : d4967 p = 1) : d1835 p ≤ (0 : Int) + d1542 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1835, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15366 p hg
    simpa only [d1835, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1835, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15374 p hg
    simpa only [d1835, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15376 (p : Pattern) (guard : d4967 p = 1) : d1836 p ≤ (0 : Int) + d1543 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1836, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15359 p hg
    simpa only [d1836, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1836, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15375 p hg
    simpa only [d1836, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15377 (p : Pattern) (guard : d4967 p = 1) : d1837 p ≤ (0 : Int) + d1544 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1837, d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15265 p hg
    simpa only [d1837, d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1837, d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15274 p hg
    simpa only [d1837, d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15378 (p : Pattern) (guard : d4967 p = 1) : d1838 p ≤ (0 : Int) + d1545 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1838, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15377 p hg
    simpa only [d1838, d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1838, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15275 p hg
    simpa only [d1838, d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15379 (p : Pattern) (guard : d4967 p = 1) : d1839 p ≤ (0 : Int) + d1546 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1839, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15378 p hg
    simpa only [d1839, d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1839, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15279 p hg
    simpa only [d1839, d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15380 (p : Pattern) (guard : d4967 p = 1) : d1840 p ≤ (0 : Int) + d1547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1840, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15379 p hg
    simpa only [d1840, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1840, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15296 p hg
    simpa only [d1840, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15381 (p : Pattern) (guard : d4967 p = 1) : d1841 p ≤ (0 : Int) + d1518 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1841, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15274 p hg
    simpa only [d1841, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1841, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15303 p hg
    simpa only [d1841, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15382 (p : Pattern) (guard : d4967 p = 1) : d1842 p ≤ (0 : Int) + d1519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1842, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15381 p hg
    simpa only [d1842, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1842, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15305 p hg
    simpa only [d1842, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15383 (p : Pattern) (guard : d4967 p = 1) : d1843 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1843, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15382 p hg
    simpa only [d1843, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1843, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15312 p hg
    simpa only [d1843, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15384 (p : Pattern) (guard : d4967 p = 1) : d1844 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15383 p hg
    simpa only [d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15323 p hg
    simpa only [d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15385 (p : Pattern) (guard : d4967 p = 1) : d1845 p ≤ (0 : Int) + d1548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1845, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15380 p hg
    simpa only [d1845, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1845, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15384 p hg
    simpa only [d1845, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15386 (p : Pattern) (guard : d4967 p = 1) : d1846 p ≤ (0 : Int) + d1549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1846, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15385 p hg
    simpa only [d1846, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1846, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15358 p hg
    simpa only [d1846, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15387 (p : Pattern) (guard : d4967 p = 1) : d1847 p ≤ (0 : Int) + d1550 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1847, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15358 p hg
    simpa only [d1847, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1847, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1847, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15388 (p : Pattern) (guard : d4967 p = 1) : d1848 p ≤ (0 : Int) + d1551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1848, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15386 p hg
    simpa only [d1848, d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1848, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15387 p hg
    simpa only [d1848, d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15389 (p : Pattern) (guard : d4967 p = 1) : d1849 p ≤ (0 : Int) + d1552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1849, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15376 p hg
    simpa only [d1849, d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1849, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15388 p hg
    simpa only [d1849, d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15390 (p : Pattern) (guard : d0 p = 1) : d358 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15391 (p : Pattern) (guard : d4474 p = 1) : d1850 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15390 p hg
    simpa only [d4474, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15392 (p : Pattern) (guard : d0 p = 1) : d1687 p ≤ (0 : Int) + d353 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15393 (p : Pattern) (guard : d4967 p = 1) : d1851 p ≤ (0 : Int) + d1553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1851, d1553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15391 p hg
    simpa only [d4967, d1851, d1553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1851, d1553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15392 p hg
    simpa only [d4967, d1851, d1553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15394 (p : Pattern) (guard : d4967 p = 1) : d1852 p ≤ (0 : Int) + d1554 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1852, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15393 p hg
    simpa only [d1852, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1852, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15268 p hg
    simpa only [d1852, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15395 (p : Pattern) (guard : d4967 p = 1) : d1853 p ≤ (0 : Int) + d1555 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1853, d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15394 p hg
    simpa only [d1853, d1555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1853, d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15275 p hg
    simpa only [d1853, d1555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15396 (p : Pattern) (guard : d4967 p = 1) : d1854 p ≤ (0 : Int) + d1556 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1854, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15395 p hg
    simpa only [d1854, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1854, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15279 p hg
    simpa only [d1854, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15397 (p : Pattern) (guard : d4967 p = 1) : d1855 p ≤ (0 : Int) + d1557 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1855, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15396 p hg
    simpa only [d1855, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1855, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15296 p hg
    simpa only [d1855, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15398 (p : Pattern) (guard : d4967 p = 1) : d1856 p ≤ (0 : Int) + d1558 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1856, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15265 p hg
    simpa only [d1856, d1558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1856, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15303 p hg
    simpa only [d1856, d1558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15399 (p : Pattern) (guard : d4967 p = 1) : d1857 p ≤ (0 : Int) + d1559 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1857, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15398 p hg
    simpa only [d1857, d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1857, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15305 p hg
    simpa only [d1857, d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
