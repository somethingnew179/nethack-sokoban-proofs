/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons087
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12320 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12321 (p : Pattern) (guard : d4206 p = 1) : d48 p ≤ (2 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d48, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4944 p hg
    simpa only [d4206, d48, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d48, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12320 p hg
    simpa only [d4206, d48, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12322 (p : Pattern) (guard : d4206 p = 1) : d49 p ≤ (2 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d49, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12321 p hg
    simpa only [d49, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d49, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d49, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12323 (p : Pattern) (guard : d4206 p = 1) : d237 p ≤ (2 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d237, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12322 p hg
    simpa only [d237, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d237, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d237, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12324 (p : Pattern) (guard : d4206 p = 1) : d1655 p ≤ (2 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1655, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12319 p hg
    simpa only [d1655, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1655, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12323 p hg
    simpa only [d1655, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12325 (p : Pattern) (guard : d4207 p = 1) : d1656 p ≤ (2 : Int) + d246 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12317 p hg
    simpa only [d4207, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12324 p hg
    simpa only [d4207, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12326 (p : Pattern) (guard : d4207 p = 1) : d1657 p ≤ (2 : Int) + d4754 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1657, d4754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12316 p hg
    simpa only [d1657, d4754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1657, d4754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12325 p hg
    simpa only [d1657, d4754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12327 (p : Pattern) (guard : d0 p = 1) : d1664 p ≤ (2 : Int) + d4754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12328 (p : Pattern) (guard : d4208 p = 1) : d1665 p ≤ (2 : Int) + d4754 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12326 p hg
    simpa only [d4208, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12327 p hg
    simpa only [d4208, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12329 (p : Pattern) (guard : d0 p = 1) : d1670 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12330 (p : Pattern) (guard : d4206 p = 1) : d1671 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12218 p hg
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12157 p hg
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12331 (p : Pattern) (guard : d4206 p = 1) : d1672 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12330 p hg
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12332 (p : Pattern) (guard : d4206 p = 1) : d1673 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12331 p hg
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12333 (p : Pattern) (guard : d4207 p = 1) : d1674 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12329 p hg
    simpa only [d4207, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12332 p hg
    simpa only [d4207, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12334 (p : Pattern) (guard : d0 p = 1) : d1652 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12335 (p : Pattern) (guard : d4206 p = 1) : d48 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12336 (p : Pattern) (guard : d4206 p = 1) : d49 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12335 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12337 (p : Pattern) (guard : d4206 p = 1) : d237 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12336 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12338 (p : Pattern) (guard : d4206 p = 1) : d1662 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12337 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12339 (p : Pattern) (guard : d4207 p = 1) : d1663 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12334 p hg
    simpa only [d4207, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12338 p hg
    simpa only [d4207, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12340 (p : Pattern) (guard : d4207 p = 1) : d1675 p ≤ (2 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12333 p hg
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12339 p hg
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12341 (p : Pattern) (guard : d4208 p = 1) : d1676 p ≤ (2 : Int) + d12 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12340 p hg
    simpa only [d4208, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4208, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12342 (p : Pattern) (guard : d4208 p = 1) : d1677 p ≤ (2 : Int) + d4980 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1677, d4980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12328 p hg
    simpa only [d1677, d4980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1677, d4980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12341 p hg
    simpa only [d1677, d4980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12343 (p : Pattern) (guard : d4208 p = 1) : d1678 p ≤ (2 : Int) + d4981 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1678, d4981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12306 p hg
    simpa only [d1678, d4981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1678, d4981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12342 p hg
    simpa only [d1678, d4981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12344 (p : Pattern) (guard : d4208 p = 1) : d1679 p ≤ (2 : Int) + d4982 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1679, d4982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12170 p hg
    simpa only [d1679, d4982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1679, d4982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12343 p hg
    simpa only [d1679, d4982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12345 (p : Pattern) (guard : d4208 p = 1) : d1680 p ≤ (2 : Int) + d4983 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1680, d4983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12292 p hg
    simpa only [d1680, d4983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1680, d4983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12344 p hg
    simpa only [d1680, d4983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12346 (p : Pattern) (guard : d4208 p = 1) : d1681 p ≤ (2 : Int) + d4984 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d1681, d4984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12249 p hg
    simpa only [d1681, d4984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d1681, d4984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12345 p hg
    simpa only [d1681, d4984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12347 (p : Pattern) (guard : d0 p = 1) : d324 p ≤ (0 : Int) + d1687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12348 (p : Pattern) (guard : d4967 p = 1) : d1504 p ≤ (0 : Int) + d1688 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1504, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11451 p hg
    simpa only [d4967, d1504, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1504, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12347 p hg
    simpa only [d4967, d1504, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12349 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (0 : Int) + d1687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12350 (p : Pattern) (guard : d4967 p = 1) : d1505 p ≤ (0 : Int) + d1690 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1505, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11455 p hg
    simpa only [d4967, d1505, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1505, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12349 p hg
    simpa only [d4967, d1505, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12351 (p : Pattern) (guard : d4967 p = 1) : d1506 p ≤ (0 : Int) + d1691 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1506, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12348 p hg
    simpa only [d1506, d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1506, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12350 p hg
    simpa only [d1506, d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12352 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d1687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12353 (p : Pattern) (guard : d4967 p = 1) : d1507 p ≤ (0 : Int) + d1692 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1507, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d1507, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1507, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12352 p hg
    simpa only [d4967, d1507, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12354 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12355 (p : Pattern) (guard : d4967 p = 1) : d43 p ≤ (0 : Int) + d1698 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d43, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d4967, d43, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d43, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12354 p hg
    simpa only [d4967, d43, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12356 (p : Pattern) (guard : d4967 p = 1) : d1508 p ≤ (0 : Int) + d1699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1508, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12353 p hg
    simpa only [d1508, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1508, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12355 p hg
    simpa only [d1508, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12357 (p : Pattern) (guard : d4967 p = 1) : d1509 p ≤ (0 : Int) + d1700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1509, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12351 p hg
    simpa only [d1509, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1509, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12356 p hg
    simpa only [d1509, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12358 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12359 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1692 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12358 p hg
    simpa only [d4967, d46, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12360 (p : Pattern) (guard : d4967 p = 1) : d47 p ≤ (0 : Int) + d1699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d47, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12359 p hg
    simpa only [d47, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d47, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12355 p hg
    simpa only [d47, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12361 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12362 (p : Pattern) (guard : d4967 p = 1) : d48 p ≤ (0 : Int) + d1706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d48, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11468 p hg
    simpa only [d4967, d48, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d48, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12361 p hg
    simpa only [d4967, d48, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12363 (p : Pattern) (guard : d4967 p = 1) : d49 p ≤ (0 : Int) + d1707 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d49, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12362 p hg
    simpa only [d49, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d49, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d49, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12364 (p : Pattern) (guard : d4967 p = 1) : d50 p ≤ (0 : Int) + d1708 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d50, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12360 p hg
    simpa only [d50, d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d50, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12363 p hg
    simpa only [d50, d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12365 (p : Pattern) (guard : d4967 p = 1) : d1510 p ≤ (0 : Int) + d1709 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1510, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12357 p hg
    simpa only [d1510, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1510, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12364 p hg
    simpa only [d1510, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12366 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1718 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12367 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1719 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12366 p hg
    simpa only [d4967, d46, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12368 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1725 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12369 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1726 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12368 p hg
    simpa only [d4967, d46, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12370 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1727 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12367 p hg
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12369 p hg
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12371 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1730 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12372 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12371 p hg
    simpa only [d4967, d46, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12373 (p : Pattern) (guard : d4967 p = 1) : d47 p ≤ (0 : Int) + d1733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d47, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12372 p hg
    simpa only [d47, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d47, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11482 p hg
    simpa only [d47, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12374 (p : Pattern) (guard : d4967 p = 1) : d1511 p ≤ (0 : Int) + d1734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1511, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12370 p hg
    simpa only [d1511, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1511, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12373 p hg
    simpa only [d1511, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12375 (p : Pattern) (guard : d4967 p = 1) : d1512 p ≤ (0 : Int) + d1738 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1512, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12374 p hg
    simpa only [d1512, d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1512, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11489 p hg
    simpa only [d1512, d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12376 (p : Pattern) (guard : d4967 p = 1) : d1513 p ≤ (0 : Int) + d1739 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1513, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12365 p hg
    simpa only [d1513, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1513, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12375 p hg
    simpa only [d1513, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12377 (p : Pattern) (guard : d0 p = 1) : d359 p ≤ (0 : Int) + d1687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12378 (p : Pattern) (guard : d4967 p = 1) : d1514 p ≤ (0 : Int) + d1741 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1514, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11493 p hg
    simpa only [d4967, d1514, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1514, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12377 p hg
    simpa only [d4967, d1514, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12379 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12380 (p : Pattern) (guard : d4967 p = 1) : d66 p ≤ (0 : Int) + d1747 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d66, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d66, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d66, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12379 p hg
    simpa only [d4967, d66, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12381 (p : Pattern) (guard : d4967 p = 1) : d1515 p ≤ (0 : Int) + d1748 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1515, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12378 p hg
    simpa only [d1515, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1515, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12380 p hg
    simpa only [d1515, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12382 (p : Pattern) (guard : d4967 p = 1) : d68 p ≤ (0 : Int) + d1749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d68, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12355 p hg
    simpa only [d68, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d68, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12362 p hg
    simpa only [d68, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12383 (p : Pattern) (guard : d4967 p = 1) : d1516 p ≤ (0 : Int) + d1750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1516, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12381 p hg
    simpa only [d1516, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1516, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12382 p hg
    simpa only [d1516, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12384 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1753 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12385 (p : Pattern) (guard : d4967 p = 1) : d70 p ≤ (0 : Int) + d1754 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d70, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11503 p hg
    simpa only [d4967, d70, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d70, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12384 p hg
    simpa only [d4967, d70, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12386 (p : Pattern) (guard : d4967 p = 1) : d71 p ≤ (0 : Int) + d1755 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d71, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12355 p hg
    simpa only [d71, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d71, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12385 p hg
    simpa only [d71, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12387 (p : Pattern) (guard : d4967 p = 1) : d72 p ≤ (0 : Int) + d1756 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d72, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11508 p hg
    simpa only [d4967, d72, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d72, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12371 p hg
    simpa only [d4967, d72, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12388 (p : Pattern) (guard : d4967 p = 1) : d73 p ≤ (0 : Int) + d1757 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d73, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12387 p hg
    simpa only [d73, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d73, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d73, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12389 (p : Pattern) (guard : d4967 p = 1) : d74 p ≤ (0 : Int) + d1758 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d74, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12386 p hg
    simpa only [d74, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d74, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12388 p hg
    simpa only [d74, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12390 (p : Pattern) (guard : d4967 p = 1) : d1517 p ≤ (0 : Int) + d1759 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1517, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12383 p hg
    simpa only [d1517, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1517, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12389 p hg
    simpa only [d1517, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12391 (p : Pattern) (guard : d4967 p = 1) : d1518 p ≤ (0 : Int) + d1761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1518, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12369 p hg
    simpa only [d1518, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1518, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11513 p hg
    simpa only [d1518, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12392 (p : Pattern) (guard : d4967 p = 1) : d1519 p ≤ (0 : Int) + d1763 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1519, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12391 p hg
    simpa only [d1519, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1519, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11515 p hg
    simpa only [d1519, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12393 (p : Pattern) (guard : d4967 p = 1) : d1520 p ≤ (0 : Int) + d1766 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1520, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12392 p hg
    simpa only [d1520, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1520, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11521 p hg
    simpa only [d1520, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12394 (p : Pattern) (guard : d4967 p = 1) : d1521 p ≤ (0 : Int) + d1767 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1521, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12390 p hg
    simpa only [d1521, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1521, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12393 p hg
    simpa only [d1521, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12395 (p : Pattern) (guard : d4967 p = 1) : d1522 p ≤ (0 : Int) + d1768 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1522, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12376 p hg
    simpa only [d1522, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1522, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12394 p hg
    simpa only [d1522, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12396 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1773 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12397 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1774 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12396 p hg
    simpa only [d4967, d46, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12398 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12399 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1783 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12398 p hg
    simpa only [d4967, d46, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12400 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12397 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12399 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12401 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1789 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12402 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1790 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12401 p hg
    simpa only [d4967, d46, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12403 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12404 (p : Pattern) (guard : d4967 p = 1) : d43 p ≤ (0 : Int) + d1799 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d43, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d4967, d43, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d43, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12403 p hg
    simpa only [d4967, d43, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12405 (p : Pattern) (guard : d4967 p = 1) : d47 p ≤ (0 : Int) + d1800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d47, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12402 p hg
    simpa only [d47, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d47, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12404 p hg
    simpa only [d47, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12406 (p : Pattern) (guard : d4967 p = 1) : d1511 p ≤ (0 : Int) + d1801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1511, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12400 p hg
    simpa only [d1511, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1511, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12405 p hg
    simpa only [d1511, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12407 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12408 (p : Pattern) (guard : d4967 p = 1) : d48 p ≤ (0 : Int) + d1805 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d48, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11468 p hg
    simpa only [d4967, d48, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d48, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12407 p hg
    simpa only [d4967, d48, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12409 (p : Pattern) (guard : d4967 p = 1) : d49 p ≤ (0 : Int) + d1806 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d49, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12408 p hg
    simpa only [d49, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d49, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d49, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12410 (p : Pattern) (guard : d4967 p = 1) : d50 p ≤ (0 : Int) + d1807 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d50, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12405 p hg
    simpa only [d50, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d50, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12409 p hg
    simpa only [d50, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12411 (p : Pattern) (guard : d4967 p = 1) : d1512 p ≤ (0 : Int) + d1808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1512, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12406 p hg
    simpa only [d1512, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1512, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12410 p hg
    simpa only [d1512, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12412 (p : Pattern) (guard : d4967 p = 1) : d66 p ≤ (0 : Int) + d1809 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d66, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d66, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d66, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12366 p hg
    simpa only [d4967, d66, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12413 (p : Pattern) (guard : d4967 p = 1) : d173 p ≤ (0 : Int) + d1810 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d173, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11543 p hg
    simpa only [d4967, d173, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d173, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12368 p hg
    simpa only [d4967, d173, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12414 (p : Pattern) (guard : d4967 p = 1) : d176 p ≤ (0 : Int) + d1811 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d176, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12412 p hg
    simpa only [d176, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d176, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12413 p hg
    simpa only [d176, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12415 (p : Pattern) (guard : d4967 p = 1) : d177 p ≤ (0 : Int) + d1812 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d177, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12414 p hg
    simpa only [d177, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d177, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12388 p hg
    simpa only [d177, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12416 (p : Pattern) (guard : d4967 p = 1) : d1523 p ≤ (0 : Int) + d1813 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1523, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12415 p hg
    simpa only [d1523, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1523, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1523, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12417 (p : Pattern) (guard : d4967 p = 1) : d1524 p ≤ (0 : Int) + d1814 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1524, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12411 p hg
    simpa only [d1524, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1524, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12416 p hg
    simpa only [d1524, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12418 (p : Pattern) (guard : d4967 p = 1) : d1518 p ≤ (0 : Int) + d1815 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1518, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12399 p hg
    simpa only [d1518, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1518, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12412 p hg
    simpa only [d1518, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12419 (p : Pattern) (guard : d4967 p = 1) : d68 p ≤ (0 : Int) + d1816 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d68, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12404 p hg
    simpa only [d68, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d68, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12408 p hg
    simpa only [d68, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12420 (p : Pattern) (guard : d4967 p = 1) : d1519 p ≤ (0 : Int) + d1817 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1519, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12418 p hg
    simpa only [d1519, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1519, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12419 p hg
    simpa only [d1519, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12421 (p : Pattern) (guard : d4967 p = 1) : d71 p ≤ (0 : Int) + d1818 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d71, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12404 p hg
    simpa only [d71, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d71, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12385 p hg
    simpa only [d71, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12422 (p : Pattern) (guard : d4967 p = 1) : d74 p ≤ (0 : Int) + d1819 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d74, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12421 p hg
    simpa only [d74, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d74, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12388 p hg
    simpa only [d74, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12423 (p : Pattern) (guard : d4967 p = 1) : d1520 p ≤ (0 : Int) + d1820 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1520, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12420 p hg
    simpa only [d1520, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1520, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12422 p hg
    simpa only [d1520, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12424 (p : Pattern) (guard : d4967 p = 1) : d183 p ≤ (0 : Int) + d1821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d183, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12413 p hg
    simpa only [d183, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d183, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d183, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12425 (p : Pattern) (guard : d4967 p = 1) : d184 p ≤ (0 : Int) + d1822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d184, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12424 p hg
    simpa only [d184, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d184, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d184, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12426 (p : Pattern) (guard : d4967 p = 1) : d1525 p ≤ (0 : Int) + d1823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1525, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12425 p hg
    simpa only [d1525, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1525, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1525, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12427 (p : Pattern) (guard : d4967 p = 1) : d1526 p ≤ (0 : Int) + d1824 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1526, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12423 p hg
    simpa only [d1526, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1526, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12426 p hg
    simpa only [d1526, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12428 (p : Pattern) (guard : d4967 p = 1) : d1527 p ≤ (0 : Int) + d1825 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1527, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12417 p hg
    simpa only [d1527, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1527, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12427 p hg
    simpa only [d1527, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12429 (p : Pattern) (guard : d4967 p = 1) : d1528 p ≤ (0 : Int) + d1826 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1528, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12395 p hg
    simpa only [d1528, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1528, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12428 p hg
    simpa only [d1528, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12430 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d1773 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12431 (p : Pattern) (guard : d4967 p = 1) : d1507 p ≤ (0 : Int) + d1774 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1507, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d1507, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1507, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12430 p hg
    simpa only [d4967, d1507, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12432 (p : Pattern) (guard : d4967 p = 1) : d1529 p ≤ (0 : Int) + d1784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1529, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12431 p hg
    simpa only [d1529, d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1529, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12399 p hg
    simpa only [d1529, d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12433 (p : Pattern) (guard : d4967 p = 1) : d1530 p ≤ (0 : Int) + d1801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1530, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12432 p hg
    simpa only [d1530, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1530, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12405 p hg
    simpa only [d1530, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12434 (p : Pattern) (guard : d4967 p = 1) : d1531 p ≤ (0 : Int) + d1808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1531, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12433 p hg
    simpa only [d1531, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1531, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12410 p hg
    simpa only [d1531, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12435 (p : Pattern) (guard : d4967 p = 1) : d1532 p ≤ (0 : Int) + d1814 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1532, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12434 p hg
    simpa only [d1532, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1532, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12416 p hg
    simpa only [d1532, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12436 (p : Pattern) (guard : d4967 p = 1) : d1533 p ≤ (0 : Int) + d1825 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1533, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12435 p hg
    simpa only [d1533, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1533, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12427 p hg
    simpa only [d1533, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12437 (p : Pattern) (guard : d4967 p = 1) : d1534 p ≤ (0 : Int) + d1827 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1534, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12408 p hg
    simpa only [d1534, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1534, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12387 p hg
    simpa only [d1534, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12438 (p : Pattern) (guard : d4967 p = 1) : d1535 p ≤ (0 : Int) + d1828 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1535, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12437 p hg
    simpa only [d1535, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1535, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12388 p hg
    simpa only [d1535, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12439 (p : Pattern) (guard : d4967 p = 1) : d1536 p ≤ (0 : Int) + d1829 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1536, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12388 p hg
    simpa only [d1536, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1536, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1536, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12440 (p : Pattern) (guard : d4967 p = 1) : d1537 p ≤ (0 : Int) + d1830 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1537, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12438 p hg
    simpa only [d1537, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1537, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12439 p hg
    simpa only [d1537, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12441 (p : Pattern) (guard : d4967 p = 1) : d1538 p ≤ (0 : Int) + d1831 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1538, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12439 p hg
    simpa only [d1538, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1538, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1538, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12442 (p : Pattern) (guard : d4967 p = 1) : d1539 p ≤ (0 : Int) + d1832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1539, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12440 p hg
    simpa only [d1539, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1539, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12441 p hg
    simpa only [d1539, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12443 (p : Pattern) (guard : d4967 p = 1) : d1540 p ≤ (0 : Int) + d1833 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1540, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12441 p hg
    simpa only [d1540, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1540, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1540, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12444 (p : Pattern) (guard : d4967 p = 1) : d1541 p ≤ (0 : Int) + d1834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1541, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12442 p hg
    simpa only [d1541, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1541, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12443 p hg
    simpa only [d1541, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12445 (p : Pattern) (guard : d4967 p = 1) : d1542 p ≤ (0 : Int) + d1835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1542, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12436 p hg
    simpa only [d1542, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1542, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12444 p hg
    simpa only [d1542, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12446 (p : Pattern) (guard : d4967 p = 1) : d1543 p ≤ (0 : Int) + d1836 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1543, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12429 p hg
    simpa only [d1543, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1543, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12445 p hg
    simpa only [d1543, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12447 (p : Pattern) (guard : d4967 p = 1) : d1544 p ≤ (0 : Int) + d1837 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1544, d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12350 p hg
    simpa only [d1544, d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1544, d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12359 p hg
    simpa only [d1544, d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12448 (p : Pattern) (guard : d4967 p = 1) : d1545 p ≤ (0 : Int) + d1838 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1545, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12447 p hg
    simpa only [d1545, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1545, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12360 p hg
    simpa only [d1545, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12449 (p : Pattern) (guard : d4967 p = 1) : d1546 p ≤ (0 : Int) + d1839 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1546, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12448 p hg
    simpa only [d1546, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1546, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12364 p hg
    simpa only [d1546, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12450 (p : Pattern) (guard : d4967 p = 1) : d1547 p ≤ (0 : Int) + d1840 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1547, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12449 p hg
    simpa only [d1547, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1547, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12375 p hg
    simpa only [d1547, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12451 (p : Pattern) (guard : d4967 p = 1) : d1518 p ≤ (0 : Int) + d1841 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1518, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12359 p hg
    simpa only [d1518, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1518, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12380 p hg
    simpa only [d1518, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12452 (p : Pattern) (guard : d4967 p = 1) : d1519 p ≤ (0 : Int) + d1842 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1519, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12451 p hg
    simpa only [d1519, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1519, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12382 p hg
    simpa only [d1519, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12453 (p : Pattern) (guard : d4967 p = 1) : d1520 p ≤ (0 : Int) + d1843 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1520, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12452 p hg
    simpa only [d1520, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1520, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12389 p hg
    simpa only [d1520, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12454 (p : Pattern) (guard : d4967 p = 1) : d1520 p ≤ (0 : Int) + d1844 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12453 p hg
    simpa only [d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12393 p hg
    simpa only [d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12455 (p : Pattern) (guard : d4967 p = 1) : d1548 p ≤ (0 : Int) + d1845 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1548, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12450 p hg
    simpa only [d1548, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1548, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12454 p hg
    simpa only [d1548, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12456 (p : Pattern) (guard : d4967 p = 1) : d1549 p ≤ (0 : Int) + d1846 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1549, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12455 p hg
    simpa only [d1549, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1549, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12428 p hg
    simpa only [d1549, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12457 (p : Pattern) (guard : d4967 p = 1) : d1550 p ≤ (0 : Int) + d1847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1550, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12428 p hg
    simpa only [d1550, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1550, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1550, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12458 (p : Pattern) (guard : d4967 p = 1) : d1551 p ≤ (0 : Int) + d1848 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1551, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12456 p hg
    simpa only [d1551, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1551, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12457 p hg
    simpa only [d1551, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12459 (p : Pattern) (guard : d4967 p = 1) : d1552 p ≤ (0 : Int) + d1849 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1552, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12446 p hg
    simpa only [d1552, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1552, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12458 p hg
    simpa only [d1552, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
