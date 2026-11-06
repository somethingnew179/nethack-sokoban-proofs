/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons275
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38640 (p : Pattern) (guard : d8094 p = 1) : d1696 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38638 p hg
    simpa only [d8094, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38639 p hg
    simpa only [d8094, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38641 (p : Pattern) (guard : d8100 p = 1) : d1697 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38640 p hg
    simpa only [d8100, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38642 (p : Pattern) (guard : d8101 p = 1) : d1698 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38604 p hg
    simpa only [d8101, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38643 (p : Pattern) (guard : d8102 p = 1) : d1699 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38637 p hg
    simpa only [d8102, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38642 p hg
    simpa only [d8102, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38644 (p : Pattern) (guard : d8103 p = 1) : d1838 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38636 p hg
    simpa only [d8103, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38643 p hg
    simpa only [d8103, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38645 (p : Pattern) (guard : d8096 p = 1) : d1692 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34748 p hg
    simpa only [d8096, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38634 p hg
    simpa only [d8096, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38646 (p : Pattern) (guard : d8101 p = 1) : d1698 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38554 p hg
    simpa only [d8101, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38647 (p : Pattern) (guard : d8102 p = 1) : d1699 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38645 p hg
    simpa only [d8102, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38646 p hg
    simpa only [d8102, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38648 (p : Pattern) (guard : d8101 p = 1) : d1706 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34397 p hg
    simpa only [d8101, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38444 p hg
    simpa only [d8101, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38649 (p : Pattern) (guard : d8107 p = 1) : d1707 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38648 p hg
    simpa only [d8107, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38650 (p : Pattern) (guard : d8108 p = 1) : d1708 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38647 p hg
    simpa only [d8108, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38649 p hg
    simpa only [d8108, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38651 (p : Pattern) (guard : d8109 p = 1) : d1839 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38644 p hg
    simpa only [d8109, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38650 p hg
    simpa only [d8109, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38652 (p : Pattern) (guard : d8096 p = 1) : d1719 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34465 p hg
    simpa only [d8096, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38653 (p : Pattern) (guard : d8101 p = 1) : d1726 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8101, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38654 (p : Pattern) (guard : d8102 p = 1) : d1727 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38652 p hg
    simpa only [d8102, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38653 p hg
    simpa only [d8102, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38655 (p : Pattern) (guard : d8101 p = 1) : d1731 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8101, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38656 (p : Pattern) (guard : d8106 p = 1) : d1732 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8106, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38657 (p : Pattern) (guard : d8107 p = 1) : d1733 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38655 p hg
    simpa only [d8107, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38656 p hg
    simpa only [d8107, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38658 (p : Pattern) (guard : d8108 p = 1) : d1734 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38654 p hg
    simpa only [d8108, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38657 p hg
    simpa only [d8108, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38659 (p : Pattern) (guard : d8101 p = 1) : d1735 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8101, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38660 (p : Pattern) (guard : d8107 p = 1) : d1736 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38659 p hg
    simpa only [d8107, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38656 p hg
    simpa only [d8107, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38661 (p : Pattern) (guard : d8112 p = 1) : d528 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38466 p hg
    simpa only [d8112, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38662 (p : Pattern) (guard : d8113 p = 1) : d1737 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38660 p hg
    simpa only [d8113, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38661 p hg
    simpa only [d8113, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38663 (p : Pattern) (guard : d8114 p = 1) : d1738 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38658 p hg
    simpa only [d8114, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38662 p hg
    simpa only [d8114, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38664 (p : Pattern) (guard : d8115 p = 1) : d1840 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38651 p hg
    simpa only [d8115, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38663 p hg
    simpa only [d8115, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38665 (p : Pattern) (guard : d8091 p = 1) : d15 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34653 p hg
    simpa only [d8091, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38666 (p : Pattern) (guard : d8096 p = 1) : d1692 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38665 p hg
    simpa only [d8096, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38634 p hg
    simpa only [d8096, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38667 (p : Pattern) (guard : d8095 p = 1) : d32 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34659 p hg
    simpa only [d8095, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38668 (p : Pattern) (guard : d8089 p = 1) : d1744 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8089, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38432 p hg
    simpa only [d8089, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38669 (p : Pattern) (guard : d5854 p = 1) : d1743 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38432 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17162 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38670 (p : Pattern) (guard : d8094 p = 1) : d1745 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38668 p hg
    simpa only [d8094, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38669 p hg
    simpa only [d8094, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38671 (p : Pattern) (guard : d8100 p = 1) : d1746 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38670 p hg
    simpa only [d8100, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38672 (p : Pattern) (guard : d8101 p = 1) : d1747 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38667 p hg
    simpa only [d8101, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38671 p hg
    simpa only [d8101, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38673 (p : Pattern) (guard : d8102 p = 1) : d1841 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38666 p hg
    simpa only [d8102, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38672 p hg
    simpa only [d8102, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38674 (p : Pattern) (guard : d8095 p = 1) : d19 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34666 p hg
    simpa only [d8095, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38675 (p : Pattern) (guard : d8101 p = 1) : d1698 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38674 p hg
    simpa only [d8101, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38676 (p : Pattern) (guard : d5854 p = 1) : d1703 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34393 p hg
    simpa only [d5854, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17112 p hg
    simpa only [d5854, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38677 (p : Pattern) (guard : d8099 p = 1) : d1704 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38676 p hg
    simpa only [d8099, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17112 p hg
    simpa only [d8099, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38678 (p : Pattern) (guard : d8105 p = 1) : d1705 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38677 p hg
    simpa only [d8105, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38679 (p : Pattern) (guard : d8106 p = 1) : d1706 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34489 p hg
    simpa only [d8106, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38678 p hg
    simpa only [d8106, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38680 (p : Pattern) (guard : d8107 p = 1) : d1749 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38675 p hg
    simpa only [d8107, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38679 p hg
    simpa only [d8107, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38681 (p : Pattern) (guard : d8108 p = 1) : d1842 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38673 p hg
    simpa only [d8108, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38680 p hg
    simpa only [d8108, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38682 (p : Pattern) (guard : d8107 p = 1) : d1755 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38642 p hg
    simpa only [d8107, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38565 p hg
    simpa only [d8107, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38683 (p : Pattern) (guard : d8113 p = 1) : d1758 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38682 p hg
    simpa only [d8113, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8113, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38684 (p : Pattern) (guard : d8114 p = 1) : d1843 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38681 p hg
    simpa only [d8114, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38683 p hg
    simpa only [d8114, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38685 (p : Pattern) (guard : d8101 p = 1) : d1726 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34752 p hg
    simpa only [d8101, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38686 (p : Pattern) (guard : d8106 p = 1) : d1760 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8106, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38687 (p : Pattern) (guard : d8107 p = 1) : d1761 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38685 p hg
    simpa only [d8107, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38686 p hg
    simpa only [d8107, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38688 (p : Pattern) (guard : d8111 p = 1) : d527 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34598 p hg
    simpa only [d8111, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38689 (p : Pattern) (guard : d8112 p = 1) : d1762 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38656 p hg
    simpa only [d8112, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38688 p hg
    simpa only [d8112, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38690 (p : Pattern) (guard : d8113 p = 1) : d1763 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38687 p hg
    simpa only [d8113, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38689 p hg
    simpa only [d8113, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38691 (p : Pattern) (guard : d8111 p = 1) : d277 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34602 p hg
    simpa only [d8111, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38692 (p : Pattern) (guard : d8112 p = 1) : d1764 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38656 p hg
    simpa only [d8112, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38691 p hg
    simpa only [d8112, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38693 (p : Pattern) (guard : d8111 p = 1) : d538 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34605 p hg
    simpa only [d8111, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38694 (p : Pattern) (guard : d8117 p = 1) : d539 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38693 p hg
    simpa only [d8117, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38695 (p : Pattern) (guard : d8118 p = 1) : d1765 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38692 p hg
    simpa only [d8118, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38694 p hg
    simpa only [d8118, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38696 (p : Pattern) (guard : d8119 p = 1) : d1766 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38690 p hg
    simpa only [d8119, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38695 p hg
    simpa only [d8119, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38697 (p : Pattern) (guard : d8120 p = 1) : d1844 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38684 p hg
    simpa only [d8120, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38696 p hg
    simpa only [d8120, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38698 (p : Pattern) (guard : d8121 p = 1) : d1845 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38664 p hg
    simpa only [d8121, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38697 p hg
    simpa only [d8121, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38699 (p : Pattern) (guard : d8085 p = 1) : d1771 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d8085, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8085, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38700 (p : Pattern) (guard : d5843 p = 1) : d1769 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19859 p hg
    simpa only [d5843, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38701 (p : Pattern) (guard : d5847 p = 1) : d1770 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38700 p hg
    simpa only [d5847, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38702 (p : Pattern) (guard : d8089 p = 1) : d1770 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38703 (p : Pattern) (guard : d8090 p = 1) : d1772 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38699 p hg
    simpa only [d8090, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38702 p hg
    simpa only [d8090, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38704 (p : Pattern) (guard : d8095 p = 1) : d1773 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38703 p hg
    simpa only [d8095, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38705 (p : Pattern) (guard : d8096 p = 1) : d1774 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34748 p hg
    simpa only [d8096, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38704 p hg
    simpa only [d8096, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38706 (p : Pattern) (guard : d5843 p = 1) : d1775 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d5843, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19926 p hg
    simpa only [d5843, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38707 (p : Pattern) (guard : d5847 p = 1) : d1776 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38706 p hg
    simpa only [d5847, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38708 (p : Pattern) (guard : d8089 p = 1) : d1777 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8089, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38707 p hg
    simpa only [d8089, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38709 (p : Pattern) (guard : d5854 p = 1) : d1780 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d5854, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17209 p hg
    simpa only [d5854, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38710 (p : Pattern) (guard : d8094 p = 1) : d1781 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38708 p hg
    simpa only [d8094, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38709 p hg
    simpa only [d8094, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38711 (p : Pattern) (guard : d8100 p = 1) : d1782 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38710 p hg
    simpa only [d8100, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38712 (p : Pattern) (guard : d8101 p = 1) : d1783 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34752 p hg
    simpa only [d8101, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38713 (p : Pattern) (guard : d8102 p = 1) : d1784 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38705 p hg
    simpa only [d8102, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38712 p hg
    simpa only [d8102, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38714 (p : Pattern) (guard : d5854 p = 1) : d1787 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d5854, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17215 p hg
    simpa only [d5854, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38715 (p : Pattern) (guard : d8094 p = 1) : d1788 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38708 p hg
    simpa only [d8094, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38714 p hg
    simpa only [d8094, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38716 (p : Pattern) (guard : d8100 p = 1) : d1789 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38715 p hg
    simpa only [d8100, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38717 (p : Pattern) (guard : d8101 p = 1) : d1790 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8101, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38718 (p : Pattern) (guard : d5854 p = 1) : d1793 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d5854, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17220 p hg
    simpa only [d5854, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38719 (p : Pattern) (guard : d0 p = 1) : d1796 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38720 (p : Pattern) (guard : d8099 p = 1) : d1797 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38718 p hg
    simpa only [d8099, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38719 p hg
    simpa only [d8099, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38721 (p : Pattern) (guard : d8105 p = 1) : d1798 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38720 p hg
    simpa only [d8105, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38722 (p : Pattern) (guard : d8106 p = 1) : d1799 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8106, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38721 p hg
    simpa only [d8106, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38723 (p : Pattern) (guard : d8107 p = 1) : d1800 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38717 p hg
    simpa only [d8107, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38722 p hg
    simpa only [d8107, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38724 (p : Pattern) (guard : d8108 p = 1) : d1801 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38713 p hg
    simpa only [d8108, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38723 p hg
    simpa only [d8108, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38725 (p : Pattern) (guard : d8112 p = 1) : d1806 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38559 p hg
    simpa only [d8112, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38726 (p : Pattern) (guard : d8113 p = 1) : d1807 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38723 p hg
    simpa only [d8113, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38725 p hg
    simpa only [d8113, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38727 (p : Pattern) (guard : d8114 p = 1) : d1808 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38724 p hg
    simpa only [d8114, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38726 p hg
    simpa only [d8114, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38728 (p : Pattern) (guard : d8101 p = 1) : d1809 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8101, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38729 (p : Pattern) (guard : d5854 p = 1) : d1720 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34424 p hg
    simpa only [d5854, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17131 p hg
    simpa only [d5854, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38730 (p : Pattern) (guard : d0 p = 1) : d1723 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38731 (p : Pattern) (guard : d8099 p = 1) : d1724 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38729 p hg
    simpa only [d8099, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38730 p hg
    simpa only [d8099, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38732 (p : Pattern) (guard : d8105 p = 1) : d1725 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38731 p hg
    simpa only [d8105, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38733 (p : Pattern) (guard : d8106 p = 1) : d1810 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8106, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38734 (p : Pattern) (guard : d8107 p = 1) : d1811 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38728 p hg
    simpa only [d8107, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38733 p hg
    simpa only [d8107, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38735 (p : Pattern) (guard : d8113 p = 1) : d1812 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38734 p hg
    simpa only [d8113, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8113, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38736 (p : Pattern) (guard : d8119 p = 1) : d1813 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38735 p hg
    simpa only [d8119, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38737 (p : Pattern) (guard : d8120 p = 1) : d1814 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38727 p hg
    simpa only [d8120, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38736 p hg
    simpa only [d8120, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38738 (p : Pattern) (guard : d8101 p = 1) : d1783 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34781 p hg
    simpa only [d8101, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38739 (p : Pattern) (guard : d5854 p = 1) : d1712 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d5854, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17123 p hg
    simpa only [d5854, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38740 (p : Pattern) (guard : d0 p = 1) : d1716 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38741 (p : Pattern) (guard : d8099 p = 1) : d1717 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38739 p hg
    simpa only [d8099, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38740 p hg
    simpa only [d8099, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38742 (p : Pattern) (guard : d8105 p = 1) : d1718 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38741 p hg
    simpa only [d8105, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38743 (p : Pattern) (guard : d8106 p = 1) : d1809 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8106, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38744 (p : Pattern) (guard : d8107 p = 1) : d1815 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38738 p hg
    simpa only [d8107, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38743 p hg
    simpa only [d8107, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38745 (p : Pattern) (guard : d8111 p = 1) : d1805 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34598 p hg
    simpa only [d8111, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15337 p hg
    simpa only [d8111, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38746 (p : Pattern) (guard : d8112 p = 1) : d1816 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38722 p hg
    simpa only [d8112, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38745 p hg
    simpa only [d8112, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38747 (p : Pattern) (guard : d8113 p = 1) : d1817 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38744 p hg
    simpa only [d8113, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38746 p hg
    simpa only [d8113, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38748 (p : Pattern) (guard : d8111 p = 1) : d1754 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34602 p hg
    simpa only [d8111, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15307 p hg
    simpa only [d8111, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38749 (p : Pattern) (guard : d8112 p = 1) : d1818 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38722 p hg
    simpa only [d8112, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38748 p hg
    simpa only [d8112, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38750 (p : Pattern) (guard : d8111 p = 1) : d1756 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34605 p hg
    simpa only [d8111, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d8111, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38751 (p : Pattern) (guard : d8117 p = 1) : d1757 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38750 p hg
    simpa only [d8117, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38752 (p : Pattern) (guard : d8118 p = 1) : d1819 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38749 p hg
    simpa only [d8118, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38753 (p : Pattern) (guard : d8119 p = 1) : d1820 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38747 p hg
    simpa only [d8119, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38752 p hg
    simpa only [d8119, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38754 (p : Pattern) (guard : d8112 p = 1) : d1821 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38733 p hg
    simpa only [d8112, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38755 (p : Pattern) (guard : d8118 p = 1) : d1822 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38754 p hg
    simpa only [d8118, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38756 (p : Pattern) (guard : d8124 p = 1) : d1823 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38755 p hg
    simpa only [d8124, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38757 (p : Pattern) (guard : d8125 p = 1) : d1824 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38753 p hg
    simpa only [d8125, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38756 p hg
    simpa only [d8125, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38758 (p : Pattern) (guard : d8126 p = 1) : d1825 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38737 p hg
    simpa only [d8126, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38757 p hg
    simpa only [d8126, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38759 (p : Pattern) (guard : d8127 p = 1) : d1846 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38698 p hg
    simpa only [d8127, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38758 p hg
    simpa only [d8127, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38760 (p : Pattern) (guard : d8096 p = 1) : d1774 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d8096, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38704 p hg
    simpa only [d8096, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38761 (p : Pattern) (guard : d8102 p = 1) : d1784 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38760 p hg
    simpa only [d8102, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38738 p hg
    simpa only [d8102, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38762 (p : Pattern) (guard : d8101 p = 1) : d1790 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34752 p hg
    simpa only [d8101, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38763 (p : Pattern) (guard : d8107 p = 1) : d1800 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38762 p hg
    simpa only [d8107, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38722 p hg
    simpa only [d8107, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38764 (p : Pattern) (guard : d8108 p = 1) : d1801 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38761 p hg
    simpa only [d8108, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38763 p hg
    simpa only [d8108, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38765 (p : Pattern) (guard : d8114 p = 1) : d1808 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38764 p hg
    simpa only [d8114, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38726 p hg
    simpa only [d8114, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38766 (p : Pattern) (guard : d8120 p = 1) : d1814 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38765 p hg
    simpa only [d8120, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38736 p hg
    simpa only [d8120, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38767 (p : Pattern) (guard : d8101 p = 1) : d1783 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34967 p hg
    simpa only [d8101, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38768 (p : Pattern) (guard : d8107 p = 1) : d1815 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38767 p hg
    simpa only [d8107, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38743 p hg
    simpa only [d8107, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38769 (p : Pattern) (guard : d8113 p = 1) : d1817 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38768 p hg
    simpa only [d8113, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38746 p hg
    simpa only [d8113, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38770 (p : Pattern) (guard : d8119 p = 1) : d1820 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38769 p hg
    simpa only [d8119, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38752 p hg
    simpa only [d8119, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38771 (p : Pattern) (guard : d8125 p = 1) : d1824 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38770 p hg
    simpa only [d8125, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38756 p hg
    simpa only [d8125, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38772 (p : Pattern) (guard : d8126 p = 1) : d1825 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38766 p hg
    simpa only [d8126, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38771 p hg
    simpa only [d8126, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38773 (p : Pattern) (guard : d8132 p = 1) : d1847 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38772 p hg
    simpa only [d8132, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38774 (p : Pattern) (guard : d8133 p = 1) : d1848 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38759 p hg
    simpa only [d8133, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38773 p hg
    simpa only [d8133, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38775 (p : Pattern) (guard : d8134 p = 1) : d1849 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38628 p hg
    simpa only [d8134, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38774 p hg
    simpa only [d8134, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38776 (p : Pattern) (guard : d8086 p = 1) : d358 p ≤ (0 : Int) + d358 p := by
  omega
theorem compare38777 (p : Pattern) (guard : d8087 p = 1) : d1850 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d1850, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34746 p hg
    simpa only [d8087, d1850, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d1850, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38776 p hg
    simpa only [d8087, d1850, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38778 (p : Pattern) (guard : d1 p = 1) : d1685 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1685, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d1685, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1685, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d1685, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38779 (p : Pattern) (guard : d8086 p = 1) : d1686 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1686, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38778 p hg
    simpa only [d8086, d1686, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1686, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38346 p hg
    simpa only [d8086, d1686, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
