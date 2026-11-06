/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons119
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16800 (p : Pattern) (guard : d4967 p = 1) : d1806 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1806, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16799 p hg
    simpa only [d1806, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1806, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1806, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16801 (p : Pattern) (guard : d4967 p = 1) : d1807 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1807, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16796 p hg
    simpa only [d1807, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1807, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16800 p hg
    simpa only [d1807, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16802 (p : Pattern) (guard : d4967 p = 1) : d1808 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1808, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16797 p hg
    simpa only [d1808, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1808, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16801 p hg
    simpa only [d1808, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16803 (p : Pattern) (guard : d4967 p = 1) : d1809 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1809, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d1809, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1809, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16758 p hg
    simpa only [d4967, d1809, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16804 (p : Pattern) (guard : d4967 p = 1) : d1810 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1810, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d4967, d1810, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1810, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16760 p hg
    simpa only [d4967, d1810, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16805 (p : Pattern) (guard : d4967 p = 1) : d1811 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1811, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16803 p hg
    simpa only [d1811, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1811, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16804 p hg
    simpa only [d1811, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16806 (p : Pattern) (guard : d4967 p = 1) : d1812 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1812, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16805 p hg
    simpa only [d1812, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1812, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16779 p hg
    simpa only [d1812, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16807 (p : Pattern) (guard : d4967 p = 1) : d1813 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1813, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16806 p hg
    simpa only [d1813, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1813, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1813, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16808 (p : Pattern) (guard : d4967 p = 1) : d1814 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1814, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16802 p hg
    simpa only [d1814, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1814, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16807 p hg
    simpa only [d1814, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16809 (p : Pattern) (guard : d4967 p = 1) : d1815 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1815, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16790 p hg
    simpa only [d1815, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1815, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16803 p hg
    simpa only [d1815, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16810 (p : Pattern) (guard : d4967 p = 1) : d1816 p ≤ (0 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1816, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16795 p hg
    simpa only [d1816, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1816, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16799 p hg
    simpa only [d1816, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16811 (p : Pattern) (guard : d4967 p = 1) : d1817 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1817, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16809 p hg
    simpa only [d1817, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1817, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16810 p hg
    simpa only [d1817, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16812 (p : Pattern) (guard : d4967 p = 1) : d1818 p ≤ (0 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1818, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16795 p hg
    simpa only [d1818, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1818, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16776 p hg
    simpa only [d1818, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16813 (p : Pattern) (guard : d4967 p = 1) : d1819 p ≤ (0 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1819, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16812 p hg
    simpa only [d1819, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1819, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16779 p hg
    simpa only [d1819, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16814 (p : Pattern) (guard : d4967 p = 1) : d1820 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1820, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16811 p hg
    simpa only [d1820, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1820, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16813 p hg
    simpa only [d1820, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16815 (p : Pattern) (guard : d4967 p = 1) : d1821 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1821, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16804 p hg
    simpa only [d1821, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1821, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1821, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16816 (p : Pattern) (guard : d4967 p = 1) : d1822 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1822, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16815 p hg
    simpa only [d1822, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1822, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1822, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16817 (p : Pattern) (guard : d4967 p = 1) : d1823 p ≤ (0 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1823, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16816 p hg
    simpa only [d1823, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1823, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1823, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16818 (p : Pattern) (guard : d4967 p = 1) : d1824 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1824, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16814 p hg
    simpa only [d1824, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1824, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16817 p hg
    simpa only [d1824, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16819 (p : Pattern) (guard : d4967 p = 1) : d1825 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1825, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16808 p hg
    simpa only [d1825, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1825, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16818 p hg
    simpa only [d1825, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16820 (p : Pattern) (guard : d4967 p = 1) : d1826 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1826, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16786 p hg
    simpa only [d1826, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1826, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16819 p hg
    simpa only [d1826, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16821 (p : Pattern) (guard : d4967 p = 1) : d1827 p ≤ (0 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1827, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16799 p hg
    simpa only [d1827, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1827, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16778 p hg
    simpa only [d1827, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16822 (p : Pattern) (guard : d4967 p = 1) : d1828 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1828, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16821 p hg
    simpa only [d1828, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1828, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16779 p hg
    simpa only [d1828, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16823 (p : Pattern) (guard : d4967 p = 1) : d1829 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1829, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16779 p hg
    simpa only [d1829, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1829, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1829, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16824 (p : Pattern) (guard : d4967 p = 1) : d1830 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1830, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16822 p hg
    simpa only [d1830, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1830, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16823 p hg
    simpa only [d1830, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16825 (p : Pattern) (guard : d4967 p = 1) : d1831 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1831, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16823 p hg
    simpa only [d1831, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1831, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1831, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16826 (p : Pattern) (guard : d4967 p = 1) : d1832 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1832, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16824 p hg
    simpa only [d1832, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1832, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16825 p hg
    simpa only [d1832, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16827 (p : Pattern) (guard : d4967 p = 1) : d1833 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1833, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16825 p hg
    simpa only [d1833, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1833, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1833, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16828 (p : Pattern) (guard : d4967 p = 1) : d1834 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1834, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16826 p hg
    simpa only [d1834, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1834, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16827 p hg
    simpa only [d1834, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16829 (p : Pattern) (guard : d4967 p = 1) : d1835 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1835, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16819 p hg
    simpa only [d1835, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1835, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16828 p hg
    simpa only [d1835, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16830 (p : Pattern) (guard : d4967 p = 1) : d1836 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1836, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16820 p hg
    simpa only [d1836, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1836, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16829 p hg
    simpa only [d1836, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16831 (p : Pattern) (guard : d4967 p = 1) : d1837 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16746 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16748 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16832 (p : Pattern) (guard : d4967 p = 1) : d1838 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1838, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16831 p hg
    simpa only [d1838, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1838, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16751 p hg
    simpa only [d1838, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16833 (p : Pattern) (guard : d4967 p = 1) : d1839 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1839, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16832 p hg
    simpa only [d1839, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1839, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16756 p hg
    simpa only [d1839, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16834 (p : Pattern) (guard : d4967 p = 1) : d1840 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1840, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16833 p hg
    simpa only [d1840, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1840, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16767 p hg
    simpa only [d1840, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16835 (p : Pattern) (guard : d4967 p = 1) : d1841 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1841, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16748 p hg
    simpa only [d1841, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1841, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16771 p hg
    simpa only [d1841, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16836 (p : Pattern) (guard : d4967 p = 1) : d1842 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1842, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16835 p hg
    simpa only [d1842, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1842, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16773 p hg
    simpa only [d1842, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16837 (p : Pattern) (guard : d4967 p = 1) : d1843 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1843, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16836 p hg
    simpa only [d1843, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1843, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16780 p hg
    simpa only [d1843, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16838 (p : Pattern) (guard : d4967 p = 1) : d1844 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1844, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16837 p hg
    simpa only [d1844, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1844, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16784 p hg
    simpa only [d1844, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16839 (p : Pattern) (guard : d4967 p = 1) : d1845 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1845, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16834 p hg
    simpa only [d1845, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1845, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16838 p hg
    simpa only [d1845, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16840 (p : Pattern) (guard : d4967 p = 1) : d1846 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1846, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16839 p hg
    simpa only [d1846, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1846, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16819 p hg
    simpa only [d1846, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16841 (p : Pattern) (guard : d4967 p = 1) : d1847 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1847, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16819 p hg
    simpa only [d1847, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1847, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1847, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16842 (p : Pattern) (guard : d4967 p = 1) : d1848 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1848, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16840 p hg
    simpa only [d1848, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1848, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16841 p hg
    simpa only [d1848, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16843 (p : Pattern) (guard : d4967 p = 1) : d1849 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1849, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16830 p hg
    simpa only [d1849, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1849, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16842 p hg
    simpa only [d1849, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16844 (p : Pattern) (guard : d4967 p = 1) : d1851 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1851, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15391 p hg
    simpa only [d4967, d1851, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1851, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16744 p hg
    simpa only [d4967, d1851, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16845 (p : Pattern) (guard : d4967 p = 1) : d1852 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16844 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16748 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16846 (p : Pattern) (guard : d4967 p = 1) : d1853 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1853, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16845 p hg
    simpa only [d1853, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1853, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16751 p hg
    simpa only [d1853, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16847 (p : Pattern) (guard : d4967 p = 1) : d1854 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1854, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16846 p hg
    simpa only [d1854, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1854, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16756 p hg
    simpa only [d1854, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16848 (p : Pattern) (guard : d4967 p = 1) : d1855 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1855, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16847 p hg
    simpa only [d1855, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1855, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16767 p hg
    simpa only [d1855, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16849 (p : Pattern) (guard : d4967 p = 1) : d1856 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1856, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16746 p hg
    simpa only [d1856, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1856, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16771 p hg
    simpa only [d1856, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16850 (p : Pattern) (guard : d4967 p = 1) : d1857 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1857, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16849 p hg
    simpa only [d1857, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1857, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16773 p hg
    simpa only [d1857, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16851 (p : Pattern) (guard : d4967 p = 1) : d1858 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1858, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16850 p hg
    simpa only [d1858, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1858, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16780 p hg
    simpa only [d1858, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16852 (p : Pattern) (guard : d4967 p = 1) : d1859 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1859, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16851 p hg
    simpa only [d1859, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1859, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16784 p hg
    simpa only [d1859, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16853 (p : Pattern) (guard : d4967 p = 1) : d1860 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1860, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16848 p hg
    simpa only [d1860, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1860, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16852 p hg
    simpa only [d1860, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16854 (p : Pattern) (guard : d4967 p = 1) : d1861 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1861, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16853 p hg
    simpa only [d1861, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1861, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16819 p hg
    simpa only [d1861, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16855 (p : Pattern) (guard : d4967 p = 1) : d1862 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1862, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16854 p hg
    simpa only [d1862, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1862, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16829 p hg
    simpa only [d1862, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16856 (p : Pattern) (guard : d4967 p = 1) : d1863 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1863, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16748 p hg
    simpa only [d1863, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1863, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16751 p hg
    simpa only [d1863, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16857 (p : Pattern) (guard : d4967 p = 1) : d1864 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1864, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16856 p hg
    simpa only [d1864, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1864, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16756 p hg
    simpa only [d1864, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16858 (p : Pattern) (guard : d4967 p = 1) : d1865 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1865, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16857 p hg
    simpa only [d1865, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1865, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16767 p hg
    simpa only [d1865, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16859 (p : Pattern) (guard : d4967 p = 1) : d1866 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1866, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16858 p hg
    simpa only [d1866, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1866, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16838 p hg
    simpa only [d1866, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16860 (p : Pattern) (guard : d4967 p = 1) : d1867 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1867, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16859 p hg
    simpa only [d1867, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1867, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16819 p hg
    simpa only [d1867, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16861 (p : Pattern) (guard : d4967 p = 1) : d1868 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1868, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16860 p hg
    simpa only [d1868, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1868, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16841 p hg
    simpa only [d1868, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16862 (p : Pattern) (guard : d4967 p = 1) : d1869 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1869, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16855 p hg
    simpa only [d1869, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1869, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16861 p hg
    simpa only [d1869, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16863 (p : Pattern) (guard : d4967 p = 1) : d1870 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16843 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16862 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16864 (p : Pattern) (guard : d0 p = 1) : d1876 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16865 (p : Pattern) (guard : d4967 p = 1) : d1877 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1877, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15416 p hg
    simpa only [d4967, d1877, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1877, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16864 p hg
    simpa only [d4967, d1877, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16866 (p : Pattern) (guard : d4967 p = 1) : d1878 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1878, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1878, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1878, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16864 p hg
    simpa only [d4967, d1878, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16867 (p : Pattern) (guard : d4967 p = 1) : d1879 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16865 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16866 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16868 (p : Pattern) (guard : d0 p = 1) : d1884 p ≤ (0 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16869 (p : Pattern) (guard : d4967 p = 1) : d1885 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1885, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d1885, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1885, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16868 p hg
    simpa only [d4967, d1885, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16870 (p : Pattern) (guard : d4967 p = 1) : d1886 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1886, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16866 p hg
    simpa only [d1886, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1886, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16869 p hg
    simpa only [d1886, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16871 (p : Pattern) (guard : d4967 p = 1) : d1887 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1887, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16867 p hg
    simpa only [d1887, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1887, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16870 p hg
    simpa only [d1887, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16872 (p : Pattern) (guard : d4967 p = 1) : d1888 p ≤ (0 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1888, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16776 p hg
    simpa only [d1888, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1888, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1888, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16873 (p : Pattern) (guard : d4967 p = 1) : d1889 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1889, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16870 p hg
    simpa only [d1889, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1889, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16872 p hg
    simpa only [d1889, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16874 (p : Pattern) (guard : d4967 p = 1) : d1890 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1890, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16871 p hg
    simpa only [d1890, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1890, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16873 p hg
    simpa only [d1890, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16875 (p : Pattern) (guard : d0 p = 1) : d1899 p ≤ (0 : Int) + d117 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16876 (p : Pattern) (guard : d4967 p = 1) : d1900 p ≤ (0 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1900, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1900, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1900, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16875 p hg
    simpa only [d4967, d1900, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16877 (p : Pattern) (guard : d0 p = 1) : d1906 p ≤ (0 : Int) + d121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16878 (p : Pattern) (guard : d4967 p = 1) : d1907 p ≤ (0 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1907, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1907, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1907, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16877 p hg
    simpa only [d4967, d1907, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16879 (p : Pattern) (guard : d4967 p = 1) : d1908 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1908, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16876 p hg
    simpa only [d1908, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1908, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16878 p hg
    simpa only [d1908, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16880 (p : Pattern) (guard : d4967 p = 1) : d1912 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1912, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16879 p hg
    simpa only [d1912, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1912, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15438 p hg
    simpa only [d1912, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16881 (p : Pattern) (guard : d4967 p = 1) : d1914 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1914, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16880 p hg
    simpa only [d1914, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1914, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15441 p hg
    simpa only [d1914, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16882 (p : Pattern) (guard : d4967 p = 1) : d1915 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1915, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16874 p hg
    simpa only [d1915, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1915, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16881 p hg
    simpa only [d1915, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16883 (p : Pattern) (guard : d4967 p = 1) : d1917 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1917, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15445 p hg
    simpa only [d4967, d1917, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1917, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16864 p hg
    simpa only [d4967, d1917, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16884 (p : Pattern) (guard : d0 p = 1) : d1922 p ≤ (0 : Int) + d117 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16885 (p : Pattern) (guard : d4967 p = 1) : d1923 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1923, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d1923, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1923, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16884 p hg
    simpa only [d4967, d1923, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16886 (p : Pattern) (guard : d4967 p = 1) : d1924 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1924, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16883 p hg
    simpa only [d1924, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1924, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16885 p hg
    simpa only [d1924, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16887 (p : Pattern) (guard : d4967 p = 1) : d1925 p ≤ (0 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1925, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16869 p hg
    simpa only [d1925, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1925, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16776 p hg
    simpa only [d1925, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16888 (p : Pattern) (guard : d4967 p = 1) : d1926 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1926, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16886 p hg
    simpa only [d1926, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1926, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16887 p hg
    simpa only [d1926, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16889 (p : Pattern) (guard : d4967 p = 1) : d1927 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1927, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16869 p hg
    simpa only [d1927, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1927, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16778 p hg
    simpa only [d1927, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16890 (p : Pattern) (guard : d4967 p = 1) : d1928 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1928, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16889 p hg
    simpa only [d1928, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1928, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1928, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16891 (p : Pattern) (guard : d4967 p = 1) : d1929 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1929, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16888 p hg
    simpa only [d1929, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1929, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16890 p hg
    simpa only [d1929, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16892 (p : Pattern) (guard : d4967 p = 1) : d1931 p ≤ (0 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1931, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16878 p hg
    simpa only [d1931, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1931, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15456 p hg
    simpa only [d1931, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16893 (p : Pattern) (guard : d4967 p = 1) : d1933 p ≤ (0 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1933, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16892 p hg
    simpa only [d1933, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1933, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15458 p hg
    simpa only [d1933, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16894 (p : Pattern) (guard : d4967 p = 1) : d1936 p ≤ (0 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1936, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16893 p hg
    simpa only [d1936, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1936, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15461 p hg
    simpa only [d1936, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16895 (p : Pattern) (guard : d4967 p = 1) : d1937 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1937, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16891 p hg
    simpa only [d1937, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1937, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16894 p hg
    simpa only [d1937, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16896 (p : Pattern) (guard : d4967 p = 1) : d1938 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1938, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16882 p hg
    simpa only [d1938, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1938, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16895 p hg
    simpa only [d1938, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16897 (p : Pattern) (guard : d0 p = 1) : d1943 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16898 (p : Pattern) (guard : d4967 p = 1) : d1944 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1944, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1944, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1944, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16897 p hg
    simpa only [d4967, d1944, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16899 (p : Pattern) (guard : d0 p = 1) : d1952 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16900 (p : Pattern) (guard : d4967 p = 1) : d1953 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1953, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1953, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1953, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16899 p hg
    simpa only [d4967, d1953, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16901 (p : Pattern) (guard : d4967 p = 1) : d1954 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16898 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16900 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16902 (p : Pattern) (guard : d0 p = 1) : d1958 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16903 (p : Pattern) (guard : d4967 p = 1) : d1959 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1959, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1959, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1959, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16902 p hg
    simpa only [d4967, d1959, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16904 (p : Pattern) (guard : d0 p = 1) : d1967 p ≤ (0 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16905 (p : Pattern) (guard : d4967 p = 1) : d1968 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1968, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d1968, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1968, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16904 p hg
    simpa only [d4967, d1968, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16906 (p : Pattern) (guard : d4967 p = 1) : d1969 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1969, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16903 p hg
    simpa only [d1969, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1969, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16905 p hg
    simpa only [d1969, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16907 (p : Pattern) (guard : d4967 p = 1) : d1970 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1970, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16901 p hg
    simpa only [d1970, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1970, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16906 p hg
    simpa only [d1970, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16908 (p : Pattern) (guard : d4967 p = 1) : d1971 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1971, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16906 p hg
    simpa only [d1971, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1971, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16872 p hg
    simpa only [d1971, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16909 (p : Pattern) (guard : d4967 p = 1) : d1972 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1972, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16907 p hg
    simpa only [d1972, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1972, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16908 p hg
    simpa only [d1972, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16910 (p : Pattern) (guard : d4967 p = 1) : d1973 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1973, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d1973, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1973, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16875 p hg
    simpa only [d4967, d1973, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16911 (p : Pattern) (guard : d4967 p = 1) : d1974 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1974, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5855 p hg
    simpa only [d4967, d1974, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1974, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16877 p hg
    simpa only [d4967, d1974, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16912 (p : Pattern) (guard : d4967 p = 1) : d1975 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1975, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16910 p hg
    simpa only [d1975, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1975, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16911 p hg
    simpa only [d1975, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16913 (p : Pattern) (guard : d4967 p = 1) : d1976 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1976, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16912 p hg
    simpa only [d1976, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1976, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1976, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16914 (p : Pattern) (guard : d4967 p = 1) : d1977 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1977, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16913 p hg
    simpa only [d1977, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1977, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1977, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16915 (p : Pattern) (guard : d4967 p = 1) : d1978 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1978, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16909 p hg
    simpa only [d1978, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1978, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16914 p hg
    simpa only [d1978, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16916 (p : Pattern) (guard : d4967 p = 1) : d1979 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1979, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16900 p hg
    simpa only [d1979, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1979, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16910 p hg
    simpa only [d1979, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16917 (p : Pattern) (guard : d4967 p = 1) : d1980 p ≤ (0 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1980, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16905 p hg
    simpa only [d1980, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1980, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16776 p hg
    simpa only [d1980, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16918 (p : Pattern) (guard : d4967 p = 1) : d1981 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1981, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16916 p hg
    simpa only [d1981, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1981, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16917 p hg
    simpa only [d1981, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16919 (p : Pattern) (guard : d4967 p = 1) : d1982 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1982, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16905 p hg
    simpa only [d1982, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1982, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16778 p hg
    simpa only [d1982, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16920 (p : Pattern) (guard : d4967 p = 1) : d1983 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1983, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16919 p hg
    simpa only [d1983, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1983, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1983, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16921 (p : Pattern) (guard : d4967 p = 1) : d1984 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1984, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16918 p hg
    simpa only [d1984, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1984, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16920 p hg
    simpa only [d1984, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16922 (p : Pattern) (guard : d4967 p = 1) : d1985 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1985, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16911 p hg
    simpa only [d1985, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1985, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1985, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16923 (p : Pattern) (guard : d4967 p = 1) : d1986 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1986, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16922 p hg
    simpa only [d1986, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1986, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1986, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16924 (p : Pattern) (guard : d4967 p = 1) : d1987 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1987, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16923 p hg
    simpa only [d1987, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1987, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1987, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16925 (p : Pattern) (guard : d4967 p = 1) : d1988 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1988, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16921 p hg
    simpa only [d1988, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1988, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16924 p hg
    simpa only [d1988, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16926 (p : Pattern) (guard : d4967 p = 1) : d1989 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1989, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16915 p hg
    simpa only [d1989, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1989, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16925 p hg
    simpa only [d1989, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16927 (p : Pattern) (guard : d4967 p = 1) : d1990 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1990, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16896 p hg
    simpa only [d1990, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1990, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16926 p hg
    simpa only [d1990, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16928 (p : Pattern) (guard : d4967 p = 1) : d1991 p ≤ (0 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1991, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16872 p hg
    simpa only [d1991, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1991, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1991, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16929 (p : Pattern) (guard : d4967 p = 1) : d1992 p ≤ (0 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1992, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16928 p hg
    simpa only [d1992, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1992, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1992, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16930 (p : Pattern) (guard : d4967 p = 1) : d1993 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1993, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16929 p hg
    simpa only [d1993, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1993, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1993, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16931 (p : Pattern) (guard : d4967 p = 1) : d1994 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1994, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16930 p hg
    simpa only [d1994, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1994, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1994, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16932 (p : Pattern) (guard : d4967 p = 1) : d1995 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1995, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16926 p hg
    simpa only [d1995, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1995, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16931 p hg
    simpa only [d1995, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16933 (p : Pattern) (guard : d4967 p = 1) : d1996 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1996, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16927 p hg
    simpa only [d1996, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1996, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16932 p hg
    simpa only [d1996, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16934 (p : Pattern) (guard : d4967 p = 1) : d1997 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1997, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16866 p hg
    simpa only [d1997, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1997, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16870 p hg
    simpa only [d1997, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16935 (p : Pattern) (guard : d4967 p = 1) : d1998 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1998, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16934 p hg
    simpa only [d1998, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1998, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16873 p hg
    simpa only [d1998, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16936 (p : Pattern) (guard : d4967 p = 1) : d1999 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1999, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16935 p hg
    simpa only [d1999, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1999, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16881 p hg
    simpa only [d1999, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16937 (p : Pattern) (guard : d4967 p = 1) : d2000 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2000, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16866 p hg
    simpa only [d2000, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2000, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16885 p hg
    simpa only [d2000, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16938 (p : Pattern) (guard : d4967 p = 1) : d2001 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2001, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16937 p hg
    simpa only [d2001, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2001, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16887 p hg
    simpa only [d2001, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16939 (p : Pattern) (guard : d4967 p = 1) : d2002 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2002, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16938 p hg
    simpa only [d2002, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2002, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16890 p hg
    simpa only [d2002, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
