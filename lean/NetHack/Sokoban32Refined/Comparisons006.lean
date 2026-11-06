/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare840 (p : Pattern) (guard : d913 p = 1) : d182 p ≤ (0 : Int) + d326 p := by
  cases selected : p 86 with
  | false =>
    have hg : d913 p = 1 := by simpa only [d182, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare825 p hg
    simpa only [d182, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d913 p = 1 := by simpa only [d182, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare839 p hg
    simpa only [d182, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare841 (p : Pattern) (guard : d913 p = 1) : d183 p ≤ (0 : Int) + d327 p := by
  cases selected : p 80 with
  | false =>
    have hg : d913 p = 1 := by simpa only [d183, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare819 p hg
    simpa only [d183, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d913 p = 1 := by simpa only [d183, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare840 p hg
    simpa only [d183, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare842 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare843 (p : Pattern) (guard : d915 p = 1) : d16 p ≤ (0 : Int) + d328 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare842 p hg
    simpa only [d915, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare844 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare845 (p : Pattern) (guard : d915 p = 1) : d27 p ≤ (0 : Int) + d328 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d27, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d27, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d27, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare844 p hg
    simpa only [d915, d27, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare846 (p : Pattern) (guard : d915 p = 1) : d28 p ≤ (0 : Int) + d328 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare847 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare848 (p : Pattern) (guard : d915 p = 1) : d36 p ≤ (0 : Int) + d328 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d36, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d36, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d36, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d915, d36, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare849 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (0 : Int) + d42 p := by
  omega
theorem compare850 (p : Pattern) (guard : d915 p = 1) : d43 p ≤ (0 : Int) + d329 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d43, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare849 p hg
    simpa only [d915, d43, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d43, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare844 p hg
    simpa only [d915, d43, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare851 (p : Pattern) (guard : d915 p = 1) : d44 p ≤ (0 : Int) + d330 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d44, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare848 p hg
    simpa only [d44, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d44, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare850 p hg
    simpa only [d44, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare852 (p : Pattern) (guard : d915 p = 1) : d45 p ≤ (0 : Int) + d331 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d45, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare846 p hg
    simpa only [d45, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d45, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d45, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare853 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare854 (p : Pattern) (guard : d915 p = 1) : d15 p ≤ (0 : Int) + d332 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d915, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare855 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare856 (p : Pattern) (guard : d915 p = 1) : d46 p ≤ (0 : Int) + d332 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d46, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d46, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d46, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d915, d46, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare857 (p : Pattern) (guard : d915 p = 1) : d47 p ≤ (0 : Int) + d332 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare854 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare856 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare858 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare859 (p : Pattern) (guard : d915 p = 1) : d48 p ≤ (0 : Int) + d332 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d48, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d48, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d48, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d915, d48, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare860 (p : Pattern) (guard : d915 p = 1) : d49 p ≤ (0 : Int) + d333 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d49, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d915, d49, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d49, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d915, d49, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare861 (p : Pattern) (guard : d915 p = 1) : d50 p ≤ (0 : Int) + d334 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d50, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare859 p hg
    simpa only [d50, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d50, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare860 p hg
    simpa only [d50, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare862 (p : Pattern) (guard : d915 p = 1) : d51 p ≤ (0 : Int) + d335 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d51, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare857 p hg
    simpa only [d51, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d51, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare861 p hg
    simpa only [d51, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare863 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare864 (p : Pattern) (guard : d915 p = 1) : d53 p ≤ (0 : Int) + d336 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare863 p hg
    simpa only [d915, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare865 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare866 (p : Pattern) (guard : d915 p = 1) : d56 p ≤ (0 : Int) + d336 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d56, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d56, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d56, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare865 p hg
    simpa only [d915, d56, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare867 (p : Pattern) (guard : d915 p = 1) : d57 p ≤ (0 : Int) + d336 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare864 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare868 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare869 (p : Pattern) (guard : d915 p = 1) : d60 p ≤ (0 : Int) + d336 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d60, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d60, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d60, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d915, d60, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare870 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (0 : Int) + d62 p := by
  omega
theorem compare871 (p : Pattern) (guard : d915 p = 1) : d63 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d915, d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare865 p hg
    simpa only [d915, d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare872 (p : Pattern) (guard : d915 p = 1) : d64 p ≤ (0 : Int) + d338 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d64, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare869 p hg
    simpa only [d64, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d64, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare871 p hg
    simpa only [d64, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare873 (p : Pattern) (guard : d915 p = 1) : d65 p ≤ (0 : Int) + d339 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d65, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d65, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d65, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare872 p hg
    simpa only [d65, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare874 (p : Pattern) (guard : d915 p = 1) : d66 p ≤ (0 : Int) + d340 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d66, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare862 p hg
    simpa only [d66, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d66, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare873 p hg
    simpa only [d66, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare875 (p : Pattern) (guard : d915 p = 1) : d67 p ≤ (0 : Int) + d341 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d67, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare852 p hg
    simpa only [d67, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d67, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare874 p hg
    simpa only [d67, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare876 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (0 : Int) + d69 p := by
  omega
theorem compare877 (p : Pattern) (guard : d0 p = 1) : d71 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare878 (p : Pattern) (guard : d915 p = 1) : d72 p ≤ (0 : Int) + d342 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d72, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare876 p hg
    simpa only [d915, d72, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d72, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare877 p hg
    simpa only [d915, d72, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare879 (p : Pattern) (guard : d915 p = 1) : d73 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d73, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d73, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d73, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare878 p hg
    simpa only [d73, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare880 (p : Pattern) (guard : d915 p = 1) : d74 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d74, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare846 p hg
    simpa only [d74, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d74, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare879 p hg
    simpa only [d74, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare881 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (0 : Int) + d68 p := by
  omega
theorem compare882 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare883 (p : Pattern) (guard : d915 p = 1) : d75 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d75, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare881 p hg
    simpa only [d915, d75, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d75, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d915, d75, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare884 (p : Pattern) (guard : d915 p = 1) : d76 p ≤ (0 : Int) + d346 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d76, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d76, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d76, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare883 p hg
    simpa only [d76, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare885 (p : Pattern) (guard : d915 p = 1) : d77 p ≤ (0 : Int) + d347 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d77, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare846 p hg
    simpa only [d77, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d77, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare884 p hg
    simpa only [d77, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare886 (p : Pattern) (guard : d915 p = 1) : d78 p ≤ (0 : Int) + d348 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d78, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare880 p hg
    simpa only [d78, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d78, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d78, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare887 (p : Pattern) (guard : d915 p = 1) : d79 p ≤ (0 : Int) + d349 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d79, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare856 p hg
    simpa only [d79, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d79, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare883 p hg
    simpa only [d79, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare888 (p : Pattern) (guard : d915 p = 1) : d80 p ≤ (0 : Int) + d350 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d80, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare857 p hg
    simpa only [d80, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d80, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare887 p hg
    simpa only [d80, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare889 (p : Pattern) (guard : d915 p = 1) : d81 p ≤ (0 : Int) + d351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d81, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d81, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d81, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare883 p hg
    simpa only [d81, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare890 (p : Pattern) (guard : d915 p = 1) : d82 p ≤ (0 : Int) + d352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d82, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d82, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d82, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare889 p hg
    simpa only [d82, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare891 (p : Pattern) (guard : d915 p = 1) : d83 p ≤ (0 : Int) + d353 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d83, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d83, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d83, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare890 p hg
    simpa only [d83, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare892 (p : Pattern) (guard : d915 p = 1) : d84 p ≤ (0 : Int) + d354 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d84, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare886 p hg
    simpa only [d84, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d84, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare891 p hg
    simpa only [d84, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare893 (p : Pattern) (guard : d915 p = 1) : d85 p ≤ (0 : Int) + d355 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d85, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare875 p hg
    simpa only [d85, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d85, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare892 p hg
    simpa only [d85, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare894 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare895 (p : Pattern) (guard : d915 p = 1) : d86 p ≤ (0 : Int) + d356 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare894 p hg
    simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare896 (p : Pattern) (guard : d0 p = 1) : d87 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare897 (p : Pattern) (guard : d915 p = 1) : d88 p ≤ (0 : Int) + d356 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d88, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d88, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d88, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare896 p hg
    simpa only [d915, d88, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare898 (p : Pattern) (guard : d915 p = 1) : d89 p ≤ (0 : Int) + d356 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare897 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare899 (p : Pattern) (guard : d0 p = 1) : d90 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare900 (p : Pattern) (guard : d915 p = 1) : d91 p ≤ (0 : Int) + d356 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d91, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d91, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d91, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d915, d91, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare901 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (0 : Int) + d92 p := by
  omega
theorem compare902 (p : Pattern) (guard : d915 p = 1) : d93 p ≤ (0 : Int) + d357 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d93, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d915, d93, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d93, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare896 p hg
    simpa only [d915, d93, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare903 (p : Pattern) (guard : d915 p = 1) : d94 p ≤ (0 : Int) + d358 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d94, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d94, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d94, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d94, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare904 (p : Pattern) (guard : d915 p = 1) : d95 p ≤ (0 : Int) + d359 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d95, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d95, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d95, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare903 p hg
    simpa only [d95, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare905 (p : Pattern) (guard : d915 p = 1) : d96 p ≤ (0 : Int) + d360 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d96, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare852 p hg
    simpa only [d96, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d96, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare904 p hg
    simpa only [d96, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare906 (p : Pattern) (guard : d0 p = 1) : d98 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare907 (p : Pattern) (guard : d915 p = 1) : d98 p ≤ (0 : Int) + d361 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare906 p hg
    simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare908 (p : Pattern) (guard : d915 p = 1) : d99 p ≤ (0 : Int) + d361 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d99, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d915, d99, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d99, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare877 p hg
    simpa only [d915, d99, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare909 (p : Pattern) (guard : d915 p = 1) : d100 p ≤ (0 : Int) + d361 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare910 (p : Pattern) (guard : d915 p = 1) : d101 p ≤ (0 : Int) + d362 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d101, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d101, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d101, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare878 p hg
    simpa only [d101, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare911 (p : Pattern) (guard : d915 p = 1) : d102 p ≤ (0 : Int) + d363 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d102, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare909 p hg
    simpa only [d102, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d102, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare910 p hg
    simpa only [d102, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare912 (p : Pattern) (guard : d915 p = 1) : d103 p ≤ (0 : Int) + d364 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare911 p hg
    simpa only [d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare913 (p : Pattern) (guard : d915 p = 1) : d104 p ≤ (0 : Int) + d365 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d104, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare897 p hg
    simpa only [d104, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d104, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare883 p hg
    simpa only [d104, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare914 (p : Pattern) (guard : d915 p = 1) : d105 p ≤ (0 : Int) + d366 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d105, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d105, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d105, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d105, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare915 (p : Pattern) (guard : d915 p = 1) : d106 p ≤ (0 : Int) + d367 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d106, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d106, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d106, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare914 p hg
    simpa only [d106, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare916 (p : Pattern) (guard : d915 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare917 (p : Pattern) (guard : d915 p = 1) : d107 p ≤ (0 : Int) + d368 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d107, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d107, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d107, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d107, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare918 (p : Pattern) (guard : d915 p = 1) : d108 p ≤ (0 : Int) + d369 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d108, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare909 p hg
    simpa only [d108, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d108, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare917 p hg
    simpa only [d108, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare919 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare920 (p : Pattern) (guard : d915 p = 1) : d97 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare921 (p : Pattern) (guard : d915 p = 1) : d109 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d109, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d915, d109, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d109, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d915, d109, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare922 (p : Pattern) (guard : d915 p = 1) : d110 p ≤ (0 : Int) + d370 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare921 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare923 (p : Pattern) (guard : d915 p = 1) : d111 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d111, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare921 p hg
    simpa only [d111, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d111, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d111, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare924 (p : Pattern) (guard : d915 p = 1) : d112 p ≤ (0 : Int) + d372 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d112, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare922 p hg
    simpa only [d112, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d112, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare923 p hg
    simpa only [d112, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare925 (p : Pattern) (guard : d915 p = 1) : d113 p ≤ (0 : Int) + d373 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d113, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare918 p hg
    simpa only [d113, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d113, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare924 p hg
    simpa only [d113, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare926 (p : Pattern) (guard : d915 p = 1) : d114 p ≤ (0 : Int) + d374 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d114, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare915 p hg
    simpa only [d114, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d114, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare925 p hg
    simpa only [d114, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare927 (p : Pattern) (guard : d915 p = 1) : d115 p ≤ (0 : Int) + d375 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d115, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare912 p hg
    simpa only [d115, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d115, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare926 p hg
    simpa only [d115, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare928 (p : Pattern) (guard : d915 p = 1) : d116 p ≤ (0 : Int) + d376 p := by
  cases selected : p 86 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d116, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare893 p hg
    simpa only [d116, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d116, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d116, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare929 (p : Pattern) (guard : d915 p = 1) : d117 p ≤ (0 : Int) + d377 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d117, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d117, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d117, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare891 p hg
    simpa only [d117, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare930 (p : Pattern) (guard : d915 p = 1) : d118 p ≤ (0 : Int) + d378 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d118, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare875 p hg
    simpa only [d118, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d118, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare929 p hg
    simpa only [d118, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare931 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare932 (p : Pattern) (guard : d915 p = 1) : d121 p ≤ (0 : Int) + d356 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d121, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d121, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d121, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare931 p hg
    simpa only [d915, d121, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare933 (p : Pattern) (guard : d915 p = 1) : d122 p ≤ (0 : Int) + d358 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d122, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare932 p hg
    simpa only [d122, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d122, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d122, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare934 (p : Pattern) (guard : d915 p = 1) : d123 p ≤ (0 : Int) + d359 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d123, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d123, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d123, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare933 p hg
    simpa only [d123, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare935 (p : Pattern) (guard : d915 p = 1) : d124 p ≤ (0 : Int) + d360 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare852 p hg
    simpa only [d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare934 p hg
    simpa only [d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare936 (p : Pattern) (guard : d915 p = 1) : d125 p ≤ (0 : Int) + d379 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d125, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare921 p hg
    simpa only [d125, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d125, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare883 p hg
    simpa only [d125, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare937 (p : Pattern) (guard : d915 p = 1) : d126 p ≤ (0 : Int) + d380 p := by
  cases selected : p 132 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d126, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare922 p hg
    simpa only [d126, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d126, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare936 p hg
    simpa only [d126, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare938 (p : Pattern) (guard : d915 p = 1) : d127 p ≤ (0 : Int) + d381 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d127, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare911 p hg
    simpa only [d127, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d127, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare937 p hg
    simpa only [d127, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare939 (p : Pattern) (guard : d915 p = 1) : d128 p ≤ (0 : Int) + d382 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d128, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare935 p hg
    simpa only [d128, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d128, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare938 p hg
    simpa only [d128, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare940 (p : Pattern) (guard : d915 p = 1) : d129 p ≤ (0 : Int) + d383 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d129, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d129, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d129, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare890 p hg
    simpa only [d129, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare941 (p : Pattern) (guard : d915 p = 1) : d130 p ≤ (0 : Int) + d384 p := by
  cases selected : p 113 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d130, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare924 p hg
    simpa only [d130, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d130, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d130, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare942 (p : Pattern) (guard : d915 p = 1) : d131 p ≤ (0 : Int) + d385 p := by
  cases selected : p 112 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d131, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare940 p hg
    simpa only [d131, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d131, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare941 p hg
    simpa only [d131, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare943 (p : Pattern) (guard : d915 p = 1) : d132 p ≤ (0 : Int) + d386 p := by
  cases selected : p 106 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d132, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare939 p hg
    simpa only [d132, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d132, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare942 p hg
    simpa only [d132, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare944 (p : Pattern) (guard : d915 p = 1) : d133 p ≤ (0 : Int) + d387 p := by
  cases selected : p 86 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d133, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare930 p hg
    simpa only [d133, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d133, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare943 p hg
    simpa only [d133, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare945 (p : Pattern) (guard : d915 p = 1) : d134 p ≤ (0 : Int) + d388 p := by
  cases selected : p 80 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d134, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare928 p hg
    simpa only [d134, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d134, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare944 p hg
    simpa only [d134, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare946 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d920 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare947 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare948 (p : Pattern) (guard : d917 p = 1) : d4 p ≤ (0 : Int) + d3 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d917, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare947 p hg
    simpa only [d917, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare949 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare950 (p : Pattern) (guard : d917 p = 1) : d5 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d917, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d917, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare951 (p : Pattern) (guard : d917 p = 1) : d6 p ≤ (0 : Int) + d744 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d6, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d6, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d6, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare950 p hg
    simpa only [d6, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare952 (p : Pattern) (guard : d917 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare953 (p : Pattern) (guard : d917 p = 1) : d7 p ≤ (0 : Int) + d744 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d7, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d7, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d7, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d7, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare954 (p : Pattern) (guard : d917 p = 1) : d8 p ≤ (0 : Int) + d744 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare951 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare953 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare955 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare956 (p : Pattern) (guard : d917 p = 1) : d10 p ≤ (0 : Int) + d9 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare699 p hg
    simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare957 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d917, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d917, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare958 (p : Pattern) (guard : d917 p = 1) : d12 p ≤ (0 : Int) + d747 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d12, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d12, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d12, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d12, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare959 (p : Pattern) (guard : d917 p = 1) : d13 p ≤ (0 : Int) + d747 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d13, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d13, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d13, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d13, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare960 (p : Pattern) (guard : d917 p = 1) : d14 p ≤ (0 : Int) + d747 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare958 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare959 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare961 (p : Pattern) (guard : d917 p = 1) : d15 p ≤ (0 : Int) + d919 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d15, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare954 p hg
    simpa only [d15, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d15, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare960 p hg
    simpa only [d15, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare962 (p : Pattern) (guard : d917 p = 1) : d16 p ≤ (0 : Int) + d920 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d16, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare954 p hg
    simpa only [d16, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d16, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare961 p hg
    simpa only [d16, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare963 (p : Pattern) (guard : d918 p = 1) : d16 p ≤ (0 : Int) + d920 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare946 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare962 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare964 (p : Pattern) (guard : d917 p = 1) : d17 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d917, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d917, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare965 (p : Pattern) (guard : d917 p = 1) : d18 p ≤ (0 : Int) + d744 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d18, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d18, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d18, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare964 p hg
    simpa only [d18, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare966 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  omega
theorem compare967 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare968 (p : Pattern) (guard : d917 p = 1) : d17 p ≤ (0 : Int) + d3 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare966 p hg
    simpa only [d917, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d917, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare969 (p : Pattern) (guard : d917 p = 1) : d19 p ≤ (0 : Int) + d744 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d19, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare968 p hg
    simpa only [d19, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d19, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d19, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare970 (p : Pattern) (guard : d917 p = 1) : d20 p ≤ (0 : Int) + d744 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare965 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare969 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare971 (p : Pattern) (guard : d917 p = 1) : d21 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d917, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d917, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare972 (p : Pattern) (guard : d917 p = 1) : d22 p ≤ (0 : Int) + d747 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d22, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d22, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d22, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare971 p hg
    simpa only [d22, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare973 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  omega
theorem compare974 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare975 (p : Pattern) (guard : d917 p = 1) : d21 p ≤ (0 : Int) + d9 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare973 p hg
    simpa only [d917, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare974 p hg
    simpa only [d917, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare976 (p : Pattern) (guard : d917 p = 1) : d23 p ≤ (0 : Int) + d747 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d23, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare975 p hg
    simpa only [d23, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d23, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d23, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare977 (p : Pattern) (guard : d917 p = 1) : d24 p ≤ (0 : Int) + d747 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare972 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare976 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare978 (p : Pattern) (guard : d917 p = 1) : d25 p ≤ (0 : Int) + d919 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d25, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare970 p hg
    simpa only [d25, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d25, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare977 p hg
    simpa only [d25, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare979 (p : Pattern) (guard : d917 p = 1) : d26 p ≤ (0 : Int) + d920 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d26, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare970 p hg
    simpa only [d26, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d26, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare978 p hg
    simpa only [d26, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
