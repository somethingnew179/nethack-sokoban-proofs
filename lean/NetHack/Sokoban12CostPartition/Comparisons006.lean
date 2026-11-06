/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare840 (p : Pattern) (guard : d849 p = 1) : d73 p ≤ (0 : Int) + d354 p := by
  cases selected : p 133 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d849, d73, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare839 p hg
    simpa only [d849, d73, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d848 p = 1 := by simpa only [d849, d73, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d849, d73, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare841 (p : Pattern) (guard : d849 p = 1) : d74 p ≤ (0 : Int) + d355 p := by
  cases selected : p 132 with
  | false =>
    have hg : d849 p = 1 := by simpa only [d74, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare838 p hg
    simpa only [d74, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d849 p = 1 := by simpa only [d74, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare840 p hg
    simpa only [d74, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare842 (p : Pattern) (guard : d849 p = 1) : d74 p ≤ (0 : Int) + d356 p := by
  cases selected : p 108 with
  | false =>
    have hg : d849 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare826 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d849 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare841 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare843 (p : Pattern) (guard : d1 p = 1) : d236 p ≤ (0 : Int) + d236 p := by
  omega
theorem compare844 (p : Pattern) (guard : d851 p = 1) : d236 p ≤ (0 : Int) + d236 p := by
  omega
theorem compare845 (p : Pattern) (guard : d0 p = 1) : d227 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare846 (p : Pattern) (guard : d737 p = 1) : d228 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d228, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare186 p hg
    simpa only [d737, d228, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d228, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d737, d228, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare847 (p : Pattern) (guard : d0 p = 1) : d231 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare848 (p : Pattern) (guard : d737 p = 1) : d232 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d232, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare189 p hg
    simpa only [d737, d232, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d232, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d737, d232, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare849 (p : Pattern) (guard : d737 p = 1) : d233 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d233, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare846 p hg
    simpa only [d233, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d233, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare848 p hg
    simpa only [d233, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare850 (p : Pattern) (guard : d737 p = 1) : d234 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d234, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare848 p hg
    simpa only [d234, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d234, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare193 p hg
    simpa only [d234, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare851 (p : Pattern) (guard : d737 p = 1) : d235 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d235, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare849 p hg
    simpa only [d235, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d235, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare850 p hg
    simpa only [d235, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare852 (p : Pattern) (guard : d737 p = 1) : d236 p ≤ (0 : Int) + d74 p := by
  cases selected : p 108 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare163 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare853 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (2 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare854 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare78 p hg
    simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare855 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare856 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare854 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare857 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare858 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare857 p hg
    simpa only [d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare859 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare860 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare859 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare861 (p : Pattern) (guard : d1 p = 1) : d227 p ≤ (2 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d227, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare856 p hg
    simpa only [d227, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d227, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare860 p hg
    simpa only [d227, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare862 (p : Pattern) (guard : d736 p = 1) : d228 p ≤ (2 : Int) + d70 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d736, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d736, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare861 p hg
    simpa only [d736, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare863 (p : Pattern) (guard : d0 p = 1) : d232 p ≤ (2 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare864 (p : Pattern) (guard : d810 p = 1) : d233 p ≤ (2 : Int) + d70 p := by
  cases selected : p 133 with
  | false =>
    have hg : d736 p = 1 := by simpa only [d810, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare862 p hg
    simpa only [d810, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d810, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare863 p hg
    simpa only [d810, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare865 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (2 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare866 (p : Pattern) (guard : d1 p = 1) : d229 p ≤ (2 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare867 (p : Pattern) (guard : d1 p = 1) : d230 p ≤ (2 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare859 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare868 (p : Pattern) (guard : d1 p = 1) : d231 p ≤ (2 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare869 (p : Pattern) (guard : d736 p = 1) : d232 p ≤ (2 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare865 p hg
    simpa only [d736, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d736, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d736, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare870 (p : Pattern) (guard : d810 p = 1) : d234 p ≤ (2 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d736 p = 1 := by simpa only [d810, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare869 p hg
    simpa only [d810, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d810, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d810, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare871 (p : Pattern) (guard : d810 p = 1) : d235 p ≤ (2 : Int) + d852 p := by
  cases selected : p 132 with
  | false =>
    have hg : d810 p = 1 := by simpa only [d235, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare864 p hg
    simpa only [d235, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d810 p = 1 := by simpa only [d235, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d235, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare872 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare873 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare92 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare874 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (2 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare872 p hg
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare873 p hg
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare875 (p : Pattern) (guard : d736 p = 1) : d67 p ≤ (2 : Int) + d70 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d736, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d736, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare874 p hg
    simpa only [d736, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare876 (p : Pattern) (guard : d0 p = 1) : d71 p ≤ (2 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare877 (p : Pattern) (guard : d810 p = 1) : d72 p ≤ (2 : Int) + d70 p := by
  cases selected : p 133 with
  | false =>
    have hg : d736 p = 1 := by simpa only [d810, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare875 p hg
    simpa only [d810, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d810, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare876 p hg
    simpa only [d810, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare878 (p : Pattern) (guard : d736 p = 1) : d71 p ≤ (2 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare865 p hg
    simpa only [d736, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d736, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d736, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare879 (p : Pattern) (guard : d810 p = 1) : d73 p ≤ (2 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d736 p = 1 := by simpa only [d810, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare878 p hg
    simpa only [d810, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d810, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d810, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare880 (p : Pattern) (guard : d810 p = 1) : d74 p ≤ (2 : Int) + d852 p := by
  cases selected : p 132 with
  | false =>
    have hg : d810 p = 1 := by simpa only [d74, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare877 p hg
    simpa only [d74, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d810 p = 1 := by simpa only [d74, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare879 p hg
    simpa only [d74, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare881 (p : Pattern) (guard : d810 p = 1) : d236 p ≤ (2 : Int) + d852 p := by
  cases selected : p 108 with
  | false =>
    have hg : d810 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare871 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d810 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare880 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare882 (p : Pattern) (guard : d755 p = 1) : d236 p ≤ (0 : Int) + d75 p := by
  cases selected : p 108 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d755, d236, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d755, d236, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d755, d236, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare751 p hg
    simpa only [d755, d236, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare883 (p : Pattern) (guard : d758 p = 1) : d227 p ≤ (0 : Int) + d227 p := by
  omega
theorem compare884 (p : Pattern) (guard : d758 p = 1) : d228 p ≤ (0 : Int) + d227 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare883 p hg
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare885 (p : Pattern) (guard : d758 p = 1) : d231 p ≤ (0 : Int) + d231 p := by
  omega
theorem compare886 (p : Pattern) (guard : d758 p = 1) : d232 p ≤ (0 : Int) + d231 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare887 (p : Pattern) (guard : d758 p = 1) : d233 p ≤ (0 : Int) + d366 p := by
  cases selected : p 133 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d233, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare884 p hg
    simpa only [d233, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d233, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare886 p hg
    simpa only [d233, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare888 (p : Pattern) (guard : d758 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare889 (p : Pattern) (guard : d758 p = 1) : d234 p ≤ (0 : Int) + d367 p := by
  cases selected : p 133 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d234, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare886 p hg
    simpa only [d234, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d234, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d234, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare890 (p : Pattern) (guard : d758 p = 1) : d235 p ≤ (0 : Int) + d368 p := by
  cases selected : p 132 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d235, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare887 p hg
    simpa only [d235, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d235, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare889 p hg
    simpa only [d235, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare891 (p : Pattern) (guard : d758 p = 1) : d67 p ≤ (0 : Int) + d369 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d67, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare892 (p : Pattern) (guard : d758 p = 1) : d71 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d71, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare893 (p : Pattern) (guard : d758 p = 1) : d72 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d72, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare891 p hg
    simpa only [d72, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d72, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare892 p hg
    simpa only [d72, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare894 (p : Pattern) (guard : d758 p = 1) : d73 p ≤ (0 : Int) + d372 p := by
  cases selected : p 133 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare892 p hg
    simpa only [d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d73, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare895 (p : Pattern) (guard : d758 p = 1) : d74 p ≤ (0 : Int) + d373 p := by
  cases selected : p 132 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d74, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare893 p hg
    simpa only [d74, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d74, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare894 p hg
    simpa only [d74, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare896 (p : Pattern) (guard : d758 p = 1) : d236 p ≤ (0 : Int) + d374 p := by
  cases selected : p 108 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d236, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare890 p hg
    simpa only [d236, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d236, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d236, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare897 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (0 : Int) + d258 p := by
  omega
theorem compare898 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare899 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare283 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare900 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare901 (p : Pattern) (guard : d854 p = 1) : d7 p ≤ (0 : Int) + d6 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d854, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d854, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare902 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare903 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare904 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare905 (p : Pattern) (guard : d854 p = 1) : d55 p ≤ (0 : Int) + d54 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare903 p hg
    simpa only [d854, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare904 p hg
    simpa only [d854, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare906 (p : Pattern) (guard : d854 p = 1) : d56 p ≤ (0 : Int) + d855 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d56, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d56, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d56, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d56, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare907 (p : Pattern) (guard : d854 p = 1) : d57 p ≤ (0 : Int) + d856 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d57, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d57, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d57, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare906 p hg
    simpa only [d57, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare908 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d8 p := by
  omega
theorem compare909 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare297 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare910 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare911 (p : Pattern) (guard : d854 p = 1) : d11 p ≤ (0 : Int) + d10 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare909 p hg
    simpa only [d854, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare910 p hg
    simpa only [d854, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare912 (p : Pattern) (guard : d854 p = 1) : d12 p ≤ (0 : Int) + d857 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d12, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d12, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d12, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare911 p hg
    simpa only [d12, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare913 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  omega
theorem compare914 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare299 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare915 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare916 (p : Pattern) (guard : d854 p = 1) : d60 p ≤ (0 : Int) + d59 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare914 p hg
    simpa only [d854, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare915 p hg
    simpa only [d854, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare917 (p : Pattern) (guard : d854 p = 1) : d61 p ≤ (0 : Int) + d858 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d61, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare911 p hg
    simpa only [d61, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d61, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d61, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare918 (p : Pattern) (guard : d854 p = 1) : d62 p ≤ (0 : Int) + d859 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d62, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare906 p hg
    simpa only [d62, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d62, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare917 p hg
    simpa only [d62, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare919 (p : Pattern) (guard : d854 p = 1) : d63 p ≤ (0 : Int) + d860 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d63, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare912 p hg
    simpa only [d63, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d63, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare918 p hg
    simpa only [d63, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare920 (p : Pattern) (guard : d854 p = 1) : d64 p ≤ (0 : Int) + d861 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d64, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d64, d861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d64, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d64, d861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare921 (p : Pattern) (guard : d854 p = 1) : d106 p ≤ (0 : Int) + d862 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d106, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d106, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d106, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d106, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare922 (p : Pattern) (guard : d854 p = 1) : d119 p ≤ (0 : Int) + d863 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d119, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d119, d863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d119, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d119, d863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare923 (p : Pattern) (guard : d854 p = 1) : d120 p ≤ (0 : Int) + d864 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d120, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d120, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d120, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare922 p hg
    simpa only [d120, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare924 (p : Pattern) (guard : d854 p = 1) : d121 p ≤ (0 : Int) + d865 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d121, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare923 p hg
    simpa only [d121, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d121, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d121, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare925 (p : Pattern) (guard : d854 p = 1) : d122 p ≤ (0 : Int) + d866 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d122, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare921 p hg
    simpa only [d122, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d122, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare924 p hg
    simpa only [d122, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare926 (p : Pattern) (guard : d854 p = 1) : d179 p ≤ (0 : Int) + d867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d179, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare921 p hg
    simpa only [d179, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d179, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare925 p hg
    simpa only [d179, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare927 (p : Pattern) (guard : d854 p = 1) : d65 p ≤ (0 : Int) + d868 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d65, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d65, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d65, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d65, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare928 (p : Pattern) (guard : d854 p = 1) : d109 p ≤ (0 : Int) + d869 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d109, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare912 p hg
    simpa only [d109, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d109, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d109, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare929 (p : Pattern) (guard : d854 p = 1) : d125 p ≤ (0 : Int) + d870 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d125, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare911 p hg
    simpa only [d125, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d125, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d125, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare930 (p : Pattern) (guard : d854 p = 1) : d126 p ≤ (0 : Int) + d871 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d126, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare911 p hg
    simpa only [d126, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d126, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare929 p hg
    simpa only [d126, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare931 (p : Pattern) (guard : d854 p = 1) : d127 p ≤ (0 : Int) + d872 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d127, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare923 p hg
    simpa only [d127, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d127, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare930 p hg
    simpa only [d127, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare932 (p : Pattern) (guard : d854 p = 1) : d128 p ≤ (0 : Int) + d873 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d128, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare931 p hg
    simpa only [d128, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d128, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d128, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare933 (p : Pattern) (guard : d854 p = 1) : d129 p ≤ (0 : Int) + d874 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d129, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare928 p hg
    simpa only [d129, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d129, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare932 p hg
    simpa only [d129, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare934 (p : Pattern) (guard : d854 p = 1) : d237 p ≤ (0 : Int) + d875 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d237, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare928 p hg
    simpa only [d237, d875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d237, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare933 p hg
    simpa only [d237, d875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare935 (p : Pattern) (guard : d854 p = 1) : d238 p ≤ (0 : Int) + d876 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d238, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare926 p hg
    simpa only [d238, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d238, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare934 p hg
    simpa only [d238, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare936 (p : Pattern) (guard : d854 p = 1) : d239 p ≤ (0 : Int) + d877 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d239, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d239, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d239, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare935 p hg
    simpa only [d239, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare937 (p : Pattern) (guard : d854 p = 1) : d68 p ≤ (0 : Int) + d878 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d68, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d68, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d68, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d68, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare938 (p : Pattern) (guard : d854 p = 1) : d69 p ≤ (0 : Int) + d879 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d69, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d69, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d69, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d69, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare939 (p : Pattern) (guard : d854 p = 1) : d70 p ≤ (0 : Int) + d880 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d70, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare937 p hg
    simpa only [d70, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d70, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare938 p hg
    simpa only [d70, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare940 (p : Pattern) (guard : d854 p = 1) : d181 p ≤ (0 : Int) + d881 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d181, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare925 p hg
    simpa only [d181, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d181, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d181, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare941 (p : Pattern) (guard : d854 p = 1) : d240 p ≤ (0 : Int) + d882 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d240, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare933 p hg
    simpa only [d240, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d240, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d240, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare942 (p : Pattern) (guard : d854 p = 1) : d241 p ≤ (0 : Int) + d883 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d241, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare940 p hg
    simpa only [d241, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d241, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare941 p hg
    simpa only [d241, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare943 (p : Pattern) (guard : d854 p = 1) : d242 p ≤ (0 : Int) + d884 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d242, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare939 p hg
    simpa only [d242, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d242, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare942 p hg
    simpa only [d242, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare944 (p : Pattern) (guard : d854 p = 1) : d243 p ≤ (0 : Int) + d885 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d243, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare936 p hg
    simpa only [d243, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d243, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare943 p hg
    simpa only [d243, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare945 (p : Pattern) (guard : d854 p = 1) : d66 p ≤ (0 : Int) + d886 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare946 (p : Pattern) (guard : d854 p = 1) : d244 p ≤ (0 : Int) + d887 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d244, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare943 p hg
    simpa only [d244, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d244, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare945 p hg
    simpa only [d244, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare947 (p : Pattern) (guard : d854 p = 1) : d245 p ≤ (0 : Int) + d888 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d245, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare944 p hg
    simpa only [d245, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d245, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare946 p hg
    simpa only [d245, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare948 (p : Pattern) (guard : d854 p = 1) : d137 p ≤ (0 : Int) + d889 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d137, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare922 p hg
    simpa only [d137, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d137, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d137, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare949 (p : Pattern) (guard : d854 p = 1) : d139 p ≤ (0 : Int) + d890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d139, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare923 p hg
    simpa only [d139, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d139, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d139, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare950 (p : Pattern) (guard : d854 p = 1) : d153 p ≤ (0 : Int) + d891 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d153, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d153, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d153, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d153, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare951 (p : Pattern) (guard : d854 p = 1) : d186 p ≤ (0 : Int) + d892 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d186, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d186, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d186, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare950 p hg
    simpa only [d186, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare952 (p : Pattern) (guard : d854 p = 1) : d143 p ≤ (0 : Int) + d893 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d143, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare929 p hg
    simpa only [d143, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d143, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d143, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare953 (p : Pattern) (guard : d854 p = 1) : d144 p ≤ (0 : Int) + d894 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d144, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d144, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d144, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d144, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare954 (p : Pattern) (guard : d854 p = 1) : d146 p ≤ (0 : Int) + d895 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d146, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare931 p hg
    simpa only [d146, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d146, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare953 p hg
    simpa only [d146, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare955 (p : Pattern) (guard : d854 p = 1) : d155 p ≤ (0 : Int) + d896 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d155, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d155, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d155, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare954 p hg
    simpa only [d155, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare956 (p : Pattern) (guard : d854 p = 1) : d246 p ≤ (0 : Int) + d897 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d246, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d246, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d246, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d246, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare957 (p : Pattern) (guard : d854 p = 1) : d247 p ≤ (0 : Int) + d898 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d247, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare951 p hg
    simpa only [d247, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d247, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d247, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare958 (p : Pattern) (guard : d854 p = 1) : d248 p ≤ (0 : Int) + d899 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d248, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d248, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d248, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare945 p hg
    simpa only [d248, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare959 (p : Pattern) (guard : d854 p = 1) : d138 p ≤ (0 : Int) + d900 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d138, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d138, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d138, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d138, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare960 (p : Pattern) (guard : d854 p = 1) : d140 p ≤ (0 : Int) + d901 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d140, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare959 p hg
    simpa only [d140, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d140, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d140, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare961 (p : Pattern) (guard : d854 p = 1) : d188 p ≤ (0 : Int) + d902 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d188, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare960 p hg
    simpa only [d188, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d188, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d188, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare962 (p : Pattern) (guard : d854 p = 1) : d145 p ≤ (0 : Int) + d903 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d145, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare912 p hg
    simpa only [d145, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d145, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare953 p hg
    simpa only [d145, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare963 (p : Pattern) (guard : d854 p = 1) : d147 p ≤ (0 : Int) + d904 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d147, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare962 p hg
    simpa only [d147, d904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d147, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare954 p hg
    simpa only [d147, d904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare964 (p : Pattern) (guard : d854 p = 1) : d249 p ≤ (0 : Int) + d905 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d249, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare963 p hg
    simpa only [d249, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d249, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d249, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare965 (p : Pattern) (guard : d854 p = 1) : d250 p ≤ (0 : Int) + d906 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d250, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare961 p hg
    simpa only [d250, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d250, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare964 p hg
    simpa only [d250, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare966 (p : Pattern) (guard : d854 p = 1) : d251 p ≤ (0 : Int) + d907 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d251, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare965 p hg
    simpa only [d251, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d251, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare945 p hg
    simpa only [d251, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare967 (p : Pattern) (guard : d854 p = 1) : d252 p ≤ (0 : Int) + d908 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d252, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare958 p hg
    simpa only [d252, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d252, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare966 p hg
    simpa only [d252, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare968 (p : Pattern) (guard : d854 p = 1) : d191 p ≤ (0 : Int) + d909 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d191, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare950 p hg
    simpa only [d191, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d191, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d191, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare969 (p : Pattern) (guard : d854 p = 1) : d253 p ≤ (0 : Int) + d910 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d253, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d253, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d253, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d253, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare970 (p : Pattern) (guard : d854 p = 1) : d254 p ≤ (0 : Int) + d911 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d254, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare968 p hg
    simpa only [d254, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d254, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare969 p hg
    simpa only [d254, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare971 (p : Pattern) (guard : d854 p = 1) : d255 p ≤ (0 : Int) + d912 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d255, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare970 p hg
    simpa only [d255, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d255, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare945 p hg
    simpa only [d255, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare972 (p : Pattern) (guard : d854 p = 1) : d256 p ≤ (0 : Int) + d913 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d256, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare971 p hg
    simpa only [d256, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d256, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare945 p hg
    simpa only [d256, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare973 (p : Pattern) (guard : d854 p = 1) : d257 p ≤ (0 : Int) + d914 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d257, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d257, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d257, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare972 p hg
    simpa only [d257, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare974 (p : Pattern) (guard : d854 p = 1) : d258 p ≤ (0 : Int) + d915 p := by
  cases selected : p 108 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d258, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare947 p hg
    simpa only [d258, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d258, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare973 p hg
    simpa only [d258, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare975 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d267 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare976 (p : Pattern) (guard : d768 p = 1) : d64 p ≤ (0 : Int) + d268 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d64, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d768, d64, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d64, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare975 p hg
    simpa only [d768, d64, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare977 (p : Pattern) (guard : d0 p = 1) : d237 p ≤ (0 : Int) + d278 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare978 (p : Pattern) (guard : d768 p = 1) : d238 p ≤ (0 : Int) + d279 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d238, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d768, d238, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d238, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare977 p hg
    simpa only [d768, d238, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare979 (p : Pattern) (guard : d768 p = 1) : d239 p ≤ (0 : Int) + d280 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d239, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare976 p hg
    simpa only [d239, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d239, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare978 p hg
    simpa only [d239, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
