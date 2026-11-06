/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare840 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (0 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare838 p hg
    simpa only [d78, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare839 p hg
    simpa only [d78, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare841 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (0 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare835 p hg
    simpa only [d79, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare840 p hg
    simpa only [d79, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare842 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (0 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare841 p hg
    simpa only [d80, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d80, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare843 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (0 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare842 p hg
    simpa only [d81, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d81, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare844 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (0 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare833 p hg
    simpa only [d82, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d82, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare845 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d53 p := by
  omega
theorem compare846 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare847 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d20 p := by
  omega
theorem compare848 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (0 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d55, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare830 p hg
    simpa only [d55, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare849 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare846 p hg
    simpa only [d56, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare848 p hg
    simpa only [d56, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare850 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare851 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare850 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare852 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare826 p hg
    simpa only [d61, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d61, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare853 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare852 p hg
    simpa only [d64, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d64, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare854 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare849 p hg
    simpa only [d65, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d65, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare855 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (0 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare840 p hg
    simpa only [d83, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d83, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare856 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (0 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d84, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d84, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare857 (p : Pattern) (guard : d1 p = 1) : d85 p ≤ (0 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d85, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare856 p hg
    simpa only [d85, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d85, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d85, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare858 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (0 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare854 p hg
    simpa only [d86, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare857 p hg
    simpa only [d86, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare859 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (0 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare844 p hg
    simpa only [d87, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d87, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare860 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (0 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare821 p hg
    simpa only [d88, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare859 p hg
    simpa only [d88, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare861 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (0 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare859 p hg
    simpa only [d99, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d99, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare862 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (0 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d100, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare860 p hg
    simpa only [d100, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d100, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare861 p hg
    simpa only [d100, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare863 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare862 p hg
    simpa only [d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare864 (p : Pattern) (guard : d0 p = 1) : d209 p ≤ (0 : Int) + d209 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare865 (p : Pattern) (guard : d4042 p = 1) : d210 p ≤ (0 : Int) + d209 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare863 p hg
    simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare864 p hg
    simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare866 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d12 p := by
  change (9 : Int) ≤ (0 : Int) + 12
  decide
theorem compare867 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare868 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare869 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare870 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare869 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare871 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare872 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare725 p hg
    simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare871 p hg
    simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare873 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare874 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare873 p hg
    simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare875 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare872 p hg
    simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare874 p hg
    simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare876 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare877 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare876 p hg
    simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare878 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (0 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare739 p hg
    simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare877 p hg
    simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare879 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare816 p hg
    simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare880 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare879 p hg
    simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare881 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (0 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare878 p hg
    simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare880 p hg
    simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare882 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (0 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare875 p hg
    simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare881 p hg
    simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare883 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (0 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare723 p hg
    simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare884 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare875 p hg
    simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare757 p hg
    simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare885 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare754 p hg
    simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare884 p hg
    simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare886 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare883 p hg
    simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare887 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare888 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare886 p hg
    simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare887 p hg
    simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare889 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) ≤ (0 : Int) + 3
  decide
theorem compare890 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare889 p hg
    simpa only [d13, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare891 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare889 p hg
    simpa only [d14, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare890 p hg
    simpa only [d14, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare892 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare891 p hg
    simpa only [d33, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare701 p hg
    simpa only [d33, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare893 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (0 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare891 p hg
    simpa only [d37, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d37, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare894 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (0 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare892 p hg
    simpa only [d38, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare893 p hg
    simpa only [d38, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare895 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem compare896 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d13, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare897 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d14, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare896 p hg
    simpa only [d14, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare898 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare897 p hg
    simpa only [d42, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare712 p hg
    simpa only [d42, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare899 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d12 p := by
  change (4 : Int) ≤ (0 : Int) + 12
  decide
theorem compare900 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare901 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare902 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare903 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d44, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d44, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare904 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (0 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare894 p hg
    simpa only [d45, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare903 p hg
    simpa only [d45, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare905 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) ≤ (0 : Int) + 7
  decide
theorem compare906 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d13, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare907 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d14, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare906 p hg
    simpa only [d14, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare908 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d46, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d46, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare909 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d47, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d47, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare910 (p : Pattern) (guard : d1 p = 1) : d49 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare876 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare911 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (0 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare909 p hg
    simpa only [d50, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare910 p hg
    simpa only [d50, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare912 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (0 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare904 p hg
    simpa only [d51, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare911 p hg
    simpa only [d51, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare913 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (0 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d52, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare912 p hg
    simpa only [d52, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare914 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (0 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare897 p hg
    simpa only [d37, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d37, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare915 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d5 p := by
  change (2 : Int) ≤ (0 : Int) + 5
  decide
theorem compare916 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare915 p hg
    simpa only [d30, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare917 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare915 p hg
    simpa only [d31, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d31, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare918 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare917 p hg
    simpa only [d66, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d66, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare919 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (0 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare914 p hg
    simpa only [d67, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare918 p hg
    simpa only [d67, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare920 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d7 p := by
  change (4 : Int) ≤ (0 : Int) + 7
  decide
theorem compare921 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare922 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d18, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare921 p hg
    simpa only [d18, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare923 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare922 p hg
    simpa only [d43, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d43, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare924 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare923 p hg
    simpa only [d68, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare876 p hg
    simpa only [d68, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare925 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (0 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d69, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare924 p hg
    simpa only [d69, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare926 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d9 p := by
  change (4 : Int) ≤ (0 : Int) + 9
  decide
theorem compare927 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare926 p hg
    simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare928 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare926 p hg
    simpa only [d18, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d18, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare929 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare928 p hg
    simpa only [d43, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d43, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare930 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare929 p hg
    simpa only [d71, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare816 p hg
    simpa only [d71, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare931 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (0 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare930 p hg
    simpa only [d74, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d74, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare932 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (0 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare925 p hg
    simpa only [d75, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare931 p hg
    simpa only [d75, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare933 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (0 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare875 p hg
    simpa only [d76, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare932 p hg
    simpa only [d76, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare934 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (0 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d77, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare933 p hg
    simpa only [d77, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare935 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare891 p hg
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare936 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare891 p hg
    simpa only [d16, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare935 p hg
    simpa only [d16, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare937 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d11 p := by
  change (4 : Int) ≤ (0 : Int) + 11
  decide
theorem compare938 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare937 p hg
    simpa only [d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare939 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare937 p hg
    simpa only [d18, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare938 p hg
    simpa only [d18, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare940 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare939 p hg
    simpa only [d19, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d19, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare941 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare939 p hg
    simpa only [d20, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare940 p hg
    simpa only [d20, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare942 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare936 p hg
    simpa only [d21, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare941 p hg
    simpa only [d21, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare943 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d22, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare942 p hg
    simpa only [d22, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare944 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare897 p hg
    simpa only [d15, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare945 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare897 p hg
    simpa only [d16, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare944 p hg
    simpa only [d16, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare946 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare945 p hg
    simpa only [d21, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare941 p hg
    simpa only [d21, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare947 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare948 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare946 p hg
    simpa only [d28, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare947 p hg
    simpa only [d28, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare949 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare943 p hg
    simpa only [d29, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d29, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare950 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d7 p := by
  change (2 : Int) ≤ (0 : Int) + 7
  decide
theorem compare951 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare950 p hg
    simpa only [d30, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare952 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare950 p hg
    simpa only [d31, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare951 p hg
    simpa only [d31, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare953 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d32, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d32, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare954 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d53, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare953 p hg
    simpa only [d53, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare955 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d12 p := by
  change (6 : Int) ≤ (0 : Int) + 12
  decide
theorem compare956 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare957 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare958 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare959 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare958 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare960 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare954 p hg
    simpa only [d79, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare959 p hg
    simpa only [d79, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare961 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare960 p hg
    simpa only [d80, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d80, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare962 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare961 p hg
    simpa only [d81, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d81, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare963 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (0 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d82, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare962 p hg
    simpa only [d82, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare964 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare936 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare724 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare965 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare964 p hg
    simpa only [d56, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare871 p hg
    simpa only [d56, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare966 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare922 p hg
    simpa only [d19, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d19, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare967 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare922 p hg
    simpa only [d20, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare966 p hg
    simpa only [d20, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare968 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d61, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d61, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare969 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare968 p hg
    simpa only [d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d64, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare970 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare965 p hg
    simpa only [d65, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare969 p hg
    simpa only [d65, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare971 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d9 p := by
  change (6 : Int) ≤ (0 : Int) + 9
  decide
theorem compare972 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare971 p hg
    simpa only [d34, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d34, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare973 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare971 p hg
    simpa only [d35, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare972 p hg
    simpa only [d35, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare974 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare973 p hg
    simpa only [d36, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d36, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare975 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare973 p hg
    simpa only [d78, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare974 p hg
    simpa only [d78, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare976 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare975 p hg
    simpa only [d83, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d83, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare977 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (0 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare976 p hg
    simpa only [d84, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d84, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare978 (p : Pattern) (guard : d1 p = 1) : d85 p ≤ (0 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d85, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare977 p hg
    simpa only [d85, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d85, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d85, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare979 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (0 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare970 p hg
    simpa only [d86, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare978 p hg
    simpa only [d86, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
