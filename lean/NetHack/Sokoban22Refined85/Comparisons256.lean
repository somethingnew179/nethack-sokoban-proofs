/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons255
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35840 (p : Pattern) (guard : d0 p = 1) : d211 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35841 (p : Pattern) (guard : d8123 p = 1) : d212 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d212, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35839 p hg
    simpa only [d8123, d212, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d212, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35840 p hg
    simpa only [d8123, d212, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35842 (p : Pattern) (guard : d0 p = 1) : d213 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35843 (p : Pattern) (guard : d8129 p = 1) : d214 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d214, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35841 p hg
    simpa only [d8129, d214, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d214, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35842 p hg
    simpa only [d8129, d214, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35844 (p : Pattern) (guard : d8135 p = 1) : d289 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d289, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35843 p hg
    simpa only [d8135, d289, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d289, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2889 p hg
    simpa only [d8135, d289, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35845 (p : Pattern) (guard : d8136 p = 1) : d290 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d290, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35832 p hg
    simpa only [d8136, d290, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d290, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35844 p hg
    simpa only [d8136, d290, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35846 (p : Pattern) (guard : d8117 p = 1) : d291 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d291, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35783 p hg
    simpa only [d8117, d291, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d291, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3860 p hg
    simpa only [d8117, d291, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35847 (p : Pattern) (guard : d8123 p = 1) : d294 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d294, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35846 p hg
    simpa only [d8123, d294, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d294, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d8123, d294, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35848 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35849 (p : Pattern) (guard : d8129 p = 1) : d296 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d296, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35847 p hg
    simpa only [d8129, d296, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d296, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35848 p hg
    simpa only [d8129, d296, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35850 (p : Pattern) (guard : d8135 p = 1) : d297 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d297, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35849 p hg
    simpa only [d8135, d297, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d297, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4628 p hg
    simpa only [d8135, d297, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35851 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35852 (p : Pattern) (guard : d8141 p = 1) : d305 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d305, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35850 p hg
    simpa only [d8141, d305, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d305, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35851 p hg
    simpa only [d8141, d305, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35853 (p : Pattern) (guard : d8142 p = 1) : d306 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d306, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35845 p hg
    simpa only [d8142, d306, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d306, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35852 p hg
    simpa only [d8142, d306, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35854 (p : Pattern) (guard : d8111 p = 1) : d354 p ≤ (0 : Int) + d354 p := by
  omega
theorem compare35855 (p : Pattern) (guard : d8117 p = 1) : d450 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d450, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35854 p hg
    simpa only [d8117, d450, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d450, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d450, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35856 (p : Pattern) (guard : d8123 p = 1) : d451 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d451, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35855 p hg
    simpa only [d8123, d451, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d451, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d451, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35857 (p : Pattern) (guard : d8129 p = 1) : d455 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d455, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35856 p hg
    simpa only [d8129, d455, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d455, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d455, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35858 (p : Pattern) (guard : d8135 p = 1) : d456 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d456, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35857 p hg
    simpa only [d8135, d456, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d456, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d456, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35859 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35860 (p : Pattern) (guard : d8141 p = 1) : d475 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d475, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35858 p hg
    simpa only [d8141, d475, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d475, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35859 p hg
    simpa only [d8141, d475, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35861 (p : Pattern) (guard : d8147 p = 1) : d476 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d476, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35860 p hg
    simpa only [d8147, d476, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d476, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d476, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35862 (p : Pattern) (guard : d8148 p = 1) : d512 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d512, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35853 p hg
    simpa only [d8148, d512, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d512, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35861 p hg
    simpa only [d8148, d512, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35863 (p : Pattern) (guard : d8149 p = 1) : d513 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d513, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35814 p hg
    simpa only [d8149, d513, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d513, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35862 p hg
    simpa only [d8149, d513, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35864 (p : Pattern) (guard : d8150 p = 1) : d514 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d514, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35695 p hg
    simpa only [d8150, d514, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d514, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35863 p hg
    simpa only [d8150, d514, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35865 (p : Pattern) (guard : d8151 p = 1) : d515 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35562 p hg
    simpa only [d8151, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35864 p hg
    simpa only [d8151, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35866 (p : Pattern) (guard : d8152 p = 1) : d516 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35381 p hg
    simpa only [d8152, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35865 p hg
    simpa only [d8152, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35867 (p : Pattern) (guard : d1 p = 1) : d313 p ≤ (0 : Int) + d313 p := by
  omega
theorem compare35868 (p : Pattern) (guard : d1 p = 1) : d3540 p ≤ (0 : Int) + d314 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3540, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35867 p hg
    simpa only [d3540, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3540, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4500 p hg
    simpa only [d3540, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35869 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4500 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35870 (p : Pattern) (guard : d1 p = 1) : d3541 p ≤ (0 : Int) + d316 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3541, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35868 p hg
    simpa only [d3541, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3541, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35869 p hg
    simpa only [d3541, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35871 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare906 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35872 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35871 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35873 (p : Pattern) (guard : d1 p = 1) : d3542 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3542, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35870 p hg
    simpa only [d3542, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3542, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35872 p hg
    simpa only [d3542, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35874 (p : Pattern) (guard : d1 p = 1) : d3543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35875 (p : Pattern) (guard : d1 p = 1) : d3544 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3544, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35869 p hg
    simpa only [d3544, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3544, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d3544, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35876 (p : Pattern) (guard : d1 p = 1) : d3545 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35875 p hg
    simpa only [d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35877 (p : Pattern) (guard : d1 p = 1) : d3546 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35873 p hg
    simpa only [d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35876 p hg
    simpa only [d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35878 (p : Pattern) (guard : d1 p = 1) : d3547 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35879 (p : Pattern) (guard : d1 p = 1) : d3548 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3548, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35871 p hg
    simpa only [d3548, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3548, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35878 p hg
    simpa only [d3548, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35880 (p : Pattern) (guard : d1 p = 1) : d3549 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35879 p hg
    simpa only [d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35878 p hg
    simpa only [d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35881 (p : Pattern) (guard : d8087 p = 1) : d3550 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35880 p hg
    simpa only [d8087, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d8087, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35882 (p : Pattern) (guard : d8088 p = 1) : d3551 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8088, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35877 p hg
    simpa only [d8088, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8087 p = 1 := by simpa only [d8088, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35881 p hg
    simpa only [d8088, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35883 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare890 p hg
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1493 p hg
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35884 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1493 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35885 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35883 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35884 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35886 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34460 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35887 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35886 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35888 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35885 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35887 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35889 (p : Pattern) (guard : d1 p = 1) : d3544 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35884 p hg
    simpa only [d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35890 (p : Pattern) (guard : d8084 p = 1) : d3543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d8084, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35891 (p : Pattern) (guard : d8085 p = 1) : d3543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35892 (p : Pattern) (guard : d8086 p = 1) : d3545 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35889 p hg
    simpa only [d8086, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35891 p hg
    simpa only [d8086, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35893 (p : Pattern) (guard : d8087 p = 1) : d3552 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35888 p hg
    simpa only [d8087, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35892 p hg
    simpa only [d8087, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35894 (p : Pattern) (guard : d1 p = 1) : d3548 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35886 p hg
    simpa only [d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35878 p hg
    simpa only [d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35895 (p : Pattern) (guard : d8084 p = 1) : d3547 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d8084, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35896 (p : Pattern) (guard : d8085 p = 1) : d3547 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35878 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35895 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35897 (p : Pattern) (guard : d8086 p = 1) : d3549 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35894 p hg
    simpa only [d8086, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35896 p hg
    simpa only [d8086, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35898 (p : Pattern) (guard : d8091 p = 1) : d3550 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35897 p hg
    simpa only [d8091, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35899 (p : Pattern) (guard : d8092 p = 1) : d3553 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35893 p hg
    simpa only [d8092, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35898 p hg
    simpa only [d8092, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35900 (p : Pattern) (guard : d8093 p = 1) : d3554 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35882 p hg
    simpa only [d8093, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35899 p hg
    simpa only [d8093, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35901 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1193 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35902 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35901 p hg
    simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35903 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35884 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35904 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35902 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35903 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35905 (p : Pattern) (guard : d1 p = 1) : d3544 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35906 (p : Pattern) (guard : d8086 p = 1) : d3545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35905 p hg
    simpa only [d8086, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35891 p hg
    simpa only [d8086, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35907 (p : Pattern) (guard : d8087 p = 1) : d3552 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35904 p hg
    simpa only [d8087, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35906 p hg
    simpa only [d8087, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35908 (p : Pattern) (guard : d1 p = 1) : d3548 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35884 p hg
    simpa only [d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35878 p hg
    simpa only [d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35909 (p : Pattern) (guard : d8086 p = 1) : d3549 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35908 p hg
    simpa only [d8086, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35896 p hg
    simpa only [d8086, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35910 (p : Pattern) (guard : d8091 p = 1) : d3550 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35909 p hg
    simpa only [d8091, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35911 (p : Pattern) (guard : d8092 p = 1) : d3553 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35907 p hg
    simpa only [d8092, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35910 p hg
    simpa only [d8092, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35912 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare921 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35913 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35912 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35914 (p : Pattern) (guard : d8084 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35915 (p : Pattern) (guard : d8085 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35916 (p : Pattern) (guard : d8086 p = 1) : d17 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35913 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35915 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35917 (p : Pattern) (guard : d5843 p = 1) : d190 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35918 (p : Pattern) (guard : d8084 p = 1) : d3555 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d8084, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35917 p hg
    simpa only [d8084, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35919 (p : Pattern) (guard : d8085 p = 1) : d3556 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d8085, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35918 p hg
    simpa only [d8085, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35920 (p : Pattern) (guard : d5847 p = 1) : d3555 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d5847, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35921 (p : Pattern) (guard : d8089 p = 1) : d3555 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35918 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35920 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35922 (p : Pattern) (guard : d8090 p = 1) : d3557 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35919 p hg
    simpa only [d8090, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35921 p hg
    simpa only [d8090, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35923 (p : Pattern) (guard : d8091 p = 1) : d3558 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35916 p hg
    simpa only [d8091, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35922 p hg
    simpa only [d8091, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35924 (p : Pattern) (guard : d8084 p = 1) : d3559 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d8084, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d8084, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35925 (p : Pattern) (guard : d8085 p = 1) : d3560 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d8085, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35924 p hg
    simpa only [d8085, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35926 (p : Pattern) (guard : d5847 p = 1) : d3559 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d5847, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35927 (p : Pattern) (guard : d8089 p = 1) : d3559 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35924 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35926 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35928 (p : Pattern) (guard : d8090 p = 1) : d3561 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35925 p hg
    simpa only [d8090, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35927 p hg
    simpa only [d8090, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35929 (p : Pattern) (guard : d8095 p = 1) : d3562 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35928 p hg
    simpa only [d8095, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35930 (p : Pattern) (guard : d8096 p = 1) : d3563 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35923 p hg
    simpa only [d8096, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35929 p hg
    simpa only [d8096, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35931 (p : Pattern) (guard : d8097 p = 1) : d3564 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35911 p hg
    simpa only [d8097, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35930 p hg
    simpa only [d8097, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35932 (p : Pattern) (guard : d8098 p = 1) : d3565 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35900 p hg
    simpa only [d8098, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35931 p hg
    simpa only [d8098, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35933 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare896 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35934 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35933 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35935 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35934 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35936 (p : Pattern) (guard : d8087 p = 1) : d3552 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35935 p hg
    simpa only [d8087, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35906 p hg
    simpa only [d8087, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35937 (p : Pattern) (guard : d1 p = 1) : d3548 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35878 p hg
    simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35938 (p : Pattern) (guard : d8086 p = 1) : d3549 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35937 p hg
    simpa only [d8086, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35896 p hg
    simpa only [d8086, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35939 (p : Pattern) (guard : d8091 p = 1) : d3550 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35938 p hg
    simpa only [d8091, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35940 (p : Pattern) (guard : d8092 p = 1) : d3553 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35936 p hg
    simpa only [d8092, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35939 p hg
    simpa only [d8092, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35941 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34378 p hg
    simpa only [d17, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d17, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35942 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35941 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35943 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35942 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35944 (p : Pattern) (guard : d8086 p = 1) : d17 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35943 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35915 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35945 (p : Pattern) (guard : d8091 p = 1) : d3558 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35944 p hg
    simpa only [d8091, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35922 p hg
    simpa only [d8091, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35946 (p : Pattern) (guard : d8096 p = 1) : d3563 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35945 p hg
    simpa only [d8096, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35929 p hg
    simpa only [d8096, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35947 (p : Pattern) (guard : d8097 p = 1) : d3564 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35940 p hg
    simpa only [d8097, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35946 p hg
    simpa only [d8097, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35948 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (0 : Int) + d23 p := by
  omega
theorem compare35949 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35948 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35950 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35949 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35951 (p : Pattern) (guard : d8084 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35952 (p : Pattern) (guard : d8085 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35951 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35953 (p : Pattern) (guard : d8086 p = 1) : d23 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35950 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35952 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35954 (p : Pattern) (guard : d8084 p = 1) : d356 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35955 (p : Pattern) (guard : d8085 p = 1) : d3566 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d8085, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35954 p hg
    simpa only [d8085, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35956 (p : Pattern) (guard : d5847 p = 1) : d356 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35957 (p : Pattern) (guard : d8089 p = 1) : d356 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35954 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35956 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35958 (p : Pattern) (guard : d8090 p = 1) : d3567 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35955 p hg
    simpa only [d8090, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35957 p hg
    simpa only [d8090, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35959 (p : Pattern) (guard : d8091 p = 1) : d3568 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35953 p hg
    simpa only [d8091, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35958 p hg
    simpa only [d8091, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35960 (p : Pattern) (guard : d8084 p = 1) : d3569 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d8084, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d8084, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35961 (p : Pattern) (guard : d8085 p = 1) : d3570 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d8085, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35960 p hg
    simpa only [d8085, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35962 (p : Pattern) (guard : d5847 p = 1) : d3569 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d5847, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35963 (p : Pattern) (guard : d8089 p = 1) : d3569 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35960 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35962 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35964 (p : Pattern) (guard : d8090 p = 1) : d3571 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35961 p hg
    simpa only [d8090, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35963 p hg
    simpa only [d8090, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35965 (p : Pattern) (guard : d8095 p = 1) : d3572 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35964 p hg
    simpa only [d8095, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35966 (p : Pattern) (guard : d8096 p = 1) : d3573 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35959 p hg
    simpa only [d8096, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35965 p hg
    simpa only [d8096, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35967 (p : Pattern) (guard : d8102 p = 1) : d3574 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35966 p hg
    simpa only [d8102, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35968 (p : Pattern) (guard : d8103 p = 1) : d3575 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35947 p hg
    simpa only [d8103, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35967 p hg
    simpa only [d8103, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35969 (p : Pattern) (guard : d8104 p = 1) : d3576 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35932 p hg
    simpa only [d8104, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35968 p hg
    simpa only [d8104, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35970 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1488 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35971 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35970 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35972 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35971 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35973 (p : Pattern) (guard : d1 p = 1) : d3577 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35974 (p : Pattern) (guard : d1 p = 1) : d3578 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35973 p hg
    simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35975 (p : Pattern) (guard : d8084 p = 1) : d3579 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d8084, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d8084, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35976 (p : Pattern) (guard : d8085 p = 1) : d3580 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d8085, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35975 p hg
    simpa only [d8085, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35977 (p : Pattern) (guard : d8086 p = 1) : d3581 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35974 p hg
    simpa only [d8086, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35976 p hg
    simpa only [d8086, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35978 (p : Pattern) (guard : d8087 p = 1) : d3582 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35972 p hg
    simpa only [d8087, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35977 p hg
    simpa only [d8087, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35979 (p : Pattern) (guard : d1 p = 1) : d3583 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1639 p hg
    simpa only [d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
