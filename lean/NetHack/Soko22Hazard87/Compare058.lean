import NetHack.Soko22Hazard87.Compare057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14500 (p : Pattern) (guard : d128260 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128259 p = 1 := by simpa only [d128260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14499 p hg
    simpa only [d128260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14501 (p : Pattern) (guard : d128261 p = 1) : d48387 p ≤ (1 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128260 p = 1 := by simpa only [d128261, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14500 p hg
    simpa only [d128261, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128261, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13796 p hg
    simpa only [d128261, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14502 (p : Pattern) (guard : d128262 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128251 p = 1 := by simpa only [d128262, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14435 p hg
    simpa only [d128262, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128261 p = 1 := by simpa only [d128262, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14501 p hg
    simpa only [d128262, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14503 (p : Pattern) (guard : d128263 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128262 p = 1 := by simpa only [d128263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14502 p hg
    simpa only [d128263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14504 (p : Pattern) (guard : d128264 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128263 p = 1 := by simpa only [d128264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14503 p hg
    simpa only [d128264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14505 (p : Pattern) (guard : d128265 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128264 p = 1 := by simpa only [d128265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14504 p hg
    simpa only [d128265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14506 (p : Pattern) (guard : d128266 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128265 p = 1 := by simpa only [d128266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14505 p hg
    simpa only [d128266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14507 (p : Pattern) (guard : d128267 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128266 p = 1 := by simpa only [d128267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14506 p hg
    simpa only [d128267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14508 (p : Pattern) (guard : d128268 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128267 p = 1 := by simpa only [d128268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14507 p hg
    simpa only [d128268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14509 (p : Pattern) (guard : d128269 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d128229 p = 1 := by simpa only [d128269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14175 p hg
    simpa only [d128269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128268 p = 1 := by simpa only [d128269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14508 p hg
    simpa only [d128269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14510 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14511 (p : Pattern) (guard : d754 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14510 p hg
    simpa only [d754, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d754, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14512 (p : Pattern) (guard : d12750 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14257 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14511 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14513 (p : Pattern) (guard : d16227 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14255 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14512 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14514 (p : Pattern) (guard : d755 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13997 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14511 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14515 (p : Pattern) (guard : d757 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14511 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14516 (p : Pattern) (guard : d758 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14514 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14515 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14517 (p : Pattern) (guard : d16228 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14513 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14516 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14518 (p : Pattern) (guard : d16229 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16229, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14517 p hg
    simpa only [d16229, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14519 (p : Pattern) (guard : d16230 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16230, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14518 p hg
    simpa only [d16230, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14520 (p : Pattern) (guard : d762 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14515 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14521 (p : Pattern) (guard : d763 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14516 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14520 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14522 (p : Pattern) (guard : d764 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d764, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14521 p hg
    simpa only [d764, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14523 (p : Pattern) (guard : d765 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d765, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14522 p hg
    simpa only [d765, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14524 (p : Pattern) (guard : d16231 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14519 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14523 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14525 (p : Pattern) (guard : d767 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14523 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14526 (p : Pattern) (guard : d16232 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14524 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14525 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14527 (p : Pattern) (guard : d16233 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14526 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14528 (p : Pattern) (guard : d16234 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14527 p hg
    simpa only [d16234, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16234, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14529 (p : Pattern) (guard : d16235 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16235, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14528 p hg
    simpa only [d16235, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14530 (p : Pattern) (guard : d772 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14525 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14531 (p : Pattern) (guard : d773 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14530 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14532 (p : Pattern) (guard : d774 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14531 p hg
    simpa only [d774, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d774, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14533 (p : Pattern) (guard : d775 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d775, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14532 p hg
    simpa only [d775, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14534 (p : Pattern) (guard : d16236 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14529 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14535 (p : Pattern) (guard : d16237 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14534 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14536 (p : Pattern) (guard : d16238 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14535 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14537 (p : Pattern) (guard : d16239 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16238 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14536 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14538 (p : Pattern) (guard : d780 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14539 (p : Pattern) (guard : d781 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14538 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14540 (p : Pattern) (guard : d782 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14539 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14541 (p : Pattern) (guard : d783 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14540 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14542 (p : Pattern) (guard : d16240 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16239 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14541 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14543 (p : Pattern) (guard : d16241 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16240 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14542 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14544 (p : Pattern) (guard : d16242 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16241 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14543 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14545 (p : Pattern) (guard : d16243 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16242 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14544 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14546 (p : Pattern) (guard : d16244 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16243 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14545 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14547 (p : Pattern) (guard : d16245 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16244 p = 1 := by simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14546 p hg
    simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14548 (p : Pattern) (guard : d16246 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16245 p = 1 := by simpa only [d16246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d16246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14549 (p : Pattern) (guard : d16247 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16246 p = 1 := by simpa only [d16247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14548 p hg
    simpa only [d16247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14550 (p : Pattern) (guard : d16230 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16230, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14518 p hg
    simpa only [d16230, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14551 (p : Pattern) (guard : d765 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d765, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14522 p hg
    simpa only [d765, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14552 (p : Pattern) (guard : d16231 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14550 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14551 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14553 (p : Pattern) (guard : d767 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14551 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14554 (p : Pattern) (guard : d16232 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14552 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14553 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14555 (p : Pattern) (guard : d16233 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14554 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14556 (p : Pattern) (guard : d16234 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14555 p hg
    simpa only [d16234, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16234, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14557 (p : Pattern) (guard : d16235 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16235, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14556 p hg
    simpa only [d16235, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14558 (p : Pattern) (guard : d772 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14553 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14559 (p : Pattern) (guard : d773 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14560 (p : Pattern) (guard : d774 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14559 p hg
    simpa only [d774, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d774, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14561 (p : Pattern) (guard : d775 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d775, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14560 p hg
    simpa only [d775, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14562 (p : Pattern) (guard : d16236 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14557 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14561 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14563 (p : Pattern) (guard : d16237 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14562 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14564 (p : Pattern) (guard : d16238 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14563 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14565 (p : Pattern) (guard : d16239 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16238 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14564 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14566 (p : Pattern) (guard : d780 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14561 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14567 (p : Pattern) (guard : d781 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14568 (p : Pattern) (guard : d782 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14567 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14569 (p : Pattern) (guard : d783 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14568 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14570 (p : Pattern) (guard : d16240 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16239 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14565 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14569 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14571 (p : Pattern) (guard : d16241 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16240 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14570 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14572 (p : Pattern) (guard : d16242 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16241 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14571 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14573 (p : Pattern) (guard : d16243 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16242 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14572 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14574 (p : Pattern) (guard : d16244 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16243 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14573 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14575 (p : Pattern) (guard : d16248 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16238 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14536 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14576 (p : Pattern) (guard : d793 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14540 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14577 (p : Pattern) (guard : d16249 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16248 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14575 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14576 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14578 (p : Pattern) (guard : d16250 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16249 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14577 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14579 (p : Pattern) (guard : d16251 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16250 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14578 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14580 (p : Pattern) (guard : d16252 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16251 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14579 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14581 (p : Pattern) (guard : d16253 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16252 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14580 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14582 (p : Pattern) (guard : d16254 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16244 p = 1 := by simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14574 p hg
    simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16253 p = 1 := by simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14581 p hg
    simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14583 (p : Pattern) (guard : d16255 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16245 p = 1 := by simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16254 p = 1 := by simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14582 p hg
    simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14584 (p : Pattern) (guard : d16256 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16255 p = 1 := by simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14583 p hg
    simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14585 (p : Pattern) (guard : d16257 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16247 p = 1 := by simpa only [d16257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14549 p hg
    simpa only [d16257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16256 p = 1 := by simpa only [d16257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14584 p hg
    simpa only [d16257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14586 (p : Pattern) (guard : d16258 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16237 p = 1 := by simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14535 p hg
    simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14587 (p : Pattern) (guard : d16259 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16258 p = 1 := by simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14586 p hg
    simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14588 (p : Pattern) (guard : d805 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d781 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14539 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14589 (p : Pattern) (guard : d806 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d805 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14588 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14590 (p : Pattern) (guard : d16260 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16259 p = 1 := by simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14587 p hg
    simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d806 p = 1 := by simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14589 p hg
    simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14591 (p : Pattern) (guard : d16261 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16260 p = 1 := by simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14590 p hg
    simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14592 (p : Pattern) (guard : d16262 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16261 p = 1 := by simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14591 p hg
    simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14593 (p : Pattern) (guard : d16263 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16262 p = 1 := by simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14592 p hg
    simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14594 (p : Pattern) (guard : d16264 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16236 p = 1 := by simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14534 p hg
    simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14595 (p : Pattern) (guard : d16265 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16264 p = 1 := by simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14594 p hg
    simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14596 (p : Pattern) (guard : d16266 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16265 p = 1 := by simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14595 p hg
    simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14597 (p : Pattern) (guard : d814 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d780 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14538 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14598 (p : Pattern) (guard : d815 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d814 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14597 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14599 (p : Pattern) (guard : d816 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d815 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14598 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14600 (p : Pattern) (guard : d16267 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16266 p = 1 := by simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14596 p hg
    simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d816 p = 1 := by simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14599 p hg
    simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14601 (p : Pattern) (guard : d16268 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16267 p = 1 := by simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14600 p hg
    simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14602 (p : Pattern) (guard : d16269 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16268 p = 1 := by simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14601 p hg
    simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14603 (p : Pattern) (guard : d836 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14604 (p : Pattern) (guard : d837 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d837, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14603 p hg
    simpa only [d837, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d837, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d837, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14605 (p : Pattern) (guard : d16270 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14606 (p : Pattern) (guard : d16271 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16270 p = 1 := by simpa only [d16271, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14605 p hg
    simpa only [d16271, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16271, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d16271, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14607 (p : Pattern) (guard : d16272 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d837 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14604 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16271 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14606 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14608 (p : Pattern) (guard : d14529 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14609 (p : Pattern) (guard : d14530 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14529 p = 1 := by simpa only [d14530, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14608 p hg
    simpa only [d14530, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14530, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d14530, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14610 (p : Pattern) (guard : d16273 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14530 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14609 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12749 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14257 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14611 (p : Pattern) (guard : d16274 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16272 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14607 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16273 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14610 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14612 (p : Pattern) (guard : d16275 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16274 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14611 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16227 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14513 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14613 (p : Pattern) (guard : d16276 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16276, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16276, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16275 p = 1 := by simpa only [d16276, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14612 p hg
    simpa only [d16276, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14614 (p : Pattern) (guard : d16277 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16277, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16277, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16276 p = 1 := by simpa only [d16277, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14613 p hg
    simpa only [d16277, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14615 (p : Pattern) (guard : d16278 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12750 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14512 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14515 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14616 (p : Pattern) (guard : d16279 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14513 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16278 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14615 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14617 (p : Pattern) (guard : d16280 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16280, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16280, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16279 p = 1 := by simpa only [d16280, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14616 p hg
    simpa only [d16280, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14618 (p : Pattern) (guard : d16281 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16281, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16281, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16280 p = 1 := by simpa only [d16281, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14617 p hg
    simpa only [d16281, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14619 (p : Pattern) (guard : d16282 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16277 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14614 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16281 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14618 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14620 (p : Pattern) (guard : d16283 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16282 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14619 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16231 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14524 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14621 (p : Pattern) (guard : d16284 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16283 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14620 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14622 (p : Pattern) (guard : d16285 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16284 p = 1 := by simpa only [d16285, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14621 p hg
    simpa only [d16285, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16285, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16285, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14623 (p : Pattern) (guard : d16286 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16286, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16286, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16285 p = 1 := by simpa only [d16286, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14622 p hg
    simpa only [d16286, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14624 (p : Pattern) (guard : d16287 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16286 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14623 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16235 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14529 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14625 (p : Pattern) (guard : d16288 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16287 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14624 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14626 (p : Pattern) (guard : d16289 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16288 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14625 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14627 (p : Pattern) (guard : d16290 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16289 p = 1 := by simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14626 p hg
    simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14628 (p : Pattern) (guard : d16291 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16290 p = 1 := by simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14627 p hg
    simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16239 p = 1 := by simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14629 (p : Pattern) (guard : d128270 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16291 p = 1 := by simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14628 p hg
    simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14630 (p : Pattern) (guard : d16311 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14529 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14631 (p : Pattern) (guard : d16312 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16311 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14630 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14632 (p : Pattern) (guard : d16313 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16312 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14631 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14633 (p : Pattern) (guard : d16314 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16313 p = 1 := by simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14632 p hg
    simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14634 (p : Pattern) (guard : d16315 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16314 p = 1 := by simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14633 p hg
    simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14635 (p : Pattern) (guard : d16316 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16315 p = 1 := by simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14634 p hg
    simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14636 (p : Pattern) (guard : d128271 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128270 p = 1 := by simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14629 p hg
    simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16316 p = 1 := by simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14635 p hg
    simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14637 (p : Pattern) (guard : d128272 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16269 p = 1 := by simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14602 p hg
    simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128271 p = 1 := by simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14636 p hg
    simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14638 (p : Pattern) (guard : d128273 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16263 p = 1 := by simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14593 p hg
    simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128272 p = 1 := by simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14637 p hg
    simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14639 (p : Pattern) (guard : d128274 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128274, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128274, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128273 p = 1 := by simpa only [d128274, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14638 p hg
    simpa only [d128274, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14640 (p : Pattern) (guard : d16258 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16237 p = 1 := by simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14563 p hg
    simpa only [d16258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14641 (p : Pattern) (guard : d16259 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16258 p = 1 := by simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14640 p hg
    simpa only [d16259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14642 (p : Pattern) (guard : d805 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d781 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14567 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14643 (p : Pattern) (guard : d806 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d805 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14642 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14644 (p : Pattern) (guard : d16260 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16259 p = 1 := by simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14641 p hg
    simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d806 p = 1 := by simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14643 p hg
    simpa only [d16260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14645 (p : Pattern) (guard : d16261 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16260 p = 1 := by simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14644 p hg
    simpa only [d16261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14646 (p : Pattern) (guard : d16262 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16261 p = 1 := by simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14645 p hg
    simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14647 (p : Pattern) (guard : d16263 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16262 p = 1 := by simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d16263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14648 (p : Pattern) (guard : d16264 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16236 p = 1 := by simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14562 p hg
    simpa only [d16264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14649 (p : Pattern) (guard : d16265 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16264 p = 1 := by simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14648 p hg
    simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14650 (p : Pattern) (guard : d16266 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16265 p = 1 := by simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14649 p hg
    simpa only [d16266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14651 (p : Pattern) (guard : d814 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d780 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14652 (p : Pattern) (guard : d815 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d814 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14651 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14653 (p : Pattern) (guard : d816 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d815 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14652 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14654 (p : Pattern) (guard : d16267 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16266 p = 1 := by simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14650 p hg
    simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d816 p = 1 := by simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14653 p hg
    simpa only [d16267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14655 (p : Pattern) (guard : d16268 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16267 p = 1 := by simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d16268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14656 (p : Pattern) (guard : d16269 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16268 p = 1 := by simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14655 p hg
    simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14657 (p : Pattern) (guard : d16277 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16277, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16277, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16276 p = 1 := by simpa only [d16277, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14613 p hg
    simpa only [d16277, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14658 (p : Pattern) (guard : d16281 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16281, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16281, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16280 p = 1 := by simpa only [d16281, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14617 p hg
    simpa only [d16281, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14659 (p : Pattern) (guard : d16282 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16277 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14657 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16281 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14658 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14660 (p : Pattern) (guard : d16283 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16282 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14659 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16231 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14552 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14661 (p : Pattern) (guard : d16284 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16283 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14660 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14662 (p : Pattern) (guard : d16285 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16284 p = 1 := by simpa only [d16285, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14661 p hg
    simpa only [d16285, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16285, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16285, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14663 (p : Pattern) (guard : d16286 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16286, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16286, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16285 p = 1 := by simpa only [d16286, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14662 p hg
    simpa only [d16286, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14664 (p : Pattern) (guard : d16287 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16286 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14663 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16235 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14557 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14665 (p : Pattern) (guard : d16288 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16287 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14664 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14666 (p : Pattern) (guard : d16289 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16288 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14665 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14667 (p : Pattern) (guard : d16290 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16289 p = 1 := by simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14666 p hg
    simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14668 (p : Pattern) (guard : d16291 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16290 p = 1 := by simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16239 p = 1 := by simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14565 p hg
    simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14669 (p : Pattern) (guard : d128270 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16291 p = 1 := by simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14668 p hg
    simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14670 (p : Pattern) (guard : d16311 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14557 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14671 (p : Pattern) (guard : d16312 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16311 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14670 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14672 (p : Pattern) (guard : d16313 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16312 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14671 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14673 (p : Pattern) (guard : d16314 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16313 p = 1 := by simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14672 p hg
    simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14674 (p : Pattern) (guard : d16315 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16314 p = 1 := by simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14673 p hg
    simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14675 (p : Pattern) (guard : d16316 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16315 p = 1 := by simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14674 p hg
    simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14676 (p : Pattern) (guard : d128271 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128270 p = 1 := by simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14669 p hg
    simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16316 p = 1 := by simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14677 (p : Pattern) (guard : d128272 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16269 p = 1 := by simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14656 p hg
    simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128271 p = 1 := by simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14676 p hg
    simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14678 (p : Pattern) (guard : d128273 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16263 p = 1 := by simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14647 p hg
    simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128272 p = 1 := by simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14677 p hg
    simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14679 (p : Pattern) (guard : d16321 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16258 p = 1 := by simpa only [d16321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14586 p hg
    simpa only [d16321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14680 (p : Pattern) (guard : d916 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d805 p = 1 := by simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14588 p hg
    simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14681 (p : Pattern) (guard : d16322 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16321 p = 1 := by simpa only [d16322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14679 p hg
    simpa only [d16322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d16322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14680 p hg
    simpa only [d16322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14682 (p : Pattern) (guard : d16323 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16322 p = 1 := by simpa only [d16323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14681 p hg
    simpa only [d16323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14683 (p : Pattern) (guard : d16324 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16323 p = 1 := by simpa only [d16324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14682 p hg
    simpa only [d16324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14684 (p : Pattern) (guard : d16325 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16324 p = 1 := by simpa only [d16325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14683 p hg
    simpa only [d16325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14685 (p : Pattern) (guard : d16326 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16265 p = 1 := by simpa only [d16326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14595 p hg
    simpa only [d16326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14686 (p : Pattern) (guard : d922 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d815 p = 1 := by simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14598 p hg
    simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14687 (p : Pattern) (guard : d16327 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16326 p = 1 := by simpa only [d16327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14685 p hg
    simpa only [d16327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d922 p = 1 := by simpa only [d16327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14686 p hg
    simpa only [d16327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14688 (p : Pattern) (guard : d16328 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16327 p = 1 := by simpa only [d16328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14687 p hg
    simpa only [d16328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14689 (p : Pattern) (guard : d16329 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16328 p = 1 := by simpa only [d16329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14688 p hg
    simpa only [d16329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14690 (p : Pattern) (guard : d16330 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16289 p = 1 := by simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14626 p hg
    simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14691 (p : Pattern) (guard : d16331 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16330 p = 1 := by simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14690 p hg
    simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16248 p = 1 := by simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14575 p hg
    simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14692 (p : Pattern) (guard : d128275 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16331 p = 1 := by simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14691 p hg
    simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14693 (p : Pattern) (guard : d16335 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16313 p = 1 := by simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14632 p hg
    simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14694 (p : Pattern) (guard : d16336 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16335 p = 1 := by simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14693 p hg
    simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14695 (p : Pattern) (guard : d16337 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16336 p = 1 := by simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14694 p hg
    simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14696 (p : Pattern) (guard : d128276 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128275 p = 1 := by simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14692 p hg
    simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16337 p = 1 := by simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14695 p hg
    simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14697 (p : Pattern) (guard : d128277 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16329 p = 1 := by simpa only [d128277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14689 p hg
    simpa only [d128277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128276 p = 1 := by simpa only [d128277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14696 p hg
    simpa only [d128277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14698 (p : Pattern) (guard : d128278 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16325 p = 1 := by simpa only [d128278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14684 p hg
    simpa only [d128278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128277 p = 1 := by simpa only [d128278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14697 p hg
    simpa only [d128278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14699 (p : Pattern) (guard : d128279 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128273 p = 1 := by simpa only [d128279, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14678 p hg
    simpa only [d128279, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128278 p = 1 := by simpa only [d128279, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14698 p hg
    simpa only [d128279, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14700 (p : Pattern) (guard : d128280 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128274 p = 1 := by simpa only [d128280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14639 p hg
    simpa only [d128280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128279 p = 1 := by simpa only [d128280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14699 p hg
    simpa only [d128280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14701 (p : Pattern) (guard : d939 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d783 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14541 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14702 (p : Pattern) (guard : d940 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d939 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14701 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14703 (p : Pattern) (guard : d941 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d940 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14702 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14704 (p : Pattern) (guard : d942 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d941 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14703 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14705 (p : Pattern) (guard : d943 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d942 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14704 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14706 (p : Pattern) (guard : d16343 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16244 p = 1 := by simpa only [d16343, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14574 p hg
    simpa only [d16343, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d943 p = 1 := by simpa only [d16343, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14705 p hg
    simpa only [d16343, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14707 (p : Pattern) (guard : d939 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d783 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14569 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14708 (p : Pattern) (guard : d940 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d939 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14707 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14709 (p : Pattern) (guard : d941 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d940 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14708 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14710 (p : Pattern) (guard : d942 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d941 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14709 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14711 (p : Pattern) (guard : d943 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d942 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14710 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14712 (p : Pattern) (guard : d945 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14576 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14713 (p : Pattern) (guard : d946 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d945 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14712 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14714 (p : Pattern) (guard : d947 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d946 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14713 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14715 (p : Pattern) (guard : d948 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d947 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14714 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14716 (p : Pattern) (guard : d949 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d948 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14715 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14717 (p : Pattern) (guard : d950 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d943 p = 1 := by simpa only [d950, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14711 p hg
    simpa only [d950, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d949 p = 1 := by simpa only [d950, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14716 p hg
    simpa only [d950, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14718 (p : Pattern) (guard : d16344 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16343 p = 1 := by simpa only [d16344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14706 p hg
    simpa only [d16344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d950 p = 1 := by simpa only [d16344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14717 p hg
    simpa only [d16344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14719 (p : Pattern) (guard : d128281 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128280 p = 1 := by simpa only [d128281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14700 p hg
    simpa only [d128281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16344 p = 1 := by simpa only [d128281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14718 p hg
    simpa only [d128281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14720 (p : Pattern) (guard : d128282 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128281 p = 1 := by simpa only [d128282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14719 p hg
    simpa only [d128282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d128282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14721 (p : Pattern) (guard : d128283 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d16257 p = 1 := by simpa only [d128283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14585 p hg
    simpa only [d128283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128282 p = 1 := by simpa only [d128283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14720 p hg
    simpa only [d128283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14722 (p : Pattern) (guard : d836 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare14723 (p : Pattern) (guard : d837 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d837, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14722 p hg
    simpa only [d837, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d837, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d837, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14724 (p : Pattern) (guard : d16270 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare14725 (p : Pattern) (guard : d16271 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16270 p = 1 := by simpa only [d16271, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14724 p hg
    simpa only [d16271, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16271, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d16271, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14726 (p : Pattern) (guard : d16272 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d837 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14723 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16271 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14725 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14727 (p : Pattern) (guard : d14529 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare14728 (p : Pattern) (guard : d14530 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14529 p = 1 := by simpa only [d14530, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14727 p hg
    simpa only [d14530, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14530, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d14530, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14729 (p : Pattern) (guard : d16273 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14530 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14728 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12749 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14376 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14730 (p : Pattern) (guard : d16274 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16272 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14726 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16273 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14729 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14731 (p : Pattern) (guard : d753 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare14732 (p : Pattern) (guard : d754 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14731 p hg
    simpa only [d754, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d754, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14733 (p : Pattern) (guard : d12750 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14376 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14732 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14734 (p : Pattern) (guard : d16227 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14374 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14733 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14735 (p : Pattern) (guard : d16275 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16274 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14730 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16227 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14734 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14736 (p : Pattern) (guard : d16276 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16276, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16276, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16275 p = 1 := by simpa only [d16276, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14735 p hg
    simpa only [d16276, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14737 (p : Pattern) (guard : d16277 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16277, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16277, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16276 p = 1 := by simpa only [d16277, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14736 p hg
    simpa only [d16277, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14738 (p : Pattern) (guard : d757 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14732 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14739 (p : Pattern) (guard : d16278 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12750 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14733 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14738 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14740 (p : Pattern) (guard : d16279 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14734 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16278 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14739 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14741 (p : Pattern) (guard : d16280 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16280, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16280, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16279 p = 1 := by simpa only [d16280, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14740 p hg
    simpa only [d16280, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14742 (p : Pattern) (guard : d16281 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16281, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16281, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16280 p = 1 := by simpa only [d16281, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14741 p hg
    simpa only [d16281, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14743 (p : Pattern) (guard : d16282 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16277 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14737 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16281 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14742 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14744 (p : Pattern) (guard : d755 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14086 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14732 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14745 (p : Pattern) (guard : d758 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14744 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14738 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14746 (p : Pattern) (guard : d16228 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14734 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14745 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14747 (p : Pattern) (guard : d16229 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16229, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14746 p hg
    simpa only [d16229, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14748 (p : Pattern) (guard : d16230 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16230, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14747 p hg
    simpa only [d16230, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14749 (p : Pattern) (guard : d762 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14738 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
