/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7700 (p : Pattern) (guard : d917 p = 1) : d700 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d700, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7697 p hg
    simpa only [d700, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d700, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7699 p hg
    simpa only [d700, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7701 (p : Pattern) (guard : d1248 p = 1) : d700 p ≤ (0 : Int) + d329 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7700 p hg
    simpa only [d1248, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7695 p hg
    simpa only [d1248, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7702 (p : Pattern) (guard : d1248 p = 1) : d700 p ≤ (0 : Int) + d330 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7701 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7703 (p : Pattern) (guard : d1248 p = 1) : d700 p ≤ (0 : Int) + d331 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7702 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7704 (p : Pattern) (guard : d0 p = 1) : d699 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7705 (p : Pattern) (guard : d1248 p = 1) : d699 p ≤ (0 : Int) + d332 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7693 p hg
    simpa only [d1248, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1248, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7706 (p : Pattern) (guard : d1248 p = 1) : d699 p ≤ (0 : Int) + d333 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7699 p hg
    simpa only [d1248, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1248, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7707 (p : Pattern) (guard : d1248 p = 1) : d699 p ≤ (0 : Int) + d334 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7705 p hg
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7706 p hg
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7708 (p : Pattern) (guard : d1248 p = 1) : d699 p ≤ (0 : Int) + d335 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7705 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7707 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7709 (p : Pattern) (guard : d917 p = 1) : d701 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7689 p hg
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7710 (p : Pattern) (guard : d917 p = 1) : d702 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7693 p hg
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7709 p hg
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7711 (p : Pattern) (guard : d0 p = 1) : d702 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7712 (p : Pattern) (guard : d1248 p = 1) : d702 p ≤ (0 : Int) + d336 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7710 p hg
    simpa only [d1248, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d1248, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7713 (p : Pattern) (guard : d917 p = 1) : d701 p ≤ (0 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d701, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7697 p hg
    simpa only [d701, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d701, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d701, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7714 (p : Pattern) (guard : d917 p = 1) : d702 p ≤ (0 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d702, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7699 p hg
    simpa only [d702, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d702, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7713 p hg
    simpa only [d702, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7715 (p : Pattern) (guard : d1248 p = 1) : d702 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7714 p hg
    simpa only [d1248, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d1248, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7716 (p : Pattern) (guard : d1248 p = 1) : d702 p ≤ (0 : Int) + d338 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7712 p hg
    simpa only [d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7715 p hg
    simpa only [d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7717 (p : Pattern) (guard : d1248 p = 1) : d702 p ≤ (0 : Int) + d339 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7712 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7716 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7718 (p : Pattern) (guard : d1248 p = 1) : d703 p ≤ (0 : Int) + d340 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d703, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7708 p hg
    simpa only [d703, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d703, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7717 p hg
    simpa only [d703, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7719 (p : Pattern) (guard : d1248 p = 1) : d704 p ≤ (0 : Int) + d341 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d704, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7703 p hg
    simpa only [d704, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d704, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7718 p hg
    simpa only [d704, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7720 (p : Pattern) (guard : d917 p = 1) : d705 p ≤ (0 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d705, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7698 p hg
    simpa only [d705, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d705, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d705, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7721 (p : Pattern) (guard : d917 p = 1) : d706 p ≤ (0 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d706, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7698 p hg
    simpa only [d706, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d706, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7720 p hg
    simpa only [d706, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7722 (p : Pattern) (guard : d0 p = 1) : d706 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7723 (p : Pattern) (guard : d1248 p = 1) : d706 p ≤ (0 : Int) + d342 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7721 p hg
    simpa only [d1248, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7722 p hg
    simpa only [d1248, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7724 (p : Pattern) (guard : d1248 p = 1) : d707 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d707, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d707, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d707, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7723 p hg
    simpa only [d707, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7725 (p : Pattern) (guard : d1248 p = 1) : d708 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d708, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d708, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d708, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7724 p hg
    simpa only [d708, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7726 (p : Pattern) (guard : d0 p = 1) : d705 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7727 (p : Pattern) (guard : d1248 p = 1) : d705 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7720 p hg
    simpa only [d1248, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1248, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7728 (p : Pattern) (guard : d1248 p = 1) : d709 p ≤ (0 : Int) + d346 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d709, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d709, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d709, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7727 p hg
    simpa only [d709, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7729 (p : Pattern) (guard : d1248 p = 1) : d710 p ≤ (0 : Int) + d347 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d710, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d710, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d710, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7728 p hg
    simpa only [d710, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7730 (p : Pattern) (guard : d1248 p = 1) : d711 p ≤ (0 : Int) + d348 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d711, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7725 p hg
    simpa only [d711, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d711, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7729 p hg
    simpa only [d711, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7731 (p : Pattern) (guard : d1248 p = 1) : d712 p ≤ (0 : Int) + d349 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d712, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7705 p hg
    simpa only [d712, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d712, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7727 p hg
    simpa only [d712, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7732 (p : Pattern) (guard : d1248 p = 1) : d713 p ≤ (0 : Int) + d350 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d713, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7705 p hg
    simpa only [d713, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d713, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7731 p hg
    simpa only [d713, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7733 (p : Pattern) (guard : d1248 p = 1) : d714 p ≤ (0 : Int) + d351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d714, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7712 p hg
    simpa only [d714, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d714, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7727 p hg
    simpa only [d714, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7734 (p : Pattern) (guard : d1248 p = 1) : d715 p ≤ (0 : Int) + d352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d715, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7712 p hg
    simpa only [d715, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d715, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7733 p hg
    simpa only [d715, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7735 (p : Pattern) (guard : d1248 p = 1) : d716 p ≤ (0 : Int) + d353 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d716, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7732 p hg
    simpa only [d716, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d716, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7734 p hg
    simpa only [d716, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7736 (p : Pattern) (guard : d1248 p = 1) : d717 p ≤ (0 : Int) + d354 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d717, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7730 p hg
    simpa only [d717, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d717, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7735 p hg
    simpa only [d717, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7737 (p : Pattern) (guard : d1248 p = 1) : d718 p ≤ (0 : Int) + d355 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d718, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7719 p hg
    simpa only [d718, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d718, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7736 p hg
    simpa only [d718, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7738 (p : Pattern) (guard : d917 p = 1) : d719 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7689 p hg
    simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7709 p hg
    simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7739 (p : Pattern) (guard : d0 p = 1) : d719 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7740 (p : Pattern) (guard : d1248 p = 1) : d719 p ≤ (0 : Int) + d356 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7738 p hg
    simpa only [d1248, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7739 p hg
    simpa only [d1248, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7741 (p : Pattern) (guard : d917 p = 1) : d719 p ≤ (0 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d719, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7697 p hg
    simpa only [d719, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d719, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7713 p hg
    simpa only [d719, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7742 (p : Pattern) (guard : d1248 p = 1) : d719 p ≤ (0 : Int) + d357 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7741 p hg
    simpa only [d1248, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7739 p hg
    simpa only [d1248, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7743 (p : Pattern) (guard : d1248 p = 1) : d719 p ≤ (0 : Int) + d358 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7740 p hg
    simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7742 p hg
    simpa only [d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7744 (p : Pattern) (guard : d1248 p = 1) : d719 p ≤ (0 : Int) + d359 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7740 p hg
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7743 p hg
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7745 (p : Pattern) (guard : d1248 p = 1) : d720 p ≤ (0 : Int) + d360 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d720, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7703 p hg
    simpa only [d720, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d720, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7744 p hg
    simpa only [d720, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7746 (p : Pattern) (guard : d917 p = 1) : d705 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7692 p hg
    simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7747 (p : Pattern) (guard : d917 p = 1) : d706 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7692 p hg
    simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7746 p hg
    simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7748 (p : Pattern) (guard : d1248 p = 1) : d706 p ≤ (0 : Int) + d361 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7747 p hg
    simpa only [d1248, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7722 p hg
    simpa only [d1248, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7749 (p : Pattern) (guard : d1248 p = 1) : d706 p ≤ (0 : Int) + d362 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7748 p hg
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7723 p hg
    simpa only [d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7750 (p : Pattern) (guard : d1248 p = 1) : d706 p ≤ (0 : Int) + d363 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7748 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7749 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7751 (p : Pattern) (guard : d1248 p = 1) : d721 p ≤ (0 : Int) + d364 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d721, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7745 p hg
    simpa only [d721, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d721, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7750 p hg
    simpa only [d721, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7752 (p : Pattern) (guard : d1248 p = 1) : d722 p ≤ (0 : Int) + d365 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d722, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7740 p hg
    simpa only [d722, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d722, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7727 p hg
    simpa only [d722, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7753 (p : Pattern) (guard : d1248 p = 1) : d723 p ≤ (0 : Int) + d366 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d723, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7740 p hg
    simpa only [d723, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d723, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7752 p hg
    simpa only [d723, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7754 (p : Pattern) (guard : d1248 p = 1) : d724 p ≤ (0 : Int) + d367 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d724, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7729 p hg
    simpa only [d724, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d724, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7753 p hg
    simpa only [d724, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7755 (p : Pattern) (guard : d1248 p = 1) : d725 p ≤ (0 : Int) + d368 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d725, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7748 p hg
    simpa only [d725, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d725, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3788 p hg
    simpa only [d725, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7756 (p : Pattern) (guard : d1248 p = 1) : d726 p ≤ (0 : Int) + d369 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d726, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7748 p hg
    simpa only [d726, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d726, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7755 p hg
    simpa only [d726, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7757 (p : Pattern) (guard : d1248 p = 1) : d705 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7746 p hg
    simpa only [d1248, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1248, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7758 (p : Pattern) (guard : d1248 p = 1) : d727 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d727, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7757 p hg
    simpa only [d727, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d727, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3788 p hg
    simpa only [d727, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7759 (p : Pattern) (guard : d1248 p = 1) : d728 p ≤ (0 : Int) + d372 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d728, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7757 p hg
    simpa only [d728, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d728, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7758 p hg
    simpa only [d728, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7760 (p : Pattern) (guard : d1248 p = 1) : d729 p ≤ (0 : Int) + d373 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d729, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7756 p hg
    simpa only [d729, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d729, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7759 p hg
    simpa only [d729, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7761 (p : Pattern) (guard : d1248 p = 1) : d730 p ≤ (0 : Int) + d374 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d730, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7754 p hg
    simpa only [d730, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d730, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7760 p hg
    simpa only [d730, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7762 (p : Pattern) (guard : d1248 p = 1) : d731 p ≤ (0 : Int) + d375 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d731, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7751 p hg
    simpa only [d731, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d731, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7761 p hg
    simpa only [d731, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7763 (p : Pattern) (guard : d1248 p = 1) : d732 p ≤ (0 : Int) + d376 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d732, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7737 p hg
    simpa only [d732, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d732, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7762 p hg
    simpa only [d732, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7764 (p : Pattern) (guard : d1248 p = 1) : d733 p ≤ (0 : Int) + d377 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d733, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7729 p hg
    simpa only [d733, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d733, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7735 p hg
    simpa only [d733, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7765 (p : Pattern) (guard : d1248 p = 1) : d734 p ≤ (0 : Int) + d378 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d734, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7719 p hg
    simpa only [d734, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d734, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7764 p hg
    simpa only [d734, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7766 (p : Pattern) (guard : d1248 p = 1) : d705 p ≤ (0 : Int) + d379 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7757 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7727 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7767 (p : Pattern) (guard : d1248 p = 1) : d705 p ≤ (0 : Int) + d380 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7757 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7766 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7768 (p : Pattern) (guard : d1248 p = 1) : d735 p ≤ (0 : Int) + d381 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d735, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7750 p hg
    simpa only [d735, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d735, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7767 p hg
    simpa only [d735, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7769 (p : Pattern) (guard : d1248 p = 1) : d736 p ≤ (0 : Int) + d382 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d736, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7745 p hg
    simpa only [d736, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d736, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7768 p hg
    simpa only [d736, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7770 (p : Pattern) (guard : d1248 p = 1) : d737 p ≤ (0 : Int) + d383 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d737, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7729 p hg
    simpa only [d737, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d737, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7734 p hg
    simpa only [d737, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7771 (p : Pattern) (guard : d1248 p = 1) : d738 p ≤ (0 : Int) + d384 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d738, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7759 p hg
    simpa only [d738, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d738, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3788 p hg
    simpa only [d738, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7772 (p : Pattern) (guard : d1248 p = 1) : d739 p ≤ (0 : Int) + d385 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d739, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7770 p hg
    simpa only [d739, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d739, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7771 p hg
    simpa only [d739, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7773 (p : Pattern) (guard : d1248 p = 1) : d740 p ≤ (0 : Int) + d386 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d740, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7769 p hg
    simpa only [d740, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d740, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7772 p hg
    simpa only [d740, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7774 (p : Pattern) (guard : d1248 p = 1) : d741 p ≤ (0 : Int) + d387 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d741, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7765 p hg
    simpa only [d741, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d741, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7773 p hg
    simpa only [d741, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7775 (p : Pattern) (guard : d1248 p = 1) : d742 p ≤ (0 : Int) + d388 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1248 p = 1 := by simpa only [d742, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7763 p hg
    simpa only [d742, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1248 p = 1 := by simpa only [d742, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7774 p hg
    simpa only [d742, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7776 (p : Pattern) (guard : d0 p = 1) : d700 p ≤ (3 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7777 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7778 (p : Pattern) (guard : d917 p = 1) : d5 p ≤ (3 : Int) + d4 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5138 p hg
    simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7777 p hg
    simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7779 (p : Pattern) (guard : d917 p = 1) : d5 p ≤ (3 : Int) + d5 p := by
  omega
theorem compare7780 (p : Pattern) (guard : d917 p = 1) : d5 p ≤ (3 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7778 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7779 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7781 (p : Pattern) (guard : d917 p = 1) : d2 p ≤ (3 : Int) + d2 p := by
  omega
theorem compare7782 (p : Pattern) (guard : d917 p = 1) : d37 p ≤ (3 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7778 p hg
    simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7781 p hg
    simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7783 (p : Pattern) (guard : d917 p = 1) : d697 p ≤ (3 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7780 p hg
    simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7782 p hg
    simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7784 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (3 : Int) + d1 p := by
  omega
theorem compare7785 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7786 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (3 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7784 p hg
    simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7785 p hg
    simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7787 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (3 : Int) + d11 p := by
  omega
theorem compare7788 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (3 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7787 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7789 (p : Pattern) (guard : d917 p = 1) : d39 p ≤ (3 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7781 p hg
    simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7790 (p : Pattern) (guard : d917 p = 1) : d698 p ≤ (3 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7788 p hg
    simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7789 p hg
    simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7791 (p : Pattern) (guard : d917 p = 1) : d699 p ≤ (3 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7783 p hg
    simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7790 p hg
    simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7792 (p : Pattern) (guard : d917 p = 1) : d700 p ≤ (3 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7783 p hg
    simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7791 p hg
    simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7793 (p : Pattern) (guard : d918 p = 1) : d700 p ≤ (3 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7776 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7792 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7794 (p : Pattern) (guard : d0 p = 1) : d700 p ≤ (3 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7795 (p : Pattern) (guard : d917 p = 1) : d37 p ≤ (3 : Int) + d37 p := by
  omega
theorem compare7796 (p : Pattern) (guard : d917 p = 1) : d697 p ≤ (3 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d697, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7780 p hg
    simpa only [d697, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d697, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7795 p hg
    simpa only [d697, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7797 (p : Pattern) (guard : d917 p = 1) : d39 p ≤ (3 : Int) + d39 p := by
  omega
theorem compare7798 (p : Pattern) (guard : d917 p = 1) : d698 p ≤ (3 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d698, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7788 p hg
    simpa only [d698, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d698, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7797 p hg
    simpa only [d698, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7799 (p : Pattern) (guard : d917 p = 1) : d699 p ≤ (3 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d699, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7796 p hg
    simpa only [d699, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d699, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7798 p hg
    simpa only [d699, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7800 (p : Pattern) (guard : d917 p = 1) : d700 p ≤ (3 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d700, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7796 p hg
    simpa only [d700, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d700, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7799 p hg
    simpa only [d700, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7801 (p : Pattern) (guard : d918 p = 1) : d700 p ≤ (3 : Int) + d42 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7794 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7800 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7802 (p : Pattern) (guard : d918 p = 1) : d700 p ≤ (3 : Int) + d1176 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7801 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7803 (p : Pattern) (guard : d918 p = 1) : d700 p ≤ (3 : Int) + d1177 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7802 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7804 (p : Pattern) (guard : d0 p = 1) : d699 p ≤ (3 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7805 (p : Pattern) (guard : d918 p = 1) : d699 p ≤ (3 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7804 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7791 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7806 (p : Pattern) (guard : d0 p = 1) : d699 p ≤ (3 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7807 (p : Pattern) (guard : d918 p = 1) : d699 p ≤ (3 : Int) + d41 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7806 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7799 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7808 (p : Pattern) (guard : d918 p = 1) : d699 p ≤ (3 : Int) + d1178 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7805 p hg
    simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7807 p hg
    simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7809 (p : Pattern) (guard : d918 p = 1) : d699 p ≤ (3 : Int) + d1179 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7805 p hg
    simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7808 p hg
    simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7810 (p : Pattern) (guard : d0 p = 1) : d702 p ≤ (3 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7811 (p : Pattern) (guard : d917 p = 1) : d701 p ≤ (3 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7783 p hg
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7781 p hg
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7812 (p : Pattern) (guard : d917 p = 1) : d702 p ≤ (3 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7791 p hg
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7811 p hg
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7813 (p : Pattern) (guard : d918 p = 1) : d702 p ≤ (3 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7810 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7812 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7814 (p : Pattern) (guard : d0 p = 1) : d702 p ≤ (3 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7815 (p : Pattern) (guard : d917 p = 1) : d701 p ≤ (3 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d701, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7796 p hg
    simpa only [d701, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d701, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7781 p hg
    simpa only [d701, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7816 (p : Pattern) (guard : d917 p = 1) : d702 p ≤ (3 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d702, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7799 p hg
    simpa only [d702, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d702, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d702, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7817 (p : Pattern) (guard : d918 p = 1) : d702 p ≤ (3 : Int) + d62 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7814 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7816 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7818 (p : Pattern) (guard : d918 p = 1) : d702 p ≤ (3 : Int) + d1180 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7819 (p : Pattern) (guard : d918 p = 1) : d702 p ≤ (3 : Int) + d1181 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7818 p hg
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7820 (p : Pattern) (guard : d918 p = 1) : d703 p ≤ (3 : Int) + d1182 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d703, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7809 p hg
    simpa only [d703, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d703, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7819 p hg
    simpa only [d703, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7821 (p : Pattern) (guard : d918 p = 1) : d704 p ≤ (3 : Int) + d1183 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d704, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7803 p hg
    simpa only [d704, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d704, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7820 p hg
    simpa only [d704, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7822 (p : Pattern) (guard : d0 p = 1) : d706 p ≤ (3 : Int) + d69 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7823 (p : Pattern) (guard : d917 p = 1) : d705 p ≤ (3 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d705, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7798 p hg
    simpa only [d705, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d705, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7781 p hg
    simpa only [d705, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7824 (p : Pattern) (guard : d917 p = 1) : d706 p ≤ (3 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d706, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7798 p hg
    simpa only [d706, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d706, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7823 p hg
    simpa only [d706, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7825 (p : Pattern) (guard : d918 p = 1) : d706 p ≤ (3 : Int) + d69 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7822 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7824 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7826 (p : Pattern) (guard : d918 p = 1) : d707 p ≤ (3 : Int) + d1184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d707, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d707, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d707, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7825 p hg
    simpa only [d707, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7827 (p : Pattern) (guard : d918 p = 1) : d708 p ≤ (3 : Int) + d1185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d708, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d708, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d708, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7826 p hg
    simpa only [d708, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7828 (p : Pattern) (guard : d0 p = 1) : d705 p ≤ (3 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7829 (p : Pattern) (guard : d918 p = 1) : d705 p ≤ (3 : Int) + d68 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7828 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7823 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7830 (p : Pattern) (guard : d918 p = 1) : d709 p ≤ (3 : Int) + d1186 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d709, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d709, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d709, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d709, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7831 (p : Pattern) (guard : d918 p = 1) : d710 p ≤ (3 : Int) + d1187 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d710, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d710, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d710, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7830 p hg
    simpa only [d710, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7832 (p : Pattern) (guard : d918 p = 1) : d711 p ≤ (3 : Int) + d1188 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d711, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7827 p hg
    simpa only [d711, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d711, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7831 p hg
    simpa only [d711, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7833 (p : Pattern) (guard : d918 p = 1) : d712 p ≤ (3 : Int) + d1189 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d712, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7805 p hg
    simpa only [d712, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d712, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d712, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7834 (p : Pattern) (guard : d918 p = 1) : d713 p ≤ (3 : Int) + d1190 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d713, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7805 p hg
    simpa only [d713, d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d713, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7833 p hg
    simpa only [d713, d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7835 (p : Pattern) (guard : d918 p = 1) : d714 p ≤ (3 : Int) + d1191 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d714, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d714, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d714, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d714, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7836 (p : Pattern) (guard : d918 p = 1) : d715 p ≤ (3 : Int) + d1192 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d715, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d715, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d715, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7835 p hg
    simpa only [d715, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7837 (p : Pattern) (guard : d918 p = 1) : d716 p ≤ (3 : Int) + d1193 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d716, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7834 p hg
    simpa only [d716, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d716, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7836 p hg
    simpa only [d716, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7838 (p : Pattern) (guard : d918 p = 1) : d717 p ≤ (3 : Int) + d1194 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d717, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7832 p hg
    simpa only [d717, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d717, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7837 p hg
    simpa only [d717, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7839 (p : Pattern) (guard : d918 p = 1) : d718 p ≤ (3 : Int) + d1195 p := by
  cases selected : p 106 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d718, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7821 p hg
    simpa only [d718, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d718, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7838 p hg
    simpa only [d718, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
