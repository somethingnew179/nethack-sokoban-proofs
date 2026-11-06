import NetHack.Soko22Hazard87.Compare067
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17000 (p : Pattern) (guard : d765 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d765, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16999 p hg
    simpa only [d765, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17001 (p : Pattern) (guard : d16231 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16996 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17000 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17002 (p : Pattern) (guard : d767 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17000 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17003 (p : Pattern) (guard : d16232 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17001 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17002 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17004 (p : Pattern) (guard : d16233 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17003 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17005 (p : Pattern) (guard : d16234 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17004 p hg
    simpa only [d16234, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d16234, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17006 (p : Pattern) (guard : d16235 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17005 p hg
    simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17007 (p : Pattern) (guard : d772 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17002 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17008 (p : Pattern) (guard : d773 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17007 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17009 (p : Pattern) (guard : d774 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17008 p hg
    simpa only [d774, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d774, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17010 (p : Pattern) (guard : d775 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17009 p hg
    simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17011 (p : Pattern) (guard : d16236 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17006 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17010 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17012 (p : Pattern) (guard : d16237 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17011 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17013 (p : Pattern) (guard : d16238 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17012 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17014 (p : Pattern) (guard : d16248 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16238 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17013 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17015 (p : Pattern) (guard : d780 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17010 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17016 (p : Pattern) (guard : d781 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17015 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17017 (p : Pattern) (guard : d782 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17016 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17018 (p : Pattern) (guard : d793 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17017 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17019 (p : Pattern) (guard : d16249 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16248 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17014 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17018 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17020 (p : Pattern) (guard : d16250 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16249 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17019 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17021 (p : Pattern) (guard : d16251 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16250 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17020 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17022 (p : Pattern) (guard : d16252 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16251 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17021 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17023 (p : Pattern) (guard : d16253 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16252 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17022 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17024 (p : Pattern) (guard : d171105 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171105, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171105, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16253 p = 1 := by simpa only [d171105, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17023 p hg
    simpa only [d171105, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17025 (p : Pattern) (guard : d171106 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171105 p = 1 := by simpa only [d171106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17024 p hg
    simpa only [d171106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17026 (p : Pattern) (guard : d171107 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171106 p = 1 := by simpa only [d171107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17025 p hg
    simpa only [d171107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17027 (p : Pattern) (guard : d171108 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171107 p = 1 := by simpa only [d171108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17026 p hg
    simpa only [d171108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17028 (p : Pattern) (guard : d171109 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171108 p = 1 := by simpa only [d171109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17027 p hg
    simpa only [d171109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17029 (p : Pattern) (guard : d171110 p = 1) : d48359 p ≤ (0 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171104 p = 1 := by simpa only [d171110, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16979 p hg
    simpa only [d171110, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171109 p = 1 := by simpa only [d171110, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17028 p hg
    simpa only [d171110, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17030 (p : Pattern) (guard : d661 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17031 (p : Pattern) (guard : d662 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d661 p = 1 := by simpa only [d662, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17030 p hg
    simpa only [d662, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d662, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d662, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17032 (p : Pattern) (guard : d16158 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17033 (p : Pattern) (guard : d16159 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16158 p = 1 := by simpa only [d16159, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17032 p hg
    simpa only [d16159, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16159, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d16159, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17034 (p : Pattern) (guard : d16160 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d662 p = 1 := by simpa only [d16160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17031 p hg
    simpa only [d16160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16159 p = 1 := by simpa only [d16160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17033 p hg
    simpa only [d16160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17035 (p : Pattern) (guard : d12860 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17036 (p : Pattern) (guard : d12861 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12860 p = 1 := by simpa only [d12861, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17035 p hg
    simpa only [d12861, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12861, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d12861, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17037 (p : Pattern) (guard : d973 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17038 (p : Pattern) (guard : d974 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d973 p = 1 := by simpa only [d974, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17037 p hg
    simpa only [d974, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d974, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d974, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17039 (p : Pattern) (guard : d12862 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12861 p = 1 := by simpa only [d12862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17036 p hg
    simpa only [d12862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d974 p = 1 := by simpa only [d12862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17038 p hg
    simpa only [d12862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17040 (p : Pattern) (guard : d16363 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16160 p = 1 := by simpa only [d16363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17034 p hg
    simpa only [d16363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12862 p = 1 := by simpa only [d16363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17039 p hg
    simpa only [d16363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17041 (p : Pattern) (guard : d975 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d415 p = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16852 p hg
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d974 p = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17038 p hg
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17042 (p : Pattern) (guard : d980 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d974 p = 1 := by simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17038 p hg
    simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17043 (p : Pattern) (guard : d981 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d975 p = 1 := by simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17041 p hg
    simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d980 p = 1 := by simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17042 p hg
    simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17044 (p : Pattern) (guard : d16372 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16363 p = 1 := by simpa only [d16372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17040 p hg
    simpa only [d16372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d981 p = 1 := by simpa only [d16372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17043 p hg
    simpa only [d16372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17045 (p : Pattern) (guard : d16373 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16373, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d16373, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16372 p = 1 := by simpa only [d16373, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17044 p hg
    simpa only [d16373, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17046 (p : Pattern) (guard : d16374 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16374, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d16374, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16373 p = 1 := by simpa only [d16374, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17045 p hg
    simpa only [d16374, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17047 (p : Pattern) (guard : d986 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d980 p = 1 := by simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17042 p hg
    simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17048 (p : Pattern) (guard : d987 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d981 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17043 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17047 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17049 (p : Pattern) (guard : d988 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d988, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d988, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d988, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17048 p hg
    simpa only [d988, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17050 (p : Pattern) (guard : d989 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d989, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d989, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d988 p = 1 := by simpa only [d989, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17049 p hg
    simpa only [d989, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17051 (p : Pattern) (guard : d16375 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16374 p = 1 := by simpa only [d16375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17046 p hg
    simpa only [d16375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d989 p = 1 := by simpa only [d16375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17050 p hg
    simpa only [d16375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17052 (p : Pattern) (guard : d995 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d989 p = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17050 p hg
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17053 (p : Pattern) (guard : d16380 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16375 p = 1 := by simpa only [d16380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17051 p hg
    simpa only [d16380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d995 p = 1 := by simpa only [d16380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17052 p hg
    simpa only [d16380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17054 (p : Pattern) (guard : d16381 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16380 p = 1 := by simpa only [d16381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17053 p hg
    simpa only [d16381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d16381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17055 (p : Pattern) (guard : d16382 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16381 p = 1 := by simpa only [d16382, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17054 p hg
    simpa only [d16382, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16382, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d16382, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17056 (p : Pattern) (guard : d16383 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16383, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d16383, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16382 p = 1 := by simpa only [d16383, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17055 p hg
    simpa only [d16383, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17057 (p : Pattern) (guard : d1004 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d995 p = 1 := by simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17052 p hg
    simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17058 (p : Pattern) (guard : d1005 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1004 p = 1 := by simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17057 p hg
    simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17059 (p : Pattern) (guard : d1006 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1005 p = 1 := by simpa only [d1006, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17058 p hg
    simpa only [d1006, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1006, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d1006, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17060 (p : Pattern) (guard : d1007 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1007, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d1007, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1006 p = 1 := by simpa only [d1007, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17059 p hg
    simpa only [d1007, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17061 (p : Pattern) (guard : d16388 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16383 p = 1 := by simpa only [d16388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17056 p hg
    simpa only [d16388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1007 p = 1 := by simpa only [d16388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17060 p hg
    simpa only [d16388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17062 (p : Pattern) (guard : d16389 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16388 p = 1 := by simpa only [d16389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17061 p hg
    simpa only [d16389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17063 (p : Pattern) (guard : d16390 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16389 p = 1 := by simpa only [d16390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17062 p hg
    simpa only [d16390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17064 (p : Pattern) (guard : d16391 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16390 p = 1 := by simpa only [d16391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17063 p hg
    simpa only [d16391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17065 (p : Pattern) (guard : d1060 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1007 p = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17060 p hg
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17066 (p : Pattern) (guard : d1061 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1060 p = 1 := by simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17065 p hg
    simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17067 (p : Pattern) (guard : d1062 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1061 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17066 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17068 (p : Pattern) (guard : d1063 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1062 p = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17067 p hg
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17069 (p : Pattern) (guard : d171111 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16391 p = 1 := by simpa only [d171111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17064 p hg
    simpa only [d171111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1063 p = 1 := by simpa only [d171111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17068 p hg
    simpa only [d171111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17070 (p : Pattern) (guard : d171112 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171111 p = 1 := by simpa only [d171112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17069 p hg
    simpa only [d171112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17071 (p : Pattern) (guard : d171113 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d171112 p = 1 := by simpa only [d171113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17070 p hg
    simpa only [d171113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17072 (p : Pattern) (guard : d171114 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171113 p = 1 := by simpa only [d171114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17071 p hg
    simpa only [d171114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17073 (p : Pattern) (guard : d171115 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171114 p = 1 := by simpa only [d171115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17072 p hg
    simpa only [d171115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17074 (p : Pattern) (guard : d171116 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171116, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171116, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171115 p = 1 := by simpa only [d171116, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17073 p hg
    simpa only [d171116, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17075 (p : Pattern) (guard : d171117 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171116 p = 1 := by simpa only [d171117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17074 p hg
    simpa only [d171117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17076 (p : Pattern) (guard : d171118 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171117 p = 1 := by simpa only [d171118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17075 p hg
    simpa only [d171118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17077 (p : Pattern) (guard : d171119 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171118 p = 1 := by simpa only [d171119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17076 p hg
    simpa only [d171119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17078 (p : Pattern) (guard : d171120 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171119 p = 1 := by simpa only [d171120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17077 p hg
    simpa only [d171120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17079 (p : Pattern) (guard : d171121 p = 1) : d48387 p ≤ (0 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171120 p = 1 := by simpa only [d171121, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17078 p hg
    simpa only [d171121, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171121, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16625 p hg
    simpa only [d171121, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17080 (p : Pattern) (guard : d171122 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171110 p = 1 := by simpa only [d171122, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17029 p hg
    simpa only [d171122, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171121 p = 1 := by simpa only [d171122, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17079 p hg
    simpa only [d171122, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17081 (p : Pattern) (guard : d171123 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171122 p = 1 := by simpa only [d171123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17080 p hg
    simpa only [d171123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17082 (p : Pattern) (guard : d171124 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171123 p = 1 := by simpa only [d171124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17081 p hg
    simpa only [d171124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17083 (p : Pattern) (guard : d171125 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171124 p = 1 := by simpa only [d171125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17082 p hg
    simpa only [d171125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17084 (p : Pattern) (guard : d171126 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171125 p = 1 := by simpa only [d171126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17083 p hg
    simpa only [d171126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17085 (p : Pattern) (guard : d171127 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171126 p = 1 := by simpa only [d171127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17084 p hg
    simpa only [d171127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17086 (p : Pattern) (guard : d171128 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171127 p = 1 := by simpa only [d171128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17085 p hg
    simpa only [d171128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17087 (p : Pattern) (guard : d171129 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171128 p = 1 := by simpa only [d171129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17086 p hg
    simpa only [d171129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17088 (p : Pattern) (guard : d171130 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d171102 p = 1 := by simpa only [d171130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16897 p hg
    simpa only [d171130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171129 p = 1 := by simpa only [d171130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17087 p hg
    simpa only [d171130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17089 (p : Pattern) (guard : d1102 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17090 (p : Pattern) (guard : d1103 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17089 p hg
    simpa only [d1103, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d1103, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17091 (p : Pattern) (guard : d16438 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17092 (p : Pattern) (guard : d16439 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17091 p hg
    simpa only [d16439, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d16439, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17093 (p : Pattern) (guard : d16440 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17090 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17092 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17094 (p : Pattern) (guard : d14758 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17095 (p : Pattern) (guard : d14759 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17094 p hg
    simpa only [d14759, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d14759, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17096 (p : Pattern) (guard : d14763 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17097 (p : Pattern) (guard : d14764 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17096 p hg
    simpa only [d14764, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d14764, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17098 (p : Pattern) (guard : d16441 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17095 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17099 (p : Pattern) (guard : d16442 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17093 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17098 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17100 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17101 (p : Pattern) (guard : d1113 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17100 p hg
    simpa only [d1113, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d1113, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17102 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17103 (p : Pattern) (guard : d1124 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17102 p hg
    simpa only [d1124, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d1124, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17104 (p : Pattern) (guard : d1125 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17101 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17103 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17105 (p : Pattern) (guard : d14765 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17097 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17106 (p : Pattern) (guard : d16443 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17104 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17105 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17107 (p : Pattern) (guard : d16444 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17099 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17106 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17108 (p : Pattern) (guard : d16445 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d16445, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17107 p hg
    simpa only [d16445, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17109 (p : Pattern) (guard : d16446 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d16446, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17108 p hg
    simpa only [d16446, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17110 (p : Pattern) (guard : d5020 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17111 (p : Pattern) (guard : d5021 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17110 p hg
    simpa only [d5021, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d5021, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17112 (p : Pattern) (guard : d5022 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17111 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17113 (p : Pattern) (guard : d14770 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17114 (p : Pattern) (guard : d14771 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17113 p hg
    simpa only [d14771, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d14771, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17115 (p : Pattern) (guard : d14772 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17114 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17116 (p : Pattern) (guard : d14773 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17112 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17115 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17117 (p : Pattern) (guard : d16447 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17106 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17116 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17118 (p : Pattern) (guard : d16448 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d16448, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17117 p hg
    simpa only [d16448, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17119 (p : Pattern) (guard : d16449 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d16449, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17118 p hg
    simpa only [d16449, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17120 (p : Pattern) (guard : d16450 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17109 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17121 (p : Pattern) (guard : d1127 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17103 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17122 (p : Pattern) (guard : d14778 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17121 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17115 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17123 (p : Pattern) (guard : d16451 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17106 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17122 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17124 (p : Pattern) (guard : d16452 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d16452, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17123 p hg
    simpa only [d16452, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17125 (p : Pattern) (guard : d16453 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d16453, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17124 p hg
    simpa only [d16453, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17126 (p : Pattern) (guard : d16454 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17125 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17127 (p : Pattern) (guard : d16455 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17120 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17126 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17128 (p : Pattern) (guard : d16456 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17127 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17129 (p : Pattern) (guard : d16457 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17128 p hg
    simpa only [d16457, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16457, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17130 (p : Pattern) (guard : d16458 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d16458, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17129 p hg
    simpa only [d16458, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17131 (p : Pattern) (guard : d16459 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17126 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17132 (p : Pattern) (guard : d16460 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17131 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17133 (p : Pattern) (guard : d16461 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17132 p hg
    simpa only [d16461, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16461, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17134 (p : Pattern) (guard : d16462 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d16462, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17133 p hg
    simpa only [d16462, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17135 (p : Pattern) (guard : d16463 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17130 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17134 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17136 (p : Pattern) (guard : d16464 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17135 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17137 (p : Pattern) (guard : d16465 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17136 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17138 (p : Pattern) (guard : d16466 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16465 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17137 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17139 (p : Pattern) (guard : d16467 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17134 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17140 (p : Pattern) (guard : d16468 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17141 (p : Pattern) (guard : d16469 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17140 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17142 (p : Pattern) (guard : d16470 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16469 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17141 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17143 (p : Pattern) (guard : d16471 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16466 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17138 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17142 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17144 (p : Pattern) (guard : d16472 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16471 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17143 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17145 (p : Pattern) (guard : d16473 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16472 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17144 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17146 (p : Pattern) (guard : d16474 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16473 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17145 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17147 (p : Pattern) (guard : d16475 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16474 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17146 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17148 (p : Pattern) (guard : d16476 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16475 p = 1 := by simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17147 p hg
    simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17149 (p : Pattern) (guard : d16446 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d16446, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17108 p hg
    simpa only [d16446, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17150 (p : Pattern) (guard : d16449 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d16449, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17118 p hg
    simpa only [d16449, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17151 (p : Pattern) (guard : d16450 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17149 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17150 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17152 (p : Pattern) (guard : d16453 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d16453, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17124 p hg
    simpa only [d16453, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17153 (p : Pattern) (guard : d16454 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17152 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17154 (p : Pattern) (guard : d16455 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17151 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17153 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17155 (p : Pattern) (guard : d16456 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17154 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17156 (p : Pattern) (guard : d16457 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17155 p hg
    simpa only [d16457, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16457, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17157 (p : Pattern) (guard : d16458 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d16458, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17156 p hg
    simpa only [d16458, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17158 (p : Pattern) (guard : d16459 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17153 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17159 (p : Pattern) (guard : d16460 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17158 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17160 (p : Pattern) (guard : d16461 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17159 p hg
    simpa only [d16461, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16461, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17161 (p : Pattern) (guard : d16462 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d16462, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17160 p hg
    simpa only [d16462, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17162 (p : Pattern) (guard : d16463 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17157 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17161 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17163 (p : Pattern) (guard : d16464 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17162 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17164 (p : Pattern) (guard : d16465 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17163 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17165 (p : Pattern) (guard : d16466 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16465 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17164 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17166 (p : Pattern) (guard : d16467 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17161 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17167 (p : Pattern) (guard : d16468 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17166 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17168 (p : Pattern) (guard : d16469 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17167 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17169 (p : Pattern) (guard : d16470 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16469 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17168 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17170 (p : Pattern) (guard : d16471 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16466 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17165 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17169 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17171 (p : Pattern) (guard : d16472 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16471 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17170 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17172 (p : Pattern) (guard : d16473 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16472 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17171 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17173 (p : Pattern) (guard : d16474 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16473 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17172 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17174 (p : Pattern) (guard : d16475 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16474 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17173 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17175 (p : Pattern) (guard : d16479 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16465 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17137 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17176 (p : Pattern) (guard : d16480 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16469 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17141 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17177 (p : Pattern) (guard : d16481 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16479 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17175 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16480 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17176 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17178 (p : Pattern) (guard : d16482 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16481 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17177 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17179 (p : Pattern) (guard : d16483 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16482 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17178 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17180 (p : Pattern) (guard : d16484 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16483 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17179 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17181 (p : Pattern) (guard : d16485 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16484 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17180 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17182 (p : Pattern) (guard : d16486 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16475 p = 1 := by simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16485 p = 1 := by simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17181 p hg
    simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17183 (p : Pattern) (guard : d16487 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16476 p = 1 := by simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17148 p hg
    simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16486 p = 1 := by simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17182 p hg
    simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17184 (p : Pattern) (guard : d16488 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16487 p = 1 := by simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17183 p hg
    simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17185 (p : Pattern) (guard : d171131 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16488 p = 1 := by simpa only [d171131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17184 p hg
    simpa only [d171131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17186 (p : Pattern) (guard : d171132 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171131 p = 1 := by simpa only [d171132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17185 p hg
    simpa only [d171132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17187 (p : Pattern) (guard : d1102 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17188 (p : Pattern) (guard : d1103 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17187 p hg
    simpa only [d1103, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d1103, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17189 (p : Pattern) (guard : d16438 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17190 (p : Pattern) (guard : d16439 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17189 p hg
    simpa only [d16439, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d16439, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17191 (p : Pattern) (guard : d16440 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17188 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17190 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17192 (p : Pattern) (guard : d14758 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17193 (p : Pattern) (guard : d14759 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17192 p hg
    simpa only [d14759, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d14759, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17194 (p : Pattern) (guard : d14763 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17195 (p : Pattern) (guard : d14764 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17194 p hg
    simpa only [d14764, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d14764, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17196 (p : Pattern) (guard : d16441 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17193 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17195 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17197 (p : Pattern) (guard : d16442 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17191 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17196 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17198 (p : Pattern) (guard : d1112 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17199 (p : Pattern) (guard : d1113 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17198 p hg
    simpa only [d1113, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d1113, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17200 (p : Pattern) (guard : d1123 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17201 (p : Pattern) (guard : d1124 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17200 p hg
    simpa only [d1124, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d1124, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17202 (p : Pattern) (guard : d1125 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17199 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17201 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17203 (p : Pattern) (guard : d14765 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17195 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17204 (p : Pattern) (guard : d16443 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17202 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17203 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17205 (p : Pattern) (guard : d16444 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17197 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17206 (p : Pattern) (guard : d16445 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d16445, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17205 p hg
    simpa only [d16445, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17207 (p : Pattern) (guard : d16446 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d16446, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17206 p hg
    simpa only [d16446, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17208 (p : Pattern) (guard : d5020 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17209 (p : Pattern) (guard : d5021 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17208 p hg
    simpa only [d5021, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d5021, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17210 (p : Pattern) (guard : d5022 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17209 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17211 (p : Pattern) (guard : d14770 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17212 (p : Pattern) (guard : d14771 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17211 p hg
    simpa only [d14771, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d14771, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17213 (p : Pattern) (guard : d14772 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17212 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17214 (p : Pattern) (guard : d14773 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17210 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17213 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17215 (p : Pattern) (guard : d16447 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17214 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17216 (p : Pattern) (guard : d16448 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d16448, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17215 p hg
    simpa only [d16448, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17217 (p : Pattern) (guard : d16449 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d16449, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17216 p hg
    simpa only [d16449, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17218 (p : Pattern) (guard : d16450 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17207 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17217 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17219 (p : Pattern) (guard : d1127 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17201 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17220 (p : Pattern) (guard : d14778 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17219 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17213 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17221 (p : Pattern) (guard : d16451 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17220 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17222 (p : Pattern) (guard : d16452 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d16452, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17221 p hg
    simpa only [d16452, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17223 (p : Pattern) (guard : d16453 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d16453, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17222 p hg
    simpa only [d16453, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17224 (p : Pattern) (guard : d16454 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17223 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17225 (p : Pattern) (guard : d16455 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17218 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17224 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17226 (p : Pattern) (guard : d16456 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17225 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17227 (p : Pattern) (guard : d16457 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17226 p hg
    simpa only [d16457, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d16457, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17228 (p : Pattern) (guard : d16458 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d16458, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17227 p hg
    simpa only [d16458, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17229 (p : Pattern) (guard : d16459 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17224 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17230 (p : Pattern) (guard : d16460 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17229 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17231 (p : Pattern) (guard : d16461 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d16461, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d16461, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17232 (p : Pattern) (guard : d16462 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17231 p hg
    simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17233 (p : Pattern) (guard : d16463 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17228 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17232 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17234 (p : Pattern) (guard : d16464 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17233 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17235 (p : Pattern) (guard : d16465 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17234 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17236 (p : Pattern) (guard : d16479 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16465 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17235 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17237 (p : Pattern) (guard : d16467 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17232 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17238 (p : Pattern) (guard : d16468 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17237 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17239 (p : Pattern) (guard : d16469 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17238 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17240 (p : Pattern) (guard : d16480 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16469 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17239 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17241 (p : Pattern) (guard : d16481 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16479 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17236 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16480 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17240 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17242 (p : Pattern) (guard : d16482 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16481 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17241 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17243 (p : Pattern) (guard : d16483 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16482 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17242 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17244 (p : Pattern) (guard : d16484 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16483 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17243 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17245 (p : Pattern) (guard : d16485 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16484 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17244 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17246 (p : Pattern) (guard : d171133 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171133, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171133, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16485 p = 1 := by simpa only [d171133, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17245 p hg
    simpa only [d171133, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17247 (p : Pattern) (guard : d171134 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171133 p = 1 := by simpa only [d171134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17246 p hg
    simpa only [d171134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17248 (p : Pattern) (guard : d171135 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171134 p = 1 := by simpa only [d171135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17247 p hg
    simpa only [d171135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17249 (p : Pattern) (guard : d171136 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171135 p = 1 := by simpa only [d171136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17248 p hg
    simpa only [d171136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171136, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
