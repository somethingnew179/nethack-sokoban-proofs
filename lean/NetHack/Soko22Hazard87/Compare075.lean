import NetHack.Soko22Hazard87.Compare074
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18750 (p : Pattern) (guard : d16277 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16277, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16277, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16276 p = 1 := by simpa only [d16277, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18706 p hg
    simpa only [d16277, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18751 (p : Pattern) (guard : d16281 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16281, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16281, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16280 p = 1 := by simpa only [d16281, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18710 p hg
    simpa only [d16281, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18752 (p : Pattern) (guard : d16282 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16277 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18750 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16281 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18751 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18753 (p : Pattern) (guard : d16283 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16282 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18752 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16231 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18636 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18754 (p : Pattern) (guard : d16284 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16283 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18753 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18755 (p : Pattern) (guard : d16285 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16284 p = 1 := by simpa only [d16285, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18754 p hg
    simpa only [d16285, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16285, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16285, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18756 (p : Pattern) (guard : d16286 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16286, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16286, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16285 p = 1 := by simpa only [d16286, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18755 p hg
    simpa only [d16286, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18757 (p : Pattern) (guard : d16287 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16286 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18756 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16235 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18641 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18758 (p : Pattern) (guard : d16288 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16287 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18757 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18759 (p : Pattern) (guard : d16289 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16288 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18758 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18760 (p : Pattern) (guard : d16290 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16289 p = 1 := by simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18759 p hg
    simpa only [d16290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18761 (p : Pattern) (guard : d16291 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16290 p = 1 := by simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18760 p hg
    simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16239 p = 1 := by simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18649 p hg
    simpa only [d16291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18762 (p : Pattern) (guard : d128270 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16291 p = 1 := by simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18761 p hg
    simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18763 (p : Pattern) (guard : d16311 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18641 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18764 (p : Pattern) (guard : d16312 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16311 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18763 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18765 (p : Pattern) (guard : d16313 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16312 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18764 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18766 (p : Pattern) (guard : d16314 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16313 p = 1 := by simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18765 p hg
    simpa only [d16314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18767 (p : Pattern) (guard : d16315 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16314 p = 1 := by simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18766 p hg
    simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18768 (p : Pattern) (guard : d16316 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16315 p = 1 := by simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18767 p hg
    simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18769 (p : Pattern) (guard : d128271 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128270 p = 1 := by simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18762 p hg
    simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16316 p = 1 := by simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18768 p hg
    simpa only [d128271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18770 (p : Pattern) (guard : d128272 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16269 p = 1 := by simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18749 p hg
    simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128271 p = 1 := by simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18769 p hg
    simpa only [d128272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18771 (p : Pattern) (guard : d128273 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16263 p = 1 := by simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18740 p hg
    simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128272 p = 1 := by simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18770 p hg
    simpa only [d128273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18772 (p : Pattern) (guard : d16321 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16258 p = 1 := by simpa only [d16321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18670 p hg
    simpa only [d16321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18773 (p : Pattern) (guard : d916 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d805 p = 1 := by simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18672 p hg
    simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18774 (p : Pattern) (guard : d16322 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16321 p = 1 := by simpa only [d16322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18772 p hg
    simpa only [d16322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d16322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18773 p hg
    simpa only [d16322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18775 (p : Pattern) (guard : d16323 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16322 p = 1 := by simpa only [d16323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18774 p hg
    simpa only [d16323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18776 (p : Pattern) (guard : d16324 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16323 p = 1 := by simpa only [d16324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18775 p hg
    simpa only [d16324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18777 (p : Pattern) (guard : d16325 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16324 p = 1 := by simpa only [d16325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18776 p hg
    simpa only [d16325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18778 (p : Pattern) (guard : d16326 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16265 p = 1 := by simpa only [d16326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18679 p hg
    simpa only [d16326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18779 (p : Pattern) (guard : d922 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d815 p = 1 := by simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18682 p hg
    simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18780 (p : Pattern) (guard : d16327 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16326 p = 1 := by simpa only [d16327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18778 p hg
    simpa only [d16327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d922 p = 1 := by simpa only [d16327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18779 p hg
    simpa only [d16327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18781 (p : Pattern) (guard : d16328 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16327 p = 1 := by simpa only [d16328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18780 p hg
    simpa only [d16328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18782 (p : Pattern) (guard : d16329 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16328 p = 1 := by simpa only [d16329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18781 p hg
    simpa only [d16329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18783 (p : Pattern) (guard : d16330 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16289 p = 1 := by simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18719 p hg
    simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18784 (p : Pattern) (guard : d16331 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16330 p = 1 := by simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18783 p hg
    simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16248 p = 1 := by simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18659 p hg
    simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18785 (p : Pattern) (guard : d128275 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16331 p = 1 := by simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18784 p hg
    simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18786 (p : Pattern) (guard : d16335 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16313 p = 1 := by simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18725 p hg
    simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18787 (p : Pattern) (guard : d16336 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16335 p = 1 := by simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18786 p hg
    simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18788 (p : Pattern) (guard : d16337 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16336 p = 1 := by simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18787 p hg
    simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18789 (p : Pattern) (guard : d128276 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128275 p = 1 := by simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18785 p hg
    simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16337 p = 1 := by simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18788 p hg
    simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18790 (p : Pattern) (guard : d128277 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16329 p = 1 := by simpa only [d128277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18782 p hg
    simpa only [d128277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128276 p = 1 := by simpa only [d128277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18789 p hg
    simpa only [d128277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18791 (p : Pattern) (guard : d128278 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16325 p = 1 := by simpa only [d128278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18777 p hg
    simpa only [d128278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128277 p = 1 := by simpa only [d128278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18790 p hg
    simpa only [d128278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18792 (p : Pattern) (guard : d128279 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128273 p = 1 := by simpa only [d128279, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18771 p hg
    simpa only [d128279, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128278 p = 1 := by simpa only [d128279, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18791 p hg
    simpa only [d128279, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18793 (p : Pattern) (guard : d128280 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128274 p = 1 := by simpa only [d128280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18732 p hg
    simpa only [d128280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128279 p = 1 := by simpa only [d128280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18792 p hg
    simpa only [d128280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18794 (p : Pattern) (guard : d939 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d783 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18625 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18795 (p : Pattern) (guard : d940 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d939 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18794 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18796 (p : Pattern) (guard : d941 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d940 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18795 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18797 (p : Pattern) (guard : d942 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d941 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18796 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18798 (p : Pattern) (guard : d943 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d942 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18797 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18799 (p : Pattern) (guard : d16343 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16244 p = 1 := by simpa only [d16343, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18658 p hg
    simpa only [d16343, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d943 p = 1 := by simpa only [d16343, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18798 p hg
    simpa only [d16343, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18800 (p : Pattern) (guard : d939 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d783 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18653 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18801 (p : Pattern) (guard : d940 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d939 p = 1 := by simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18800 p hg
    simpa only [d940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18802 (p : Pattern) (guard : d941 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d940 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18801 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18803 (p : Pattern) (guard : d942 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d941 p = 1 := by simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18802 p hg
    simpa only [d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18804 (p : Pattern) (guard : d943 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d942 p = 1 := by simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18803 p hg
    simpa only [d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18805 (p : Pattern) (guard : d945 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18660 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18806 (p : Pattern) (guard : d946 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d945 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18805 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18807 (p : Pattern) (guard : d947 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d946 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18806 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18808 (p : Pattern) (guard : d948 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d947 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18807 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18809 (p : Pattern) (guard : d949 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d948 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18808 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18810 (p : Pattern) (guard : d950 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d943 p = 1 := by simpa only [d950, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18804 p hg
    simpa only [d950, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d949 p = 1 := by simpa only [d950, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18809 p hg
    simpa only [d950, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18811 (p : Pattern) (guard : d16344 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16343 p = 1 := by simpa only [d16344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18799 p hg
    simpa only [d16344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d950 p = 1 := by simpa only [d16344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18810 p hg
    simpa only [d16344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18812 (p : Pattern) (guard : d128281 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128280 p = 1 := by simpa only [d128281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18793 p hg
    simpa only [d128281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16344 p = 1 := by simpa only [d128281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18811 p hg
    simpa only [d128281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18813 (p : Pattern) (guard : d128282 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128281 p = 1 := by simpa only [d128282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18812 p hg
    simpa only [d128282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d128282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18814 (p : Pattern) (guard : d128283 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d16257 p = 1 := by simpa only [d128283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18669 p hg
    simpa only [d128283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128282 p = 1 := by simpa only [d128283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18813 p hg
    simpa only [d128283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18815 (p : Pattern) (guard : d833 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18816 (p : Pattern) (guard : d834 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18815 p hg
    simpa only [d834, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d834, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18817 (p : Pattern) (guard : d835 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d834 p = 1 := by simpa only [d835, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18816 p hg
    simpa only [d835, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d835, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18818 (p : Pattern) (guard : d836 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18817 p hg
    simpa only [d836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18819 (p : Pattern) (guard : d837 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d837, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18818 p hg
    simpa only [d837, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d837, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d837, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18820 (p : Pattern) (guard : d9586 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18821 (p : Pattern) (guard : d9587 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9586 p = 1 := by simpa only [d9587, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18820 p hg
    simpa only [d9587, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9587, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9587, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18822 (p : Pattern) (guard : d9589 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9587 p = 1 := by simpa only [d9589, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18821 p hg
    simpa only [d9589, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9589, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9589, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18823 (p : Pattern) (guard : d16270 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16270, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d16270, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9589 p = 1 := by simpa only [d16270, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18822 p hg
    simpa only [d16270, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18824 (p : Pattern) (guard : d16271 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16270 p = 1 := by simpa only [d16271, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18823 p hg
    simpa only [d16271, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16271, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d16271, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18825 (p : Pattern) (guard : d16272 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d837 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18819 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16271 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18824 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18826 (p : Pattern) (guard : d9596 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18827 (p : Pattern) (guard : d9597 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9596 p = 1 := by simpa only [d9597, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18826 p hg
    simpa only [d9597, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9597, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9597, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18828 (p : Pattern) (guard : d9599 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9597 p = 1 := by simpa only [d9599, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18827 p hg
    simpa only [d9599, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9599, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9599, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18829 (p : Pattern) (guard : d14529 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14529, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d14529, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9599 p = 1 := by simpa only [d14529, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18828 p hg
    simpa only [d14529, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18830 (p : Pattern) (guard : d14530 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14529 p = 1 := by simpa only [d14530, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18829 p hg
    simpa only [d14530, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14530, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d14530, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18831 (p : Pattern) (guard : d16273 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14530 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18830 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12749 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18523 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18832 (p : Pattern) (guard : d16274 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16272 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18825 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16273 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18831 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18833 (p : Pattern) (guard : d750 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18834 (p : Pattern) (guard : d751 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18833 p hg
    simpa only [d751, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d751, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18835 (p : Pattern) (guard : d752 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18834 p hg
    simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18836 (p : Pattern) (guard : d753 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18835 p hg
    simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18837 (p : Pattern) (guard : d754 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18836 p hg
    simpa only [d754, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d754, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18838 (p : Pattern) (guard : d12750 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18523 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18837 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18839 (p : Pattern) (guard : d16227 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18518 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18838 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18840 (p : Pattern) (guard : d16275 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16274 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18832 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16227 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18839 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18841 (p : Pattern) (guard : d16276 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16276, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16276, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16275 p = 1 := by simpa only [d16276, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18840 p hg
    simpa only [d16276, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18842 (p : Pattern) (guard : d16277 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16277, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16277, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16276 p = 1 := by simpa only [d16277, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18841 p hg
    simpa only [d16277, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18843 (p : Pattern) (guard : d757 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18837 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18844 (p : Pattern) (guard : d16278 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12750 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18838 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18843 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18845 (p : Pattern) (guard : d16279 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18839 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16278 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18844 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18846 (p : Pattern) (guard : d16280 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16280, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16280, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16279 p = 1 := by simpa only [d16280, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18845 p hg
    simpa only [d16280, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18847 (p : Pattern) (guard : d16281 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16281, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16281, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16280 p = 1 := by simpa only [d16281, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18846 p hg
    simpa only [d16281, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18848 (p : Pattern) (guard : d16282 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16277 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18842 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16281 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18847 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18849 (p : Pattern) (guard : d755 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18254 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18837 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18850 (p : Pattern) (guard : d758 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18849 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18843 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18851 (p : Pattern) (guard : d16228 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18839 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18850 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18852 (p : Pattern) (guard : d16229 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16229, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18851 p hg
    simpa only [d16229, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18853 (p : Pattern) (guard : d16230 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16230, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18852 p hg
    simpa only [d16230, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18854 (p : Pattern) (guard : d762 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18843 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18855 (p : Pattern) (guard : d763 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18850 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18854 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18856 (p : Pattern) (guard : d764 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d764, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18855 p hg
    simpa only [d764, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18857 (p : Pattern) (guard : d765 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d765, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18856 p hg
    simpa only [d765, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18858 (p : Pattern) (guard : d16231 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18853 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18857 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18859 (p : Pattern) (guard : d16283 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16282 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18848 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16231 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18858 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18860 (p : Pattern) (guard : d16284 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16283 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18859 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18861 (p : Pattern) (guard : d16285 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16284 p = 1 := by simpa only [d16285, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18860 p hg
    simpa only [d16285, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16285, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16285, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18862 (p : Pattern) (guard : d16286 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16286, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16286, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16285 p = 1 := by simpa only [d16286, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18861 p hg
    simpa only [d16286, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18863 (p : Pattern) (guard : d767 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18857 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18864 (p : Pattern) (guard : d16232 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18858 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18863 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18865 (p : Pattern) (guard : d16233 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18864 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18866 (p : Pattern) (guard : d16234 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18865 p hg
    simpa only [d16234, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16234, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18867 (p : Pattern) (guard : d16235 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18866 p hg
    simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18868 (p : Pattern) (guard : d16287 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16286 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18862 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16235 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18867 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18869 (p : Pattern) (guard : d16288 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16287 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18868 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18870 (p : Pattern) (guard : d16289 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16288 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18869 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18871 (p : Pattern) (guard : d16330 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16289 p = 1 := by simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18870 p hg
    simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18872 (p : Pattern) (guard : d772 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18863 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18873 (p : Pattern) (guard : d773 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18872 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18874 (p : Pattern) (guard : d774 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18873 p hg
    simpa only [d774, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d774, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18875 (p : Pattern) (guard : d775 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18874 p hg
    simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18876 (p : Pattern) (guard : d16236 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18867 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18875 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18877 (p : Pattern) (guard : d16237 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18876 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18878 (p : Pattern) (guard : d16238 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18877 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18879 (p : Pattern) (guard : d16248 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16238 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18878 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18880 (p : Pattern) (guard : d16331 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16330 p = 1 := by simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18871 p hg
    simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16248 p = 1 := by simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18879 p hg
    simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18881 (p : Pattern) (guard : d128275 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16331 p = 1 := by simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18880 p hg
    simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18882 (p : Pattern) (guard : d16311 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18867 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18883 (p : Pattern) (guard : d16312 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16311 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18882 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18884 (p : Pattern) (guard : d16313 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16312 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18883 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18885 (p : Pattern) (guard : d16335 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16313 p = 1 := by simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18884 p hg
    simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18886 (p : Pattern) (guard : d16336 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16335 p = 1 := by simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18885 p hg
    simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18887 (p : Pattern) (guard : d16337 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16336 p = 1 := by simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18886 p hg
    simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18888 (p : Pattern) (guard : d128276 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128275 p = 1 := by simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18881 p hg
    simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16337 p = 1 := by simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18887 p hg
    simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18889 (p : Pattern) (guard : d128284 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128276 p = 1 := by simpa only [d128284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18888 p hg
    simpa only [d128284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18890 (p : Pattern) (guard : d128285 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128284 p = 1 := by simpa only [d128285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18889 p hg
    simpa only [d128285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18891 (p : Pattern) (guard : d128286 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128286, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128286, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128285 p = 1 := by simpa only [d128286, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18890 p hg
    simpa only [d128286, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18892 (p : Pattern) (guard : d128287 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128286 p = 1 := by simpa only [d128287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18891 p hg
    simpa only [d128287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18893 (p : Pattern) (guard : d780 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18875 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18894 (p : Pattern) (guard : d781 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18893 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18895 (p : Pattern) (guard : d782 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18894 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18896 (p : Pattern) (guard : d793 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18895 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18897 (p : Pattern) (guard : d945 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18896 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18898 (p : Pattern) (guard : d946 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d945 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18897 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18899 (p : Pattern) (guard : d947 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d946 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18898 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18900 (p : Pattern) (guard : d948 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d947 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18899 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18901 (p : Pattern) (guard : d949 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d948 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18900 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18902 (p : Pattern) (guard : d959 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d959, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d959, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d949 p = 1 := by simpa only [d959, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18901 p hg
    simpa only [d959, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18903 (p : Pattern) (guard : d960 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d959 p = 1 := by simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18902 p hg
    simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18904 (p : Pattern) (guard : d128288 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128287 p = 1 := by simpa only [d128288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18892 p hg
    simpa only [d128288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d960 p = 1 := by simpa only [d128288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18903 p hg
    simpa only [d128288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18905 (p : Pattern) (guard : d128289 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128288 p = 1 := by simpa only [d128289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18904 p hg
    simpa only [d128289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18906 (p : Pattern) (guard : d128290 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128289 p = 1 := by simpa only [d128290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18905 p hg
    simpa only [d128290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18907 (p : Pattern) (guard : d128291 p = 1) : d48359 p ≤ (1 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128283 p = 1 := by simpa only [d128291, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18814 p hg
    simpa only [d128291, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128290 p = 1 := by simpa only [d128291, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18906 p hg
    simpa only [d128291, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18908 (p : Pattern) (guard : d175465 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128291 p = 1 := by simpa only [d175465, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18907 p hg
    simpa only [d175465, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175465, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17977 p hg
    simpa only [d175465, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18909 (p : Pattern) (guard : d175466 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175465 p = 1 := by simpa only [d175466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18908 p hg
    simpa only [d175466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18910 (p : Pattern) (guard : d175467 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175466 p = 1 := by simpa only [d175467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18909 p hg
    simpa only [d175467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18911 (p : Pattern) (guard : d175468 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175467 p = 1 := by simpa only [d175468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18910 p hg
    simpa only [d175468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18912 (p : Pattern) (guard : d175469 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175468 p = 1 := by simpa only [d175469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18911 p hg
    simpa only [d175469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18913 (p : Pattern) (guard : d175470 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175469 p = 1 := by simpa only [d175470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18912 p hg
    simpa only [d175470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18914 (p : Pattern) (guard : d175471 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175470 p = 1 := by simpa only [d175471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18913 p hg
    simpa only [d175471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18915 (p : Pattern) (guard : d175472 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175471 p = 1 := by simpa only [d175472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18914 p hg
    simpa only [d175472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18916 (p : Pattern) (guard : d175473 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d175464 p = 1 := by simpa only [d175473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18590 p hg
    simpa only [d175473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175472 p = 1 := by simpa only [d175473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18915 p hg
    simpa only [d175473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18917 (p : Pattern) (guard : d1099 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18918 (p : Pattern) (guard : d1100 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18917 p hg
    simpa only [d1100, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d1100, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18919 (p : Pattern) (guard : d1101 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18918 p hg
    simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18920 (p : Pattern) (guard : d1102 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d1102, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18919 p hg
    simpa only [d1102, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18921 (p : Pattern) (guard : d1103 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18920 p hg
    simpa only [d1103, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d1103, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18922 (p : Pattern) (guard : d9788 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18923 (p : Pattern) (guard : d9789 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9788 p = 1 := by simpa only [d9789, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18922 p hg
    simpa only [d9789, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9789, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9789, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18924 (p : Pattern) (guard : d9791 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9789 p = 1 := by simpa only [d9791, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18923 p hg
    simpa only [d9791, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9791, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9791, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18925 (p : Pattern) (guard : d16438 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16438, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d16438, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9791 p = 1 := by simpa only [d16438, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18924 p hg
    simpa only [d16438, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18926 (p : Pattern) (guard : d16439 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18925 p hg
    simpa only [d16439, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d16439, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18927 (p : Pattern) (guard : d16440 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18921 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18926 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18928 (p : Pattern) (guard : d9777 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18929 (p : Pattern) (guard : d9778 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9777 p = 1 := by simpa only [d9778, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18928 p hg
    simpa only [d9778, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9778, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9778, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18930 (p : Pattern) (guard : d9780 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9778 p = 1 := by simpa only [d9780, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18929 p hg
    simpa only [d9780, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9780, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9780, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18931 (p : Pattern) (guard : d14758 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14758, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d14758, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9780 p = 1 := by simpa only [d14758, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18930 p hg
    simpa only [d14758, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18932 (p : Pattern) (guard : d14759 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18931 p hg
    simpa only [d14759, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d14759, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18933 (p : Pattern) (guard : d9799 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18934 (p : Pattern) (guard : d9800 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9799 p = 1 := by simpa only [d9800, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18933 p hg
    simpa only [d9800, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9800, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9800, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18935 (p : Pattern) (guard : d9802 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9800 p = 1 := by simpa only [d9802, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18934 p hg
    simpa only [d9802, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9802, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9802, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18936 (p : Pattern) (guard : d14763 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14763, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d14763, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9802 p = 1 := by simpa only [d14763, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18935 p hg
    simpa only [d14763, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18937 (p : Pattern) (guard : d14764 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18936 p hg
    simpa only [d14764, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d14764, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18938 (p : Pattern) (guard : d16441 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18932 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18937 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18939 (p : Pattern) (guard : d16442 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18927 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18938 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18940 (p : Pattern) (guard : d1109 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18941 (p : Pattern) (guard : d1110 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18940 p hg
    simpa only [d1110, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d1110, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18942 (p : Pattern) (guard : d1111 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18941 p hg
    simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18943 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d1112, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18942 p hg
    simpa only [d1112, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18944 (p : Pattern) (guard : d1113 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18943 p hg
    simpa only [d1113, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d1113, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18945 (p : Pattern) (guard : d1120 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18946 (p : Pattern) (guard : d1121 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18945 p hg
    simpa only [d1121, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d1121, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18947 (p : Pattern) (guard : d1122 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18946 p hg
    simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18948 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d1123, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18947 p hg
    simpa only [d1123, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18949 (p : Pattern) (guard : d1124 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18948 p hg
    simpa only [d1124, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d1124, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18950 (p : Pattern) (guard : d1125 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18944 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18949 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18951 (p : Pattern) (guard : d14765 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18937 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18952 (p : Pattern) (guard : d16443 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18950 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18951 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18953 (p : Pattern) (guard : d16444 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18939 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18952 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18954 (p : Pattern) (guard : d16445 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16445, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18953 p hg
    simpa only [d16445, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18955 (p : Pattern) (guard : d16446 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16446, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18954 p hg
    simpa only [d16446, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18956 (p : Pattern) (guard : d5017 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18957 (p : Pattern) (guard : d5018 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18956 p hg
    simpa only [d5018, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d5018, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18958 (p : Pattern) (guard : d5019 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18957 p hg
    simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18959 (p : Pattern) (guard : d5020 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d5020, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18958 p hg
    simpa only [d5020, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18960 (p : Pattern) (guard : d5021 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18959 p hg
    simpa only [d5021, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d5021, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18961 (p : Pattern) (guard : d5022 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18960 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18962 (p : Pattern) (guard : d9843 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18963 (p : Pattern) (guard : d9844 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9843 p = 1 := by simpa only [d9844, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18962 p hg
    simpa only [d9844, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9844, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9844, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18964 (p : Pattern) (guard : d9846 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9844 p = 1 := by simpa only [d9846, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18963 p hg
    simpa only [d9846, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9846, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9846, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18965 (p : Pattern) (guard : d14770 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14770, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d14770, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9846 p = 1 := by simpa only [d14770, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18964 p hg
    simpa only [d14770, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18966 (p : Pattern) (guard : d14771 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18965 p hg
    simpa only [d14771, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d14771, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18967 (p : Pattern) (guard : d14772 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18966 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18968 (p : Pattern) (guard : d14773 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18961 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18967 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18969 (p : Pattern) (guard : d16447 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18952 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18968 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18970 (p : Pattern) (guard : d16448 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16448, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18969 p hg
    simpa only [d16448, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18971 (p : Pattern) (guard : d16449 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16449, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18970 p hg
    simpa only [d16449, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18972 (p : Pattern) (guard : d16450 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18955 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18971 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18973 (p : Pattern) (guard : d1127 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18949 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18974 (p : Pattern) (guard : d14778 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18973 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18967 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18975 (p : Pattern) (guard : d16451 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18952 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18974 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18976 (p : Pattern) (guard : d16452 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16452, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18975 p hg
    simpa only [d16452, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18977 (p : Pattern) (guard : d16453 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16453, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18976 p hg
    simpa only [d16453, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18978 (p : Pattern) (guard : d16454 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18977 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18979 (p : Pattern) (guard : d16455 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18972 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18978 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18980 (p : Pattern) (guard : d16456 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18979 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18981 (p : Pattern) (guard : d16457 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18980 p hg
    simpa only [d16457, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16457, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18982 (p : Pattern) (guard : d16458 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16458, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18981 p hg
    simpa only [d16458, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18983 (p : Pattern) (guard : d16459 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18978 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18984 (p : Pattern) (guard : d16460 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18983 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18985 (p : Pattern) (guard : d16461 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18984 p hg
    simpa only [d16461, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16461, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18986 (p : Pattern) (guard : d16462 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16462, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18985 p hg
    simpa only [d16462, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18987 (p : Pattern) (guard : d16463 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18982 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18986 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18988 (p : Pattern) (guard : d16464 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18987 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18989 (p : Pattern) (guard : d16465 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18988 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18990 (p : Pattern) (guard : d16466 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16465 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18989 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18991 (p : Pattern) (guard : d16467 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18986 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18992 (p : Pattern) (guard : d16468 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18991 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18993 (p : Pattern) (guard : d16469 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18992 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18994 (p : Pattern) (guard : d16470 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16469 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18993 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18995 (p : Pattern) (guard : d16471 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16466 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18990 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18994 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18996 (p : Pattern) (guard : d16472 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16471 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18995 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18997 (p : Pattern) (guard : d16473 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16472 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18996 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18998 (p : Pattern) (guard : d16474 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16473 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18997 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18999 (p : Pattern) (guard : d16475 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16474 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18998 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
