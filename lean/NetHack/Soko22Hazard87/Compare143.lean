import NetHack.Soko22Hazard87.Compare142
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35750 (p : Pattern) (guard : d316394 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316393 p = 1 := by simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35749 p hg
    simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316318 p = 1 := by simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35614 p hg
    simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35751 (p : Pattern) (guard : d316395 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316394 p = 1 := by simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35750 p hg
    simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35752 (p : Pattern) (guard : d316396 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316395 p = 1 := by simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35751 p hg
    simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35753 (p : Pattern) (guard : d316397 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316396 p = 1 := by simpa only [d316397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35752 p hg
    simpa only [d316397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35754 (p : Pattern) (guard : d316398 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316397 p = 1 := by simpa only [d316398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35753 p hg
    simpa only [d316398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316322 p = 1 := by simpa only [d316398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35622 p hg
    simpa only [d316398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35755 (p : Pattern) (guard : d316399 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316398 p = 1 := by simpa only [d316399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35754 p hg
    simpa only [d316399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35756 (p : Pattern) (guard : d316400 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316318 p = 1 := by simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35614 p hg
    simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35757 (p : Pattern) (guard : d316401 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316400 p = 1 := by simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35756 p hg
    simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35758 (p : Pattern) (guard : d316402 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316401 p = 1 := by simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35757 p hg
    simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35759 (p : Pattern) (guard : d316403 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316402 p = 1 := by simpa only [d316403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35758 p hg
    simpa only [d316403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35760 (p : Pattern) (guard : d316404 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316403 p = 1 := by simpa only [d316404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35759 p hg
    simpa only [d316404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35761 (p : Pattern) (guard : d316405 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316404 p = 1 := by simpa only [d316405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35760 p hg
    simpa only [d316405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35762 (p : Pattern) (guard : d316406 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316399 p = 1 := by simpa only [d316406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35755 p hg
    simpa only [d316406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316405 p = 1 := by simpa only [d316406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35761 p hg
    simpa only [d316406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35763 (p : Pattern) (guard : d316407 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d316352 p = 1 := by simpa only [d316407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35742 p hg
    simpa only [d316407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316406 p = 1 := by simpa only [d316407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35762 p hg
    simpa only [d316407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35764 (p : Pattern) (guard : d316408 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d316346 p = 1 := by simpa only [d316408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35733 p hg
    simpa only [d316408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316407 p = 1 := by simpa only [d316408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35763 p hg
    simpa only [d316408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35765 (p : Pattern) (guard : d316410 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316341 p = 1 := by simpa only [d316410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35643 p hg
    simpa only [d316410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35766 (p : Pattern) (guard : d286214 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286143 p = 1 := by simpa only [d286214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35645 p hg
    simpa only [d286214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35767 (p : Pattern) (guard : d316411 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316410 p = 1 := by simpa only [d316411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35765 p hg
    simpa only [d316411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286214 p = 1 := by simpa only [d316411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35766 p hg
    simpa only [d316411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35768 (p : Pattern) (guard : d316412 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316411 p = 1 := by simpa only [d316412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d316412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35769 (p : Pattern) (guard : d316413 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316412 p = 1 := by simpa only [d316413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35768 p hg
    simpa only [d316413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35770 (p : Pattern) (guard : d316414 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316413 p = 1 := by simpa only [d316414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35769 p hg
    simpa only [d316414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35771 (p : Pattern) (guard : d316415 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316348 p = 1 := by simpa only [d316415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35652 p hg
    simpa only [d316415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35772 (p : Pattern) (guard : d286220 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286153 p = 1 := by simpa only [d286220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35655 p hg
    simpa only [d286220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35773 (p : Pattern) (guard : d316416 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316415 p = 1 := by simpa only [d316416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35771 p hg
    simpa only [d316416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286220 p = 1 := by simpa only [d316416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35772 p hg
    simpa only [d316416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35774 (p : Pattern) (guard : d316417 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316416 p = 1 := by simpa only [d316417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35773 p hg
    simpa only [d316417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35775 (p : Pattern) (guard : d316418 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316417 p = 1 := by simpa only [d316418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35774 p hg
    simpa only [d316418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35776 (p : Pattern) (guard : d316419 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316396 p = 1 := by simpa only [d316419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35712 p hg
    simpa only [d316419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35777 (p : Pattern) (guard : d316420 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316419 p = 1 := by simpa only [d316420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35776 p hg
    simpa only [d316420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316331 p = 1 := by simpa only [d316420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35632 p hg
    simpa only [d316420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35778 (p : Pattern) (guard : d316421 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316420 p = 1 := by simpa only [d316421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35777 p hg
    simpa only [d316421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35779 (p : Pattern) (guard : d316422 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316402 p = 1 := by simpa only [d316422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35718 p hg
    simpa only [d316422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35780 (p : Pattern) (guard : d316423 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316422 p = 1 := by simpa only [d316423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35779 p hg
    simpa only [d316423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35781 (p : Pattern) (guard : d316424 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316423 p = 1 := by simpa only [d316424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35780 p hg
    simpa only [d316424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35782 (p : Pattern) (guard : d316425 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316421 p = 1 := by simpa only [d316425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35778 p hg
    simpa only [d316425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316424 p = 1 := by simpa only [d316425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35781 p hg
    simpa only [d316425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35783 (p : Pattern) (guard : d316426 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d316418 p = 1 := by simpa only [d316426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35775 p hg
    simpa only [d316426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316425 p = 1 := by simpa only [d316426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35782 p hg
    simpa only [d316426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35784 (p : Pattern) (guard : d316427 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d316414 p = 1 := by simpa only [d316427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35770 p hg
    simpa only [d316427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316426 p = 1 := by simpa only [d316427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35783 p hg
    simpa only [d316427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35785 (p : Pattern) (guard : d316428 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d316408 p = 1 := by simpa only [d316428, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d316428, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316427 p = 1 := by simpa only [d316428, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35784 p hg
    simpa only [d316428, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35786 (p : Pattern) (guard : d316429 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d316409 p = 1 := by simpa only [d316429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35725 p hg
    simpa only [d316429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316428 p = 1 := by simpa only [d316429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35785 p hg
    simpa only [d316429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35787 (p : Pattern) (guard : d286235 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286121 p = 1 := by simpa only [d286235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35601 p hg
    simpa only [d286235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35788 (p : Pattern) (guard : d286236 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286235 p = 1 := by simpa only [d286236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35787 p hg
    simpa only [d286236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35789 (p : Pattern) (guard : d286237 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d286236 p = 1 := by simpa only [d286237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35788 p hg
    simpa only [d286237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35790 (p : Pattern) (guard : d286238 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286237 p = 1 := by simpa only [d286238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35789 p hg
    simpa only [d286238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35791 (p : Pattern) (guard : d286239 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286238 p = 1 := by simpa only [d286239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35790 p hg
    simpa only [d286239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35792 (p : Pattern) (guard : d316430 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d316327 p = 1 := by simpa only [d316430, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35631 p hg
    simpa only [d316430, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286239 p = 1 := by simpa only [d316430, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35791 p hg
    simpa only [d316430, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35793 (p : Pattern) (guard : d286235 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286121 p = 1 := by simpa only [d286235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35626 p hg
    simpa only [d286235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35794 (p : Pattern) (guard : d286236 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286235 p = 1 := by simpa only [d286236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35793 p hg
    simpa only [d286236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35795 (p : Pattern) (guard : d286237 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d286236 p = 1 := by simpa only [d286237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35794 p hg
    simpa only [d286237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35796 (p : Pattern) (guard : d286238 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286237 p = 1 := by simpa only [d286238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35795 p hg
    simpa only [d286238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35797 (p : Pattern) (guard : d286239 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286238 p = 1 := by simpa only [d286239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35796 p hg
    simpa only [d286239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35798 (p : Pattern) (guard : d286241 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286131 p = 1 := by simpa only [d286241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35633 p hg
    simpa only [d286241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35799 (p : Pattern) (guard : d286242 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286241 p = 1 := by simpa only [d286242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35798 p hg
    simpa only [d286242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35800 (p : Pattern) (guard : d286243 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d286242 p = 1 := by simpa only [d286243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35799 p hg
    simpa only [d286243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35801 (p : Pattern) (guard : d286244 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286243 p = 1 := by simpa only [d286244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35800 p hg
    simpa only [d286244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35802 (p : Pattern) (guard : d286245 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286244 p = 1 := by simpa only [d286245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35801 p hg
    simpa only [d286245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35803 (p : Pattern) (guard : d286246 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d286239 p = 1 := by simpa only [d286246, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35797 p hg
    simpa only [d286246, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286245 p = 1 := by simpa only [d286246, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35802 p hg
    simpa only [d286246, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35804 (p : Pattern) (guard : d316431 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d316430 p = 1 := by simpa only [d316431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35792 p hg
    simpa only [d316431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286246 p = 1 := by simpa only [d316431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35803 p hg
    simpa only [d316431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35805 (p : Pattern) (guard : d316432 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d316429 p = 1 := by simpa only [d316432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35786 p hg
    simpa only [d316432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316431 p = 1 := by simpa only [d316432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35804 p hg
    simpa only [d316432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35806 (p : Pattern) (guard : d316433 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d316432 p = 1 := by simpa only [d316433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35805 p hg
    simpa only [d316433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d316433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35807 (p : Pattern) (guard : d316434 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d316340 p = 1 := by simpa only [d316434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35642 p hg
    simpa only [d316434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316433 p = 1 := by simpa only [d316434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35806 p hg
    simpa only [d316434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35808 (p : Pattern) (guard : d316353 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286613 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35429 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35809 (p : Pattern) (guard : d825 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare35810 (p : Pattern) (guard : d5121 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35809 p hg
    simpa only [d5121, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d5121, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35811 (p : Pattern) (guard : d34352 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5121 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35810 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35812 (p : Pattern) (guard : d34353 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d34352 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35811 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35813 (p : Pattern) (guard : d34354 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d34353 p = 1 := by simpa only [d34354, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35812 p hg
    simpa only [d34354, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34354, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d34354, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35814 (p : Pattern) (guard : d316354 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35813 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316230 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35435 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35815 (p : Pattern) (guard : d316355 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316353 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35808 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316354 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35814 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35816 (p : Pattern) (guard : d316356 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316355 p = 1 := by simpa only [d316356, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35815 p hg
    simpa only [d316356, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316356, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d316356, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35817 (p : Pattern) (guard : d316357 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35816 p hg
    simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316233 p = 1 := by simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35438 p hg
    simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35818 (p : Pattern) (guard : d316358 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316357 p = 1 := by simpa only [d316358, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35817 p hg
    simpa only [d316358, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316358, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316358, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35819 (p : Pattern) (guard : d316359 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316358 p = 1 := by simpa only [d316359, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35818 p hg
    simpa only [d316359, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316359, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316359, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35820 (p : Pattern) (guard : d316360 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316360, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316360, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316359 p = 1 := by simpa only [d316360, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35819 p hg
    simpa only [d316360, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35821 (p : Pattern) (guard : d316361 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316360 p = 1 := by simpa only [d316361, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35820 p hg
    simpa only [d316361, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316361, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316361, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35822 (p : Pattern) (guard : d1540 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare35823 (p : Pattern) (guard : d1541 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35822 p hg
    simpa only [d1541, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d1541, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35824 (p : Pattern) (guard : d258089 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35823 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35825 (p : Pattern) (guard : d316362 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258089 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35824 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35826 (p : Pattern) (guard : d316363 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316362 p = 1 := by simpa only [d316363, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35825 p hg
    simpa only [d316363, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316363, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d316363, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35827 (p : Pattern) (guard : d316364 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316363 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35826 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34955 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35828 (p : Pattern) (guard : d316365 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316364 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35827 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35829 (p : Pattern) (guard : d316366 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316365 p = 1 := by simpa only [d316366, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35828 p hg
    simpa only [d316366, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316366, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d316366, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35830 (p : Pattern) (guard : d316367 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35438 p hg
    simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35829 p hg
    simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35831 (p : Pattern) (guard : d316368 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316367 p = 1 := by simpa only [d316368, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35830 p hg
    simpa only [d316368, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316368, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316368, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35832 (p : Pattern) (guard : d316369 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316368 p = 1 := by simpa only [d316369, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35831 p hg
    simpa only [d316369, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316369, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316369, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35833 (p : Pattern) (guard : d316370 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316370, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316370, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316369 p = 1 := by simpa only [d316370, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35832 p hg
    simpa only [d316370, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35834 (p : Pattern) (guard : d316371 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316370 p = 1 := by simpa only [d316371, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35833 p hg
    simpa only [d316371, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316371, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316371, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35835 (p : Pattern) (guard : d316372 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316361 p = 1 := by simpa only [d316372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35821 p hg
    simpa only [d316372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316371 p = 1 := by simpa only [d316372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35834 p hg
    simpa only [d316372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35836 (p : Pattern) (guard : d316373 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35429 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35826 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35837 (p : Pattern) (guard : d316374 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316373 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35836 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35838 (p : Pattern) (guard : d316375 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316374 p = 1 := by simpa only [d316375, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35837 p hg
    simpa only [d316375, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316375, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d316375, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35839 (p : Pattern) (guard : d316376 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316375 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35838 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35829 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35840 (p : Pattern) (guard : d316377 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316376 p = 1 := by simpa only [d316377, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35839 p hg
    simpa only [d316377, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316377, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316377, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35841 (p : Pattern) (guard : d316378 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316377 p = 1 := by simpa only [d316378, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35840 p hg
    simpa only [d316378, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316378, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316378, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35842 (p : Pattern) (guard : d316379 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316379, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316379, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316378 p = 1 := by simpa only [d316379, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35841 p hg
    simpa only [d316379, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35843 (p : Pattern) (guard : d316380 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316379 p = 1 := by simpa only [d316380, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35842 p hg
    simpa only [d316380, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316380, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316380, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35844 (p : Pattern) (guard : d316381 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316380 p = 1 := by simpa only [d316381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35843 p hg
    simpa only [d316381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285997 p = 1 := by simpa only [d316381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35451 p hg
    simpa only [d316381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35845 (p : Pattern) (guard : d316382 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316372 p = 1 := by simpa only [d316382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35835 p hg
    simpa only [d316382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316381 p = 1 := by simpa only [d316382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35844 p hg
    simpa only [d316382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35846 (p : Pattern) (guard : d316383 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316382 p = 1 := by simpa only [d316383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35845 p hg
    simpa only [d316383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316240 p = 1 := by simpa only [d316383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35453 p hg
    simpa only [d316383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35847 (p : Pattern) (guard : d316384 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316384, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d316384, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316383 p = 1 := by simpa only [d316384, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35846 p hg
    simpa only [d316384, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35848 (p : Pattern) (guard : d316385 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316385, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d316385, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316384 p = 1 := by simpa only [d316385, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35847 p hg
    simpa only [d316385, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35849 (p : Pattern) (guard : d286188 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d285998 p = 1 := by simpa only [d286188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35452 p hg
    simpa only [d286188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257193 p = 1 := by simpa only [d286188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34971 p hg
    simpa only [d286188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35850 (p : Pattern) (guard : d316386 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316240 p = 1 := by simpa only [d316386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35453 p hg
    simpa only [d316386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286188 p = 1 := by simpa only [d316386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35849 p hg
    simpa only [d316386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35851 (p : Pattern) (guard : d316387 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316387, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d316387, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316386 p = 1 := by simpa only [d316387, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35850 p hg
    simpa only [d316387, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35852 (p : Pattern) (guard : d316388 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316388, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d316388, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316387 p = 1 := by simpa only [d316388, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35851 p hg
    simpa only [d316388, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35853 (p : Pattern) (guard : d316389 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316385 p = 1 := by simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35848 p hg
    simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316388 p = 1 := by simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35852 p hg
    simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35854 (p : Pattern) (guard : d316390 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316389 p = 1 := by simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35853 p hg
    simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316244 p = 1 := by simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35457 p hg
    simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35855 (p : Pattern) (guard : d316391 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316390 p = 1 := by simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35854 p hg
    simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35856 (p : Pattern) (guard : d316392 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316391 p = 1 := by simpa only [d316392, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35855 p hg
    simpa only [d316392, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316392, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d316392, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35857 (p : Pattern) (guard : d316393 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316393, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d316393, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316392 p = 1 := by simpa only [d316393, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35856 p hg
    simpa only [d316393, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35858 (p : Pattern) (guard : d286105 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35205 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35859 (p : Pattern) (guard : d316315 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316244 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35457 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286105 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35858 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35860 (p : Pattern) (guard : d316316 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316315 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35859 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35861 (p : Pattern) (guard : d316317 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316316 p = 1 := by simpa only [d316317, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35860 p hg
    simpa only [d316317, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316317, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d316317, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35862 (p : Pattern) (guard : d316318 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316318, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d316318, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316317 p = 1 := by simpa only [d316318, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35861 p hg
    simpa only [d316318, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35863 (p : Pattern) (guard : d316394 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316393 p = 1 := by simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35857 p hg
    simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316318 p = 1 := by simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35862 p hg
    simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35864 (p : Pattern) (guard : d316395 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316394 p = 1 := by simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35863 p hg
    simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35865 (p : Pattern) (guard : d316396 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316395 p = 1 := by simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35864 p hg
    simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35866 (p : Pattern) (guard : d316419 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316396 p = 1 := by simpa only [d316419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35865 p hg
    simpa only [d316419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35867 (p : Pattern) (guard : d286110 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d286105 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35858 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35868 (p : Pattern) (guard : d286111 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d286110 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35867 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35869 (p : Pattern) (guard : d286112 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d286111 p = 1 := by simpa only [d286112, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35868 p hg
    simpa only [d286112, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286112, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d286112, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35870 (p : Pattern) (guard : d286113 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286113, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d286113, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286112 p = 1 := by simpa only [d286113, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35869 p hg
    simpa only [d286113, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35871 (p : Pattern) (guard : d316319 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316318 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35862 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286113 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35870 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35872 (p : Pattern) (guard : d316320 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316319 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35871 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35873 (p : Pattern) (guard : d316321 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316320 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35872 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35874 (p : Pattern) (guard : d316331 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316321 p = 1 := by simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35873 p hg
    simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35875 (p : Pattern) (guard : d316420 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316419 p = 1 := by simpa only [d316420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35866 p hg
    simpa only [d316420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316331 p = 1 := by simpa only [d316420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d316420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35876 (p : Pattern) (guard : d316421 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316420 p = 1 := by simpa only [d316421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35875 p hg
    simpa only [d316421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35877 (p : Pattern) (guard : d316400 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316318 p = 1 := by simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35862 p hg
    simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35878 (p : Pattern) (guard : d316401 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316400 p = 1 := by simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35877 p hg
    simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35879 (p : Pattern) (guard : d316402 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316401 p = 1 := by simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35878 p hg
    simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35880 (p : Pattern) (guard : d316422 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316402 p = 1 := by simpa only [d316422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35879 p hg
    simpa only [d316422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35881 (p : Pattern) (guard : d316423 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316422 p = 1 := by simpa only [d316423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35880 p hg
    simpa only [d316423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35882 (p : Pattern) (guard : d316424 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316423 p = 1 := by simpa only [d316424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35881 p hg
    simpa only [d316424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35883 (p : Pattern) (guard : d316425 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316421 p = 1 := by simpa only [d316425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35876 p hg
    simpa only [d316425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316424 p = 1 := by simpa only [d316425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35882 p hg
    simpa only [d316425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35884 (p : Pattern) (guard : d316435 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316425 p = 1 := by simpa only [d316435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35883 p hg
    simpa only [d316435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35885 (p : Pattern) (guard : d316436 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d316436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316435 p = 1 := by simpa only [d316436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35884 p hg
    simpa only [d316436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35886 (p : Pattern) (guard : d316437 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316437, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316437, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316436 p = 1 := by simpa only [d316437, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35885 p hg
    simpa only [d316437, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35887 (p : Pattern) (guard : d316438 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d316438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316437 p = 1 := by simpa only [d316438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35886 p hg
    simpa only [d316438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35888 (p : Pattern) (guard : d286118 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d286113 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35870 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35889 (p : Pattern) (guard : d286119 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286118 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35888 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35890 (p : Pattern) (guard : d286120 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286119 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35889 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35891 (p : Pattern) (guard : d286131 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286120 p = 1 := by simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35892 (p : Pattern) (guard : d286241 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286131 p = 1 := by simpa only [d286241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35891 p hg
    simpa only [d286241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35893 (p : Pattern) (guard : d286242 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286241 p = 1 := by simpa only [d286242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35892 p hg
    simpa only [d286242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35894 (p : Pattern) (guard : d286243 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d286242 p = 1 := by simpa only [d286243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35893 p hg
    simpa only [d286243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35895 (p : Pattern) (guard : d286244 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286243 p = 1 := by simpa only [d286244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35894 p hg
    simpa only [d286244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35896 (p : Pattern) (guard : d286245 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d286245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286244 p = 1 := by simpa only [d286245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35895 p hg
    simpa only [d286245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35897 (p : Pattern) (guard : d286255 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286255, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286255, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286245 p = 1 := by simpa only [d286255, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35896 p hg
    simpa only [d286255, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35898 (p : Pattern) (guard : d286256 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d286256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286255 p = 1 := by simpa only [d286256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35897 p hg
    simpa only [d286256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35899 (p : Pattern) (guard : d316439 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d316438 p = 1 := by simpa only [d316439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35887 p hg
    simpa only [d316439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286256 p = 1 := by simpa only [d316439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35898 p hg
    simpa only [d316439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35900 (p : Pattern) (guard : d316440 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d316439 p = 1 := by simpa only [d316440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35899 p hg
    simpa only [d316440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d316440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35901 (p : Pattern) (guard : d316441 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d316440 p = 1 := by simpa only [d316441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35900 p hg
    simpa only [d316441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d316441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35902 (p : Pattern) (guard : d316442 p = 1) : d50390 p ≤ (3 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d316434 p = 1 := by simpa only [d316442, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35807 p hg
    simpa only [d316442, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316441 p = 1 := by simpa only [d316442, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35901 p hg
    simpa only [d316442, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35903 (p : Pattern) (guard : d316353 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286613 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35493 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35904 (p : Pattern) (guard : d825 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare35905 (p : Pattern) (guard : d5121 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35904 p hg
    simpa only [d5121, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d5121, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35906 (p : Pattern) (guard : d34352 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5121 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35905 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35907 (p : Pattern) (guard : d34353 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d34352 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35906 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35908 (p : Pattern) (guard : d34354 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d34353 p = 1 := by simpa only [d34354, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35907 p hg
    simpa only [d34354, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34354, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d34354, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35909 (p : Pattern) (guard : d316354 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35908 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316230 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35499 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35910 (p : Pattern) (guard : d316355 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316353 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35903 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316354 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35909 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35911 (p : Pattern) (guard : d316356 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316355 p = 1 := by simpa only [d316356, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35910 p hg
    simpa only [d316356, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316356, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d316356, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35912 (p : Pattern) (guard : d316357 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35911 p hg
    simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316233 p = 1 := by simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35502 p hg
    simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35913 (p : Pattern) (guard : d316443 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316357 p = 1 := by simpa only [d316443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35912 p hg
    simpa only [d316443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35914 (p : Pattern) (guard : d316358 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316357 p = 1 := by simpa only [d316358, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35669 p hg
    simpa only [d316358, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316358, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316358, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35915 (p : Pattern) (guard : d316444 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316443 p = 1 := by simpa only [d316444, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35913 p hg
    simpa only [d316444, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316358 p = 1 := by simpa only [d316444, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d316444, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35916 (p : Pattern) (guard : d316353 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286613 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35511 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35917 (p : Pattern) (guard : d825 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare35918 (p : Pattern) (guard : d5121 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35917 p hg
    simpa only [d5121, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d5121, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35919 (p : Pattern) (guard : d34352 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5121 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35918 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35920 (p : Pattern) (guard : d34353 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d34352 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35919 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35921 (p : Pattern) (guard : d34354 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d34353 p = 1 := by simpa only [d34354, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35920 p hg
    simpa only [d34354, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34354, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d34354, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35922 (p : Pattern) (guard : d316354 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35921 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316230 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35517 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35923 (p : Pattern) (guard : d316355 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316353 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35916 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316354 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35922 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35924 (p : Pattern) (guard : d316356 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316355 p = 1 := by simpa only [d316356, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35923 p hg
    simpa only [d316356, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316356, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d316356, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35925 (p : Pattern) (guard : d316357 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35924 p hg
    simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316233 p = 1 := by simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35520 p hg
    simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35926 (p : Pattern) (guard : d316358 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316357 p = 1 := by simpa only [d316358, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35925 p hg
    simpa only [d316358, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316358, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316358, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35927 (p : Pattern) (guard : d316359 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316358 p = 1 := by simpa only [d316359, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35926 p hg
    simpa only [d316359, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316359, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316359, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35928 (p : Pattern) (guard : d316445 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316444 p = 1 := by simpa only [d316445, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35915 p hg
    simpa only [d316445, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316359 p = 1 := by simpa only [d316445, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35927 p hg
    simpa only [d316445, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35929 (p : Pattern) (guard : d316446 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316445 p = 1 := by simpa only [d316446, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35928 p hg
    simpa only [d316446, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316446, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316446, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35930 (p : Pattern) (guard : d1540 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare35931 (p : Pattern) (guard : d1541 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35930 p hg
    simpa only [d1541, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d1541, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35932 (p : Pattern) (guard : d258089 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35931 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35933 (p : Pattern) (guard : d316362 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258089 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35932 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35934 (p : Pattern) (guard : d316363 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316362 p = 1 := by simpa only [d316363, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35933 p hg
    simpa only [d316363, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316363, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d316363, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35935 (p : Pattern) (guard : d316364 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316363 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35934 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35936 (p : Pattern) (guard : d316365 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316364 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35935 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35937 (p : Pattern) (guard : d316366 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316365 p = 1 := by simpa only [d316366, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35936 p hg
    simpa only [d316366, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316366, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d316366, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35938 (p : Pattern) (guard : d316367 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35502 p hg
    simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35937 p hg
    simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35939 (p : Pattern) (guard : d316447 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316367 p = 1 := by simpa only [d316447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35938 p hg
    simpa only [d316447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35940 (p : Pattern) (guard : d316368 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316367 p = 1 := by simpa only [d316368, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35682 p hg
    simpa only [d316368, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316368, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316368, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35941 (p : Pattern) (guard : d316448 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316447 p = 1 := by simpa only [d316448, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35939 p hg
    simpa only [d316448, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316368 p = 1 := by simpa only [d316448, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35940 p hg
    simpa only [d316448, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35942 (p : Pattern) (guard : d1540 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare35943 (p : Pattern) (guard : d1541 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35942 p hg
    simpa only [d1541, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d1541, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35944 (p : Pattern) (guard : d258089 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35943 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35945 (p : Pattern) (guard : d316362 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258089 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35944 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35946 (p : Pattern) (guard : d316363 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316362 p = 1 := by simpa only [d316363, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35945 p hg
    simpa only [d316363, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316363, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d316363, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35947 (p : Pattern) (guard : d316364 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316363 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35946 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35027 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35948 (p : Pattern) (guard : d316365 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316364 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35947 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35949 (p : Pattern) (guard : d316366 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316365 p = 1 := by simpa only [d316366, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35948 p hg
    simpa only [d316366, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316366, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d316366, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35950 (p : Pattern) (guard : d316367 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35520 p hg
    simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35949 p hg
    simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35951 (p : Pattern) (guard : d316368 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316367 p = 1 := by simpa only [d316368, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35950 p hg
    simpa only [d316368, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316368, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316368, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35952 (p : Pattern) (guard : d316369 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316368 p = 1 := by simpa only [d316369, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35951 p hg
    simpa only [d316369, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316369, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316369, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35953 (p : Pattern) (guard : d316449 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316448 p = 1 := by simpa only [d316449, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35941 p hg
    simpa only [d316449, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316369 p = 1 := by simpa only [d316449, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35952 p hg
    simpa only [d316449, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35954 (p : Pattern) (guard : d316450 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316449 p = 1 := by simpa only [d316450, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35953 p hg
    simpa only [d316450, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316450, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316450, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35955 (p : Pattern) (guard : d316451 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316446 p = 1 := by simpa only [d316451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35929 p hg
    simpa only [d316451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316450 p = 1 := by simpa only [d316451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35954 p hg
    simpa only [d316451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35956 (p : Pattern) (guard : d316373 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35493 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35934 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35957 (p : Pattern) (guard : d316374 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316373 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35956 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35958 (p : Pattern) (guard : d316375 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316374 p = 1 := by simpa only [d316375, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35957 p hg
    simpa only [d316375, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316375, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d316375, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35959 (p : Pattern) (guard : d316376 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316375 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35958 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35937 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35960 (p : Pattern) (guard : d316452 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316376 p = 1 := by simpa only [d316452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35959 p hg
    simpa only [d316452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35961 (p : Pattern) (guard : d316377 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316376 p = 1 := by simpa only [d316377, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35691 p hg
    simpa only [d316377, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316377, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316377, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35962 (p : Pattern) (guard : d316453 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316452 p = 1 := by simpa only [d316453, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35960 p hg
    simpa only [d316453, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316377 p = 1 := by simpa only [d316453, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35961 p hg
    simpa only [d316453, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35963 (p : Pattern) (guard : d316373 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35511 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35946 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35964 (p : Pattern) (guard : d316374 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316373 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35963 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35965 (p : Pattern) (guard : d316375 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316374 p = 1 := by simpa only [d316375, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35964 p hg
    simpa only [d316375, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316375, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d316375, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35966 (p : Pattern) (guard : d316376 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316375 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35965 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35949 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35967 (p : Pattern) (guard : d316377 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316376 p = 1 := by simpa only [d316377, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35966 p hg
    simpa only [d316377, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316377, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316377, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35968 (p : Pattern) (guard : d316378 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316377 p = 1 := by simpa only [d316378, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35967 p hg
    simpa only [d316378, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316378, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316378, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35969 (p : Pattern) (guard : d316454 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316453 p = 1 := by simpa only [d316454, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35962 p hg
    simpa only [d316454, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316378 p = 1 := by simpa only [d316454, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35968 p hg
    simpa only [d316454, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35970 (p : Pattern) (guard : d316455 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316454 p = 1 := by simpa only [d316455, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35969 p hg
    simpa only [d316455, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316455, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316455, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35971 (p : Pattern) (guard : d316456 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316455 p = 1 := by simpa only [d316456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35970 p hg
    simpa only [d316456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286065 p = 1 := by simpa only [d316456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35539 p hg
    simpa only [d316456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35972 (p : Pattern) (guard : d316457 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316451 p = 1 := by simpa only [d316457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35955 p hg
    simpa only [d316457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316456 p = 1 := by simpa only [d316457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35971 p hg
    simpa only [d316457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35973 (p : Pattern) (guard : d316458 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316457 p = 1 := by simpa only [d316458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35972 p hg
    simpa only [d316458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316283 p = 1 := by simpa only [d316458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35541 p hg
    simpa only [d316458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35974 (p : Pattern) (guard : d316459 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316459, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d316459, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316458 p = 1 := by simpa only [d316459, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35973 p hg
    simpa only [d316459, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35975 (p : Pattern) (guard : d316460 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316460, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d316460, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316459 p = 1 := by simpa only [d316460, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35974 p hg
    simpa only [d316460, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35976 (p : Pattern) (guard : d286279 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d286066 p = 1 := by simpa only [d286279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35540 p hg
    simpa only [d286279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257234 p = 1 := by simpa only [d286279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35041 p hg
    simpa only [d286279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35977 (p : Pattern) (guard : d316461 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316283 p = 1 := by simpa only [d316461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35541 p hg
    simpa only [d316461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286279 p = 1 := by simpa only [d316461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35976 p hg
    simpa only [d316461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35978 (p : Pattern) (guard : d316462 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316462, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d316462, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316461 p = 1 := by simpa only [d316462, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35977 p hg
    simpa only [d316462, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35979 (p : Pattern) (guard : d316463 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316463, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d316463, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316462 p = 1 := by simpa only [d316463, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35978 p hg
    simpa only [d316463, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35980 (p : Pattern) (guard : d316464 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316460 p = 1 := by simpa only [d316464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35975 p hg
    simpa only [d316464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316463 p = 1 := by simpa only [d316464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35979 p hg
    simpa only [d316464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35981 (p : Pattern) (guard : d316465 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316464 p = 1 := by simpa only [d316465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35980 p hg
    simpa only [d316465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316287 p = 1 := by simpa only [d316465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d316465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35982 (p : Pattern) (guard : d316466 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316465 p = 1 := by simpa only [d316466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35981 p hg
    simpa only [d316466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d316466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35983 (p : Pattern) (guard : d316467 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316466 p = 1 := by simpa only [d316467, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35982 p hg
    simpa only [d316467, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316467, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d316467, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35984 (p : Pattern) (guard : d316468 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316468, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d316468, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316467 p = 1 := by simpa only [d316468, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35983 p hg
    simpa only [d316468, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35985 (p : Pattern) (guard : d286288 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285923 p = 1 := by simpa only [d286288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35255 p hg
    simpa only [d286288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d286288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35986 (p : Pattern) (guard : d316469 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316287 p = 1 := by simpa only [d316469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d316469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286288 p = 1 := by simpa only [d316469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35985 p hg
    simpa only [d316469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35987 (p : Pattern) (guard : d316470 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316469 p = 1 := by simpa only [d316470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35986 p hg
    simpa only [d316470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d316470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35988 (p : Pattern) (guard : d316471 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316470 p = 1 := by simpa only [d316471, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35987 p hg
    simpa only [d316471, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316471, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d316471, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35989 (p : Pattern) (guard : d316472 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316472, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d316472, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316471 p = 1 := by simpa only [d316472, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35988 p hg
    simpa only [d316472, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35990 (p : Pattern) (guard : d316473 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316468 p = 1 := by simpa only [d316473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35984 p hg
    simpa only [d316473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316472 p = 1 := by simpa only [d316473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d316473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35991 (p : Pattern) (guard : d316474 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316473 p = 1 := by simpa only [d316474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35990 p hg
    simpa only [d316474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35992 (p : Pattern) (guard : d316475 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316474 p = 1 := by simpa only [d316475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35991 p hg
    simpa only [d316475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35993 (p : Pattern) (guard : d316476 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316475 p = 1 := by simpa only [d316476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35992 p hg
    simpa only [d316476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35994 (p : Pattern) (guard : d286297 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d286288 p = 1 := by simpa only [d286297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35985 p hg
    simpa only [d286297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d286297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35995 (p : Pattern) (guard : d286298 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d286297 p = 1 := by simpa only [d286298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35994 p hg
    simpa only [d286298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d286298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35996 (p : Pattern) (guard : d286299 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d286298 p = 1 := by simpa only [d286299, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35995 p hg
    simpa only [d286299, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286299, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d286299, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35997 (p : Pattern) (guard : d286300 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286300, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d286300, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286299 p = 1 := by simpa only [d286300, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35996 p hg
    simpa only [d286300, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35998 (p : Pattern) (guard : d316477 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316472 p = 1 := by simpa only [d316477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d316477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286300 p = 1 := by simpa only [d316477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35997 p hg
    simpa only [d316477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35999 (p : Pattern) (guard : d316478 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316477 p = 1 := by simpa only [d316478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35998 p hg
    simpa only [d316478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316478, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
