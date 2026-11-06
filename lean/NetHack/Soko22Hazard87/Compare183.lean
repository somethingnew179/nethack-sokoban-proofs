import NetHack.Soko22Hazard87.Compare182
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45750 (p : Pattern) (guard : d367448 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367447 p = 1 := by simpa only [d367448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45749 p hg
    simpa only [d367448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45751 (p : Pattern) (guard : d367449 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367448 p = 1 := by simpa only [d367449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45750 p hg
    simpa only [d367449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45752 (p : Pattern) (guard : d367450 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367449 p = 1 := by simpa only [d367450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45751 p hg
    simpa only [d367450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45753 (p : Pattern) (guard : d367451 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367450 p = 1 := by simpa only [d367451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45752 p hg
    simpa only [d367451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45754 (p : Pattern) (guard : d367452 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367452, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367452, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367451 p = 1 := by simpa only [d367452, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45753 p hg
    simpa only [d367452, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45755 (p : Pattern) (guard : d367453 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367452 p = 1 := by simpa only [d367453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45754 p hg
    simpa only [d367453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45756 (p : Pattern) (guard : d367454 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367453 p = 1 := by simpa only [d367454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45755 p hg
    simpa only [d367454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45757 (p : Pattern) (guard : d367455 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367454 p = 1 := by simpa only [d367455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45756 p hg
    simpa only [d367455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45758 (p : Pattern) (guard : d367456 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367455 p = 1 := by simpa only [d367456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45757 p hg
    simpa only [d367456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45759 (p : Pattern) (guard : d367457 p = 1) : d51634 p ≤ (7 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367456 p = 1 := by simpa only [d367457, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45758 p hg
    simpa only [d367457, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367457, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d367457, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45760 (p : Pattern) (guard : d367458 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d367446 p = 1 := by simpa only [d367458, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45698 p hg
    simpa only [d367458, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367457 p = 1 := by simpa only [d367458, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45759 p hg
    simpa only [d367458, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45761 (p : Pattern) (guard : d367459 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367458 p = 1 := by simpa only [d367459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45760 p hg
    simpa only [d367459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45762 (p : Pattern) (guard : d367460 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367459 p = 1 := by simpa only [d367460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45761 p hg
    simpa only [d367460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45763 (p : Pattern) (guard : d367461 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367460 p = 1 := by simpa only [d367461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45762 p hg
    simpa only [d367461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45764 (p : Pattern) (guard : d367462 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367461 p = 1 := by simpa only [d367462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45763 p hg
    simpa only [d367462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45765 (p : Pattern) (guard : d367463 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367462 p = 1 := by simpa only [d367463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45764 p hg
    simpa only [d367463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45766 (p : Pattern) (guard : d367464 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367463 p = 1 := by simpa only [d367464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45765 p hg
    simpa only [d367464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45767 (p : Pattern) (guard : d367465 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367464 p = 1 := by simpa only [d367465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45766 p hg
    simpa only [d367465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45768 (p : Pattern) (guard : d367466 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d344008 p = 1 := by simpa only [d367466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45578 p hg
    simpa only [d367466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367465 p = 1 := by simpa only [d367466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45767 p hg
    simpa only [d367466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45769 (p : Pattern) (guard : d1087 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45274 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45770 (p : Pattern) (guard : d366506 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d42941 p = 1 := by simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45583 p hg
    simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45769 p hg
    simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45771 (p : Pattern) (guard : d366507 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366506 p = 1 := by simpa only [d366507, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45770 p hg
    simpa only [d366507, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366507, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d366507, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45772 (p : Pattern) (guard : d366508 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366507 p = 1 := by simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45771 p hg
    simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45773 (p : Pattern) (guard : d366347 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d42940 p = 1 := by simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45582 p hg
    simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45274 p hg
    simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45774 (p : Pattern) (guard : d366348 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d366347 p = 1 := by simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45773 p hg
    simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45775 (p : Pattern) (guard : d366349 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366348 p = 1 := by simpa only [d366349, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45774 p hg
    simpa only [d366349, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366349, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d366349, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45776 (p : Pattern) (guard : d366350 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d42943 p = 1 := by simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45585 p hg
    simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366349 p = 1 := by simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45775 p hg
    simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45777 (p : Pattern) (guard : d366509 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366508 p = 1 := by simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45772 p hg
    simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366350 p = 1 := by simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45776 p hg
    simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45778 (p : Pattern) (guard : d366510 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366509 p = 1 := by simpa only [d366510, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45777 p hg
    simpa only [d366510, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366510, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366510, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45779 (p : Pattern) (guard : d366511 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d342818 p = 1 := by simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45448 p hg
    simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45275 p hg
    simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45780 (p : Pattern) (guard : d366512 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366511 p = 1 := by simpa only [d366512, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45779 p hg
    simpa only [d366512, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366512, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d366512, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45781 (p : Pattern) (guard : d366513 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366507 p = 1 := by simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45771 p hg
    simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366512 p = 1 := by simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45780 p hg
    simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45782 (p : Pattern) (guard : d366353 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366349 p = 1 := by simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45775 p hg
    simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45278 p hg
    simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45783 (p : Pattern) (guard : d366514 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366513 p = 1 := by simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45781 p hg
    simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366353 p = 1 := by simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45782 p hg
    simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45784 (p : Pattern) (guard : d366515 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366514 p = 1 := by simpa only [d366515, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45783 p hg
    simpa only [d366515, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366515, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366515, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45785 (p : Pattern) (guard : d366516 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366510 p = 1 := by simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45778 p hg
    simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366515 p = 1 := by simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45784 p hg
    simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45786 (p : Pattern) (guard : d366517 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366516 p = 1 := by simpa only [d366517, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45785 p hg
    simpa only [d366517, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366517, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366517, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45787 (p : Pattern) (guard : d366518 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366517 p = 1 := by simpa only [d366518, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45786 p hg
    simpa only [d366518, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366518, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366518, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45788 (p : Pattern) (guard : d366519 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366519, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366519, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366518 p = 1 := by simpa only [d366519, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45787 p hg
    simpa only [d366519, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45789 (p : Pattern) (guard : d366520 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366519 p = 1 := by simpa only [d366520, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45788 p hg
    simpa only [d366520, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366520, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366520, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45790 (p : Pattern) (guard : d366521 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366513 p = 1 := by simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45781 p hg
    simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342821 p = 1 := by simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45451 p hg
    simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45791 (p : Pattern) (guard : d366522 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366521 p = 1 := by simpa only [d366522, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45790 p hg
    simpa only [d366522, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366522, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366522, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45792 (p : Pattern) (guard : d1525 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45446 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45793 (p : Pattern) (guard : d32153 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45792 p hg
    simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45794 (p : Pattern) (guard : d366523 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32153 p = 1 := by simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45793 p hg
    simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45275 p hg
    simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45795 (p : Pattern) (guard : d366524 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366523 p = 1 := by simpa only [d366524, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45794 p hg
    simpa only [d366524, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366524, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d366524, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45796 (p : Pattern) (guard : d366525 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366524 p = 1 := by simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45795 p hg
    simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45278 p hg
    simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45797 (p : Pattern) (guard : d366526 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366525 p = 1 := by simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45796 p hg
    simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45798 (p : Pattern) (guard : d366527 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366526 p = 1 := by simpa only [d366527, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45797 p hg
    simpa only [d366527, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366527, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366527, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45799 (p : Pattern) (guard : d366528 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366522 p = 1 := by simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45791 p hg
    simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366527 p = 1 := by simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45798 p hg
    simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45800 (p : Pattern) (guard : d366529 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366528 p = 1 := by simpa only [d366529, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45799 p hg
    simpa only [d366529, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366529, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366529, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45801 (p : Pattern) (guard : d366530 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366529 p = 1 := by simpa only [d366530, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45800 p hg
    simpa only [d366530, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366530, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366530, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45802 (p : Pattern) (guard : d366531 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366531, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366531, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366530 p = 1 := by simpa only [d366531, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45801 p hg
    simpa only [d366531, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45803 (p : Pattern) (guard : d366532 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366531 p = 1 := by simpa only [d366532, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45802 p hg
    simpa only [d366532, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366532, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366532, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45804 (p : Pattern) (guard : d366533 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366520 p = 1 := by simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45789 p hg
    simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366532 p = 1 := by simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45803 p hg
    simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45805 (p : Pattern) (guard : d366361 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32153 p = 1 := by simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45793 p hg
    simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45806 (p : Pattern) (guard : d366362 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366361 p = 1 := by simpa only [d366362, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45805 p hg
    simpa only [d366362, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366362, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d366362, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45807 (p : Pattern) (guard : d366534 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366507 p = 1 := by simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45771 p hg
    simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366362 p = 1 := by simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45806 p hg
    simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45808 (p : Pattern) (guard : d366535 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366534 p = 1 := by simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45807 p hg
    simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45809 (p : Pattern) (guard : d366536 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366535 p = 1 := by simpa only [d366536, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45808 p hg
    simpa only [d366536, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366536, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366536, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45810 (p : Pattern) (guard : d366537 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366536 p = 1 := by simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45809 p hg
    simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366527 p = 1 := by simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45798 p hg
    simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45811 (p : Pattern) (guard : d366538 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366537 p = 1 := by simpa only [d366538, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45810 p hg
    simpa only [d366538, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366538, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366538, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45812 (p : Pattern) (guard : d366539 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366538 p = 1 := by simpa only [d366539, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45811 p hg
    simpa only [d366539, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366539, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366539, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45813 (p : Pattern) (guard : d366540 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366540, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366540, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366539 p = 1 := by simpa only [d366540, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45812 p hg
    simpa only [d366540, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45814 (p : Pattern) (guard : d366541 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366540 p = 1 := by simpa only [d366541, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45813 p hg
    simpa only [d366541, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366541, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366541, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45815 (p : Pattern) (guard : d366542 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366512 p = 1 := by simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45780 p hg
    simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45278 p hg
    simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45816 (p : Pattern) (guard : d366543 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366542 p = 1 := by simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45815 p hg
    simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342710 p = 1 := by simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45280 p hg
    simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45817 (p : Pattern) (guard : d366544 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366543 p = 1 := by simpa only [d366544, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45816 p hg
    simpa only [d366544, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366544, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366544, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45818 (p : Pattern) (guard : d366545 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366544 p = 1 := by simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45817 p hg
    simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45284 p hg
    simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45819 (p : Pattern) (guard : d366546 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366545 p = 1 := by simpa only [d366546, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45818 p hg
    simpa only [d366546, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366546, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366546, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45820 (p : Pattern) (guard : d366547 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366546 p = 1 := by simpa only [d366547, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45819 p hg
    simpa only [d366547, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366547, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366547, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45821 (p : Pattern) (guard : d366548 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366548, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366548, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366547 p = 1 := by simpa only [d366548, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45820 p hg
    simpa only [d366548, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45822 (p : Pattern) (guard : d366549 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366548 p = 1 := by simpa only [d366549, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45821 p hg
    simpa only [d366549, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366549, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366549, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45823 (p : Pattern) (guard : d366550 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366541 p = 1 := by simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45814 p hg
    simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45822 p hg
    simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45824 (p : Pattern) (guard : d366551 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366533 p = 1 := by simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45804 p hg
    simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366550 p = 1 := by simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45823 p hg
    simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45825 (p : Pattern) (guard : d366552 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366522 p = 1 := by simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45791 p hg
    simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366544 p = 1 := by simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45817 p hg
    simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45826 (p : Pattern) (guard : d366553 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366552 p = 1 := by simpa only [d366553, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45825 p hg
    simpa only [d366553, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366553, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366553, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45827 (p : Pattern) (guard : d366554 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366553 p = 1 := by simpa only [d366554, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45826 p hg
    simpa only [d366554, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366554, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366554, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45828 (p : Pattern) (guard : d366555 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366555, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366555, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366554 p = 1 := by simpa only [d366555, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45827 p hg
    simpa only [d366555, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45829 (p : Pattern) (guard : d366556 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366555 p = 1 := by simpa only [d366556, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45828 p hg
    simpa only [d366556, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366556, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366556, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45830 (p : Pattern) (guard : d366557 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366556 p = 1 := by simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45829 p hg
    simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45822 p hg
    simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45831 (p : Pattern) (guard : d366558 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366549 p = 1 := by simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45822 p hg
    simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45832 (p : Pattern) (guard : d366559 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366557 p = 1 := by simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45830 p hg
    simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366558 p = 1 := by simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45831 p hg
    simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45833 (p : Pattern) (guard : d366560 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366551 p = 1 := by simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45824 p hg
    simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366559 p = 1 := by simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45832 p hg
    simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45834 (p : Pattern) (guard : d366561 p = 1) : d51294 p ≤ (7 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366561, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d366561, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366560 p = 1 := by simpa only [d366561, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45833 p hg
    simpa only [d366561, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45835 (p : Pattern) (guard : d366562 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366562, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d366562, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366561 p = 1 := by simpa only [d366562, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45834 p hg
    simpa only [d366562, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45836 (p : Pattern) (guard : d366563 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366558 p = 1 := by simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45831 p hg
    simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45837 (p : Pattern) (guard : d366564 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366559 p = 1 := by simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45832 p hg
    simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366563 p = 1 := by simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45836 p hg
    simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45838 (p : Pattern) (guard : d366565 p = 1) : d51294 p ≤ (7 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366565, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d366565, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366564 p = 1 := by simpa only [d366565, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45837 p hg
    simpa only [d366565, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45839 (p : Pattern) (guard : d366566 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366566, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d366566, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366565 p = 1 := by simpa only [d366566, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45838 p hg
    simpa only [d366566, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45840 (p : Pattern) (guard : d366567 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366562 p = 1 := by simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45835 p hg
    simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366566 p = 1 := by simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45839 p hg
    simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45841 (p : Pattern) (guard : d366568 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366566 p = 1 := by simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45839 p hg
    simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45842 (p : Pattern) (guard : d366569 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366567 p = 1 := by simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45840 p hg
    simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366568 p = 1 := by simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45841 p hg
    simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45843 (p : Pattern) (guard : d366570 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366569 p = 1 := by simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45842 p hg
    simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45844 (p : Pattern) (guard : d366571 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366570 p = 1 := by simpa only [d366571, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45843 p hg
    simpa only [d366571, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366571, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d366571, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45845 (p : Pattern) (guard : d366572 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366572, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d366572, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366571 p = 1 := by simpa only [d366572, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45844 p hg
    simpa only [d366572, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45846 (p : Pattern) (guard : d366573 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366568 p = 1 := by simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45841 p hg
    simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45847 (p : Pattern) (guard : d366574 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366573 p = 1 := by simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45846 p hg
    simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45848 (p : Pattern) (guard : d366575 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366574 p = 1 := by simpa only [d366575, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45847 p hg
    simpa only [d366575, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366575, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d366575, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45849 (p : Pattern) (guard : d366576 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366576, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d366576, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366575 p = 1 := by simpa only [d366576, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45848 p hg
    simpa only [d366576, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45850 (p : Pattern) (guard : d366577 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366572 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45845 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366576 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45849 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45851 (p : Pattern) (guard : d366578 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366577 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45850 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45852 (p : Pattern) (guard : d366579 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366578 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45851 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45853 (p : Pattern) (guard : d366580 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366579 p = 1 := by simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45852 p hg
    simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45854 (p : Pattern) (guard : d366581 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366576 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45849 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45855 (p : Pattern) (guard : d366582 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366581 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45854 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45856 (p : Pattern) (guard : d366583 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366582 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45855 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45857 (p : Pattern) (guard : d366584 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366583 p = 1 := by simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45856 p hg
    simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45858 (p : Pattern) (guard : d366585 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366580 p = 1 := by simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45853 p hg
    simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366584 p = 1 := by simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45857 p hg
    simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45859 (p : Pattern) (guard : d366586 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366585 p = 1 := by simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45858 p hg
    simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45860 (p : Pattern) (guard : d366587 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366586 p = 1 := by simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45859 p hg
    simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45861 (p : Pattern) (guard : d366588 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366587 p = 1 := by simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45860 p hg
    simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45862 (p : Pattern) (guard : d366589 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366588 p = 1 := by simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45861 p hg
    simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45863 (p : Pattern) (guard : d366590 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366590, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366590, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366589 p = 1 := by simpa only [d366590, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45862 p hg
    simpa only [d366590, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45864 (p : Pattern) (guard : d366572 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366572, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d366572, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366571 p = 1 := by simpa only [d366572, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45844 p hg
    simpa only [d366572, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45865 (p : Pattern) (guard : d366576 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366576, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d366576, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366575 p = 1 := by simpa only [d366576, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45848 p hg
    simpa only [d366576, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45866 (p : Pattern) (guard : d366577 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366572 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45864 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366576 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45865 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45867 (p : Pattern) (guard : d366578 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366577 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45866 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45868 (p : Pattern) (guard : d366579 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366578 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45867 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45869 (p : Pattern) (guard : d366580 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366579 p = 1 := by simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45868 p hg
    simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45870 (p : Pattern) (guard : d366581 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366576 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45865 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45871 (p : Pattern) (guard : d366582 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366581 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45870 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45872 (p : Pattern) (guard : d366583 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366582 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45871 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45873 (p : Pattern) (guard : d366584 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366583 p = 1 := by simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45872 p hg
    simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45874 (p : Pattern) (guard : d366585 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366580 p = 1 := by simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45869 p hg
    simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366584 p = 1 := by simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45873 p hg
    simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45875 (p : Pattern) (guard : d366586 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366585 p = 1 := by simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45874 p hg
    simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45876 (p : Pattern) (guard : d366587 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366586 p = 1 := by simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45875 p hg
    simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45877 (p : Pattern) (guard : d366588 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366587 p = 1 := by simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45876 p hg
    simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45878 (p : Pattern) (guard : d366589 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366588 p = 1 := by simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45877 p hg
    simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45879 (p : Pattern) (guard : d366593 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366579 p = 1 := by simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45852 p hg
    simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45880 (p : Pattern) (guard : d366594 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366583 p = 1 := by simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45856 p hg
    simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45881 (p : Pattern) (guard : d366595 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366593 p = 1 := by simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45879 p hg
    simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366594 p = 1 := by simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45880 p hg
    simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45882 (p : Pattern) (guard : d366596 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366595 p = 1 := by simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45881 p hg
    simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45883 (p : Pattern) (guard : d366597 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366596 p = 1 := by simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45882 p hg
    simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45884 (p : Pattern) (guard : d366598 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366597 p = 1 := by simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45883 p hg
    simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45885 (p : Pattern) (guard : d366599 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366598 p = 1 := by simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45884 p hg
    simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45886 (p : Pattern) (guard : d366600 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366589 p = 1 := by simpa only [d366600, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45878 p hg
    simpa only [d366600, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366599 p = 1 := by simpa only [d366600, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45885 p hg
    simpa only [d366600, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45887 (p : Pattern) (guard : d366601 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366590 p = 1 := by simpa only [d366601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45863 p hg
    simpa only [d366601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366600 p = 1 := by simpa only [d366601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45886 p hg
    simpa only [d366601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45888 (p : Pattern) (guard : d366602 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366601 p = 1 := by simpa only [d366602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45887 p hg
    simpa only [d366602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d366602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45889 (p : Pattern) (guard : d367467 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366602 p = 1 := by simpa only [d367467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45888 p hg
    simpa only [d367467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d367467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45890 (p : Pattern) (guard : d367468 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d367468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367467 p = 1 := by simpa only [d367468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45889 p hg
    simpa only [d367468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45891 (p : Pattern) (guard : d366518 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45892 (p : Pattern) (guard : d366519 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366519, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366519, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366518 p = 1 := by simpa only [d366519, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45891 p hg
    simpa only [d366519, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45893 (p : Pattern) (guard : d366520 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366519 p = 1 := by simpa only [d366520, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45892 p hg
    simpa only [d366520, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366520, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366520, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45894 (p : Pattern) (guard : d366530 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45895 (p : Pattern) (guard : d366531 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366531, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366531, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366530 p = 1 := by simpa only [d366531, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45894 p hg
    simpa only [d366531, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45896 (p : Pattern) (guard : d366532 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366531 p = 1 := by simpa only [d366532, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45895 p hg
    simpa only [d366532, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366532, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366532, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45897 (p : Pattern) (guard : d366533 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366520 p = 1 := by simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45893 p hg
    simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366532 p = 1 := by simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45896 p hg
    simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45898 (p : Pattern) (guard : d366539 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45899 (p : Pattern) (guard : d366540 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366540, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366540, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366539 p = 1 := by simpa only [d366540, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45898 p hg
    simpa only [d366540, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45900 (p : Pattern) (guard : d366541 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366540 p = 1 := by simpa only [d366541, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45899 p hg
    simpa only [d366541, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366541, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366541, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45901 (p : Pattern) (guard : d366547 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45902 (p : Pattern) (guard : d366548 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366548, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366548, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366547 p = 1 := by simpa only [d366548, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45901 p hg
    simpa only [d366548, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45903 (p : Pattern) (guard : d366549 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366548 p = 1 := by simpa only [d366549, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45902 p hg
    simpa only [d366549, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366549, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366549, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45904 (p : Pattern) (guard : d366550 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366541 p = 1 := by simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45900 p hg
    simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45903 p hg
    simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45905 (p : Pattern) (guard : d366551 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366533 p = 1 := by simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45897 p hg
    simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366550 p = 1 := by simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45904 p hg
    simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45906 (p : Pattern) (guard : d366554 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45907 (p : Pattern) (guard : d366555 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366555, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366555, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366554 p = 1 := by simpa only [d366555, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45906 p hg
    simpa only [d366555, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45908 (p : Pattern) (guard : d366556 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366555 p = 1 := by simpa only [d366556, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45907 p hg
    simpa only [d366556, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366556, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366556, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45909 (p : Pattern) (guard : d366557 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366556 p = 1 := by simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45908 p hg
    simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45903 p hg
    simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45910 (p : Pattern) (guard : d366558 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366549 p = 1 := by simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45903 p hg
    simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45911 (p : Pattern) (guard : d366559 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366557 p = 1 := by simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45909 p hg
    simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366558 p = 1 := by simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45910 p hg
    simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45912 (p : Pattern) (guard : d366560 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366551 p = 1 := by simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45905 p hg
    simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366559 p = 1 := by simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45911 p hg
    simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45913 (p : Pattern) (guard : d366561 p = 1) : d51453 p ≤ (7 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366561, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d366561, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366560 p = 1 := by simpa only [d366561, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45912 p hg
    simpa only [d366561, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45914 (p : Pattern) (guard : d366562 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366562, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d366562, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366561 p = 1 := by simpa only [d366562, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45913 p hg
    simpa only [d366562, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45915 (p : Pattern) (guard : d366563 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366558 p = 1 := by simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45910 p hg
    simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45916 (p : Pattern) (guard : d366564 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366559 p = 1 := by simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45911 p hg
    simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366563 p = 1 := by simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45915 p hg
    simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45917 (p : Pattern) (guard : d366565 p = 1) : d51453 p ≤ (7 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366565, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d366565, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366564 p = 1 := by simpa only [d366565, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45916 p hg
    simpa only [d366565, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45918 (p : Pattern) (guard : d366566 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366566, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d366566, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366565 p = 1 := by simpa only [d366566, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45917 p hg
    simpa only [d366566, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45919 (p : Pattern) (guard : d366567 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366562 p = 1 := by simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45914 p hg
    simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366566 p = 1 := by simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45918 p hg
    simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45920 (p : Pattern) (guard : d366568 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366566 p = 1 := by simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45918 p hg
    simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45921 (p : Pattern) (guard : d366569 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366567 p = 1 := by simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45919 p hg
    simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366568 p = 1 := by simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45920 p hg
    simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45922 (p : Pattern) (guard : d366570 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366569 p = 1 := by simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45921 p hg
    simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45923 (p : Pattern) (guard : d366571 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366570 p = 1 := by simpa only [d366571, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45922 p hg
    simpa only [d366571, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366571, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d366571, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45924 (p : Pattern) (guard : d366572 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366572, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d366572, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366571 p = 1 := by simpa only [d366572, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45923 p hg
    simpa only [d366572, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45925 (p : Pattern) (guard : d366573 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366568 p = 1 := by simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45920 p hg
    simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45926 (p : Pattern) (guard : d366574 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366573 p = 1 := by simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45925 p hg
    simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45927 (p : Pattern) (guard : d366575 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366574 p = 1 := by simpa only [d366575, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45926 p hg
    simpa only [d366575, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366575, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d366575, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45928 (p : Pattern) (guard : d366576 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366576, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d366576, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366575 p = 1 := by simpa only [d366576, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45927 p hg
    simpa only [d366576, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45929 (p : Pattern) (guard : d366577 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366572 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45924 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366576 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45928 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45930 (p : Pattern) (guard : d366578 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366577 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45929 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45931 (p : Pattern) (guard : d366579 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366578 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45930 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45932 (p : Pattern) (guard : d366593 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366579 p = 1 := by simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45931 p hg
    simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45933 (p : Pattern) (guard : d366581 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366576 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45928 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45934 (p : Pattern) (guard : d366582 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366581 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45933 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45935 (p : Pattern) (guard : d366583 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366582 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45934 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45936 (p : Pattern) (guard : d366594 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366583 p = 1 := by simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45935 p hg
    simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45937 (p : Pattern) (guard : d366595 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366593 p = 1 := by simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45932 p hg
    simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366594 p = 1 := by simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45936 p hg
    simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45938 (p : Pattern) (guard : d366596 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366595 p = 1 := by simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45937 p hg
    simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45939 (p : Pattern) (guard : d366597 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366596 p = 1 := by simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45938 p hg
    simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45940 (p : Pattern) (guard : d366598 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366597 p = 1 := by simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45939 p hg
    simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45941 (p : Pattern) (guard : d366599 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366598 p = 1 := by simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45940 p hg
    simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45942 (p : Pattern) (guard : d367469 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367469, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367469, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366599 p = 1 := by simpa only [d367469, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45941 p hg
    simpa only [d367469, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45943 (p : Pattern) (guard : d367470 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367469 p = 1 := by simpa only [d367470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45942 p hg
    simpa only [d367470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45944 (p : Pattern) (guard : d367471 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367470 p = 1 := by simpa only [d367471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45943 p hg
    simpa only [d367471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45945 (p : Pattern) (guard : d367472 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367471 p = 1 := by simpa only [d367472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45944 p hg
    simpa only [d367472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45946 (p : Pattern) (guard : d367473 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367472 p = 1 := by simpa only [d367473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45945 p hg
    simpa only [d367473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45947 (p : Pattern) (guard : d367474 p = 1) : d51470 p ≤ (7 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367468 p = 1 := by simpa only [d367474, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45890 p hg
    simpa only [d367474, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367473 p = 1 := by simpa only [d367474, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45946 p hg
    simpa only [d367474, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45948 (p : Pattern) (guard : d1087 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45387 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45949 (p : Pattern) (guard : d366506 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d42941 p = 1 := by simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45703 p hg
    simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45948 p hg
    simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45950 (p : Pattern) (guard : d366507 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366506 p = 1 := by simpa only [d366507, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45949 p hg
    simpa only [d366507, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366507, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d366507, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45951 (p : Pattern) (guard : d366508 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366507 p = 1 := by simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45950 p hg
    simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45952 (p : Pattern) (guard : d366347 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d42940 p = 1 := by simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45702 p hg
    simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45387 p hg
    simpa only [d366347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45953 (p : Pattern) (guard : d366348 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d366347 p = 1 := by simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45952 p hg
    simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d366348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45954 (p : Pattern) (guard : d366349 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366348 p = 1 := by simpa only [d366349, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45953 p hg
    simpa only [d366349, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366349, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d366349, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45955 (p : Pattern) (guard : d366350 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d42943 p = 1 := by simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45705 p hg
    simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366349 p = 1 := by simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45954 p hg
    simpa only [d366350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45956 (p : Pattern) (guard : d366509 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366508 p = 1 := by simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45951 p hg
    simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366350 p = 1 := by simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45955 p hg
    simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45957 (p : Pattern) (guard : d366510 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366509 p = 1 := by simpa only [d366510, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45956 p hg
    simpa only [d366510, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366510, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366510, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45958 (p : Pattern) (guard : d366511 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d342818 p = 1 := by simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45533 p hg
    simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45388 p hg
    simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45959 (p : Pattern) (guard : d366512 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366511 p = 1 := by simpa only [d366512, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45958 p hg
    simpa only [d366512, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366512, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d366512, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45960 (p : Pattern) (guard : d366513 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366507 p = 1 := by simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45950 p hg
    simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366512 p = 1 := by simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45959 p hg
    simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45961 (p : Pattern) (guard : d366353 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366349 p = 1 := by simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45954 p hg
    simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45391 p hg
    simpa only [d366353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45962 (p : Pattern) (guard : d366514 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366513 p = 1 := by simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45960 p hg
    simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366353 p = 1 := by simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45961 p hg
    simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45963 (p : Pattern) (guard : d366515 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366514 p = 1 := by simpa only [d366515, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45962 p hg
    simpa only [d366515, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366515, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366515, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45964 (p : Pattern) (guard : d366516 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366510 p = 1 := by simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45957 p hg
    simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366515 p = 1 := by simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45963 p hg
    simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45965 (p : Pattern) (guard : d366752 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366752, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d366752, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366516 p = 1 := by simpa only [d366752, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45964 p hg
    simpa only [d366752, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45966 (p : Pattern) (guard : d366517 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366516 p = 1 := by simpa only [d366517, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45785 p hg
    simpa only [d366517, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366517, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366517, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45967 (p : Pattern) (guard : d366753 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366752 p = 1 := by simpa only [d366753, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45965 p hg
    simpa only [d366753, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366517 p = 1 := by simpa only [d366753, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45966 p hg
    simpa only [d366753, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45968 (p : Pattern) (guard : d366518 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare45969 (p : Pattern) (guard : d366754 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366753 p = 1 := by simpa only [d366754, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45967 p hg
    simpa only [d366754, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366518 p = 1 := by simpa only [d366754, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45968 p hg
    simpa only [d366754, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45970 (p : Pattern) (guard : d366755 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366754 p = 1 := by simpa only [d366755, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45969 p hg
    simpa only [d366755, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366755, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d366755, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45971 (p : Pattern) (guard : d366521 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366513 p = 1 := by simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45960 p hg
    simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342821 p = 1 := by simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45536 p hg
    simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45972 (p : Pattern) (guard : d366522 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366521 p = 1 := by simpa only [d366522, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45971 p hg
    simpa only [d366522, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366522, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366522, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45973 (p : Pattern) (guard : d1525 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45531 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45974 (p : Pattern) (guard : d32153 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45973 p hg
    simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d32153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45975 (p : Pattern) (guard : d366523 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32153 p = 1 := by simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45974 p hg
    simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45388 p hg
    simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45976 (p : Pattern) (guard : d366524 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366523 p = 1 := by simpa only [d366524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45975 p hg
    simpa only [d366524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d366524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45977 (p : Pattern) (guard : d366525 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366524 p = 1 := by simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45976 p hg
    simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45391 p hg
    simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45978 (p : Pattern) (guard : d366526 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366525 p = 1 := by simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45977 p hg
    simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45979 (p : Pattern) (guard : d366527 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366526 p = 1 := by simpa only [d366527, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45978 p hg
    simpa only [d366527, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366527, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366527, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45980 (p : Pattern) (guard : d366528 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366522 p = 1 := by simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45972 p hg
    simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366527 p = 1 := by simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45979 p hg
    simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45981 (p : Pattern) (guard : d366756 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366756, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d366756, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366528 p = 1 := by simpa only [d366756, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45980 p hg
    simpa only [d366756, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45982 (p : Pattern) (guard : d366529 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366528 p = 1 := by simpa only [d366529, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45799 p hg
    simpa only [d366529, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366529, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366529, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45983 (p : Pattern) (guard : d366757 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366756 p = 1 := by simpa only [d366757, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45981 p hg
    simpa only [d366757, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366529 p = 1 := by simpa only [d366757, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45982 p hg
    simpa only [d366757, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45984 (p : Pattern) (guard : d366530 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare45985 (p : Pattern) (guard : d366758 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366757 p = 1 := by simpa only [d366758, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45983 p hg
    simpa only [d366758, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366530 p = 1 := by simpa only [d366758, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45984 p hg
    simpa only [d366758, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45986 (p : Pattern) (guard : d366759 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366758 p = 1 := by simpa only [d366759, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45985 p hg
    simpa only [d366759, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366759, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d366759, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45987 (p : Pattern) (guard : d366760 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366755 p = 1 := by simpa only [d366760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45970 p hg
    simpa only [d366760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366759 p = 1 := by simpa only [d366760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45986 p hg
    simpa only [d366760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45988 (p : Pattern) (guard : d366361 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32153 p = 1 := by simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45974 p hg
    simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d366361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45989 (p : Pattern) (guard : d366362 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366361 p = 1 := by simpa only [d366362, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45988 p hg
    simpa only [d366362, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366362, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d366362, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45990 (p : Pattern) (guard : d366534 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366507 p = 1 := by simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45950 p hg
    simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366362 p = 1 := by simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45989 p hg
    simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45991 (p : Pattern) (guard : d366535 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366534 p = 1 := by simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45990 p hg
    simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45992 (p : Pattern) (guard : d366536 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366535 p = 1 := by simpa only [d366536, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45991 p hg
    simpa only [d366536, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366536, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366536, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45993 (p : Pattern) (guard : d366537 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366536 p = 1 := by simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45992 p hg
    simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366527 p = 1 := by simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45979 p hg
    simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45994 (p : Pattern) (guard : d366746 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366746, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d366746, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366537 p = 1 := by simpa only [d366746, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45993 p hg
    simpa only [d366746, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45995 (p : Pattern) (guard : d366538 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366537 p = 1 := by simpa only [d366538, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45810 p hg
    simpa only [d366538, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366538, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366538, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45996 (p : Pattern) (guard : d366747 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366746 p = 1 := by simpa only [d366747, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45994 p hg
    simpa only [d366747, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366538 p = 1 := by simpa only [d366747, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45995 p hg
    simpa only [d366747, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45997 (p : Pattern) (guard : d366539 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare45998 (p : Pattern) (guard : d366748 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366747 p = 1 := by simpa only [d366748, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45996 p hg
    simpa only [d366748, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366539 p = 1 := by simpa only [d366748, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45997 p hg
    simpa only [d366748, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45999 (p : Pattern) (guard : d366749 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366748 p = 1 := by simpa only [d366749, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45998 p hg
    simpa only [d366749, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366749, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d366749, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
