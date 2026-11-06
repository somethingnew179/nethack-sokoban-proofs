import NetHack.Soko22Hazard87.Compare141
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35500 (p : Pattern) (guard : d316231 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316230 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35499 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35501 (p : Pattern) (guard : d316232 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316227 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35494 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35500 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35502 (p : Pattern) (guard : d316233 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316232 p = 1 := by simpa only [d316233, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35501 p hg
    simpa only [d316233, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316233, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d316233, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35503 (p : Pattern) (guard : d316234 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35502 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285870 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35233 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35504 (p : Pattern) (guard : d316278 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316234 p = 1 := by simpa only [d316278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35503 p hg
    simpa only [d316278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35505 (p : Pattern) (guard : d316235 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316234 p = 1 := by simpa only [d316235, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35328 p hg
    simpa only [d316235, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316235, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316235, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35506 (p : Pattern) (guard : d316279 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316278 p = 1 := by simpa only [d316279, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35504 p hg
    simpa only [d316279, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316235 p = 1 := by simpa only [d316279, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35505 p hg
    simpa only [d316279, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35507 (p : Pattern) (guard : d1520 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare35508 (p : Pattern) (guard : d33554 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d33554, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35507 p hg
    simpa only [d33554, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33554, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d33554, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35509 (p : Pattern) (guard : d286611 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33554 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35508 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35510 (p : Pattern) (guard : d286612 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d286611 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35509 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35511 (p : Pattern) (guard : d286613 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d286612 p = 1 := by simpa only [d286613, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35510 p hg
    simpa only [d286613, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286613, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d286613, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35512 (p : Pattern) (guard : d316227 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35511 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285867 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35242 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35513 (p : Pattern) (guard : d534 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare35514 (p : Pattern) (guard : d33559 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d33559, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35513 p hg
    simpa only [d33559, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33559, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d33559, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35515 (p : Pattern) (guard : d316228 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33559 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35514 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35516 (p : Pattern) (guard : d316229 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316228 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35515 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35517 (p : Pattern) (guard : d316230 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316229 p = 1 := by simpa only [d316230, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35516 p hg
    simpa only [d316230, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316230, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d316230, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35518 (p : Pattern) (guard : d316231 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316230 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35517 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35027 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35519 (p : Pattern) (guard : d316232 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316227 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35512 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35518 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35520 (p : Pattern) (guard : d316233 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316232 p = 1 := by simpa only [d316233, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35519 p hg
    simpa only [d316233, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316233, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d316233, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35521 (p : Pattern) (guard : d316234 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35520 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285870 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35245 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35522 (p : Pattern) (guard : d316235 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316234 p = 1 := by simpa only [d316235, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35521 p hg
    simpa only [d316235, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316235, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316235, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35523 (p : Pattern) (guard : d316236 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316235 p = 1 := by simpa only [d316236, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35522 p hg
    simpa only [d316236, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316236, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316236, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35524 (p : Pattern) (guard : d316280 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316279 p = 1 := by simpa only [d316280, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35506 p hg
    simpa only [d316280, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316236 p = 1 := by simpa only [d316280, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35523 p hg
    simpa only [d316280, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35525 (p : Pattern) (guard : d316281 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316280 p = 1 := by simpa only [d316281, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35524 p hg
    simpa only [d316281, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316281, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316281, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35526 (p : Pattern) (guard : d316282 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316281 p = 1 := by simpa only [d316282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35525 p hg
    simpa only [d316282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285918 p = 1 := by simpa only [d316282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35250 p hg
    simpa only [d316282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35527 (p : Pattern) (guard : d285991 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35231 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35528 (p : Pattern) (guard : d285992 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285991 p = 1 := by simpa only [d285992, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35527 p hg
    simpa only [d285992, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285992, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d285992, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35529 (p : Pattern) (guard : d285993 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285992 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35528 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35015 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35530 (p : Pattern) (guard : d286062 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d286062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285993 p = 1 := by simpa only [d286062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35529 p hg
    simpa only [d286062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35531 (p : Pattern) (guard : d285994 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285993 p = 1 := by simpa only [d285994, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35336 p hg
    simpa only [d285994, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285994, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d285994, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35532 (p : Pattern) (guard : d286063 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d286062 p = 1 := by simpa only [d286063, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35530 p hg
    simpa only [d286063, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285994 p = 1 := by simpa only [d286063, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35531 p hg
    simpa only [d286063, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35533 (p : Pattern) (guard : d285991 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35243 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35534 (p : Pattern) (guard : d285992 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285991 p = 1 := by simpa only [d285992, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35533 p hg
    simpa only [d285992, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285992, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d285992, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35535 (p : Pattern) (guard : d285993 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285992 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35534 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35032 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35536 (p : Pattern) (guard : d285994 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285993 p = 1 := by simpa only [d285994, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35535 p hg
    simpa only [d285994, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285994, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d285994, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35537 (p : Pattern) (guard : d285995 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285994 p = 1 := by simpa only [d285995, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35536 p hg
    simpa only [d285995, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285995, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d285995, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35538 (p : Pattern) (guard : d286064 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d286063 p = 1 := by simpa only [d286064, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35532 p hg
    simpa only [d286064, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285995 p = 1 := by simpa only [d286064, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35537 p hg
    simpa only [d286064, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35539 (p : Pattern) (guard : d286065 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d286064 p = 1 := by simpa only [d286065, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35538 p hg
    simpa only [d286065, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286065, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d286065, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35540 (p : Pattern) (guard : d286066 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d286065 p = 1 := by simpa only [d286066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35539 p hg
    simpa only [d286066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257233 p = 1 := by simpa only [d286066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35039 p hg
    simpa only [d286066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35541 (p : Pattern) (guard : d316283 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316282 p = 1 := by simpa only [d316283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35526 p hg
    simpa only [d316283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286066 p = 1 := by simpa only [d316283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35540 p hg
    simpa only [d316283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35542 (p : Pattern) (guard : d316284 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316283 p = 1 := by simpa only [d316284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35541 p hg
    simpa only [d316284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285920 p = 1 := by simpa only [d316284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d316284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35543 (p : Pattern) (guard : d316285 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316285, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d316285, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316284 p = 1 := by simpa only [d316285, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35542 p hg
    simpa only [d316285, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35544 (p : Pattern) (guard : d316286 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316286, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d316286, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316285 p = 1 := by simpa only [d316286, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35543 p hg
    simpa only [d316286, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35545 (p : Pattern) (guard : d316287 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316286 p = 1 := by simpa only [d316287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35544 p hg
    simpa only [d316287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285923 p = 1 := by simpa only [d316287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35255 p hg
    simpa only [d316287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35546 (p : Pattern) (guard : d316288 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316287 p = 1 := by simpa only [d316288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d316288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285924 p = 1 := by simpa only [d316288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35256 p hg
    simpa only [d316288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35547 (p : Pattern) (guard : d316289 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316288 p = 1 := by simpa only [d316289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35546 p hg
    simpa only [d316289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d316289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35548 (p : Pattern) (guard : d316290 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316289 p = 1 := by simpa only [d316290, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35547 p hg
    simpa only [d316290, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316290, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d316290, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35549 (p : Pattern) (guard : d316291 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316291, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d316291, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316290 p = 1 := by simpa only [d316291, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35548 p hg
    simpa only [d316291, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35550 (p : Pattern) (guard : d316292 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316291 p = 1 := by simpa only [d316292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35549 p hg
    simpa only [d316292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285928 p = 1 := by simpa only [d316292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35260 p hg
    simpa only [d316292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35551 (p : Pattern) (guard : d316293 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316292 p = 1 := by simpa only [d316293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35550 p hg
    simpa only [d316293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35552 (p : Pattern) (guard : d316294 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316293 p = 1 := by simpa only [d316294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35551 p hg
    simpa only [d316294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35553 (p : Pattern) (guard : d316295 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316294 p = 1 := by simpa only [d316295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35552 p hg
    simpa only [d316295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35554 (p : Pattern) (guard : d316296 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316295 p = 1 := by simpa only [d316296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35553 p hg
    simpa only [d316296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285932 p = 1 := by simpa only [d316296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35264 p hg
    simpa only [d316296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35555 (p : Pattern) (guard : d316297 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316296 p = 1 := by simpa only [d316297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35554 p hg
    simpa only [d316297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35556 (p : Pattern) (guard : d286082 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285928 p = 1 := by simpa only [d286082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35260 p hg
    simpa only [d286082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35557 (p : Pattern) (guard : d286083 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286082 p = 1 := by simpa only [d286083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35556 p hg
    simpa only [d286083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35558 (p : Pattern) (guard : d286084 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286083 p = 1 := by simpa only [d286084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35557 p hg
    simpa only [d286084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35559 (p : Pattern) (guard : d286085 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286084 p = 1 := by simpa only [d286085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35558 p hg
    simpa only [d286085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35560 (p : Pattern) (guard : d286086 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286085 p = 1 := by simpa only [d286086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35559 p hg
    simpa only [d286086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35561 (p : Pattern) (guard : d286087 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d286086 p = 1 := by simpa only [d286087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35560 p hg
    simpa only [d286087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35562 (p : Pattern) (guard : d316298 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316297 p = 1 := by simpa only [d316298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35555 p hg
    simpa only [d316298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286087 p = 1 := by simpa only [d316298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35561 p hg
    simpa only [d316298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35563 (p : Pattern) (guard : d316299 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316298 p = 1 := by simpa only [d316299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35562 p hg
    simpa only [d316299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35564 (p : Pattern) (guard : d316300 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316299 p = 1 := by simpa only [d316300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35563 p hg
    simpa only [d316300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35565 (p : Pattern) (guard : d316301 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316301, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316301, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316300 p = 1 := by simpa only [d316301, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35564 p hg
    simpa only [d316301, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35566 (p : Pattern) (guard : d316302 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d316302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316301 p = 1 := by simpa only [d316302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35565 p hg
    simpa only [d316302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35567 (p : Pattern) (guard : d257532 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257248 p = 1 := by simpa only [d257532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35057 p hg
    simpa only [d257532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35568 (p : Pattern) (guard : d257533 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257532 p = 1 := by simpa only [d257533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35567 p hg
    simpa only [d257533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35569 (p : Pattern) (guard : d257534 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257533 p = 1 := by simpa only [d257534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35568 p hg
    simpa only [d257534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35570 (p : Pattern) (guard : d257535 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257534 p = 1 := by simpa only [d257535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35569 p hg
    simpa only [d257535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35571 (p : Pattern) (guard : d257536 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257536, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257536, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257535 p = 1 := by simpa only [d257536, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35570 p hg
    simpa only [d257536, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35572 (p : Pattern) (guard : d257537 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d257537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257536 p = 1 := by simpa only [d257537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35571 p hg
    simpa only [d257537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35573 (p : Pattern) (guard : d316303 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d316302 p = 1 := by simpa only [d316303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35566 p hg
    simpa only [d316303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257537 p = 1 := by simpa only [d316303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35572 p hg
    simpa only [d316303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35574 (p : Pattern) (guard : d316304 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d316303 p = 1 := by simpa only [d316304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35573 p hg
    simpa only [d316304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d316304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35575 (p : Pattern) (guard : d316305 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d316304 p = 1 := by simpa only [d316305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35574 p hg
    simpa only [d316305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d316305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35576 (p : Pattern) (guard : d316306 p = 1) : d50492 p ≤ (3 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d316305 p = 1 := by simpa only [d316306, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35575 p hg
    simpa only [d316306, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316306, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d316306, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35577 (p : Pattern) (guard : d316307 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d316277 p = 1 := by simpa only [d316307, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35488 p hg
    simpa only [d316307, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316306 p = 1 := by simpa only [d316307, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35576 p hg
    simpa only [d316307, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35578 (p : Pattern) (guard : d316308 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316307 p = 1 := by simpa only [d316308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35577 p hg
    simpa only [d316308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35579 (p : Pattern) (guard : d316309 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316308 p = 1 := by simpa only [d316309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35578 p hg
    simpa only [d316309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35580 (p : Pattern) (guard : d316310 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316309 p = 1 := by simpa only [d316310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35579 p hg
    simpa only [d316310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35581 (p : Pattern) (guard : d316311 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316310 p = 1 := by simpa only [d316311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35580 p hg
    simpa only [d316311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35582 (p : Pattern) (guard : d316312 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316311 p = 1 := by simpa only [d316312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35581 p hg
    simpa only [d316312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35583 (p : Pattern) (guard : d316313 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316312 p = 1 := by simpa only [d316313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35582 p hg
    simpa only [d316313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35584 (p : Pattern) (guard : d316314 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d285950 p = 1 := by simpa only [d316314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35282 p hg
    simpa only [d316314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316313 p = 1 := by simpa only [d316314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35583 p hg
    simpa only [d316314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35585 (p : Pattern) (guard : d286105 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35123 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35586 (p : Pattern) (guard : d316315 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316244 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35346 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286105 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35585 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35587 (p : Pattern) (guard : d316316 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316315 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35586 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35588 (p : Pattern) (guard : d316317 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316316 p = 1 := by simpa only [d316317, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35587 p hg
    simpa only [d316317, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316317, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d316317, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35589 (p : Pattern) (guard : d316318 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316318, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d316318, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316317 p = 1 := by simpa only [d316318, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35588 p hg
    simpa only [d316318, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35590 (p : Pattern) (guard : d286110 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d286105 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35585 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35591 (p : Pattern) (guard : d286111 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d286110 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35590 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35592 (p : Pattern) (guard : d286112 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d286111 p = 1 := by simpa only [d286112, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35591 p hg
    simpa only [d286112, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286112, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d286112, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35593 (p : Pattern) (guard : d286113 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286113, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d286113, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286112 p = 1 := by simpa only [d286113, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35592 p hg
    simpa only [d286113, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35594 (p : Pattern) (guard : d316319 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316318 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35589 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286113 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35593 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35595 (p : Pattern) (guard : d316320 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316319 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35594 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35596 (p : Pattern) (guard : d316321 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316320 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35595 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35597 (p : Pattern) (guard : d316322 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316321 p = 1 := by simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35596 p hg
    simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35598 (p : Pattern) (guard : d286118 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d286113 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35593 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35599 (p : Pattern) (guard : d286119 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286118 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35598 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35600 (p : Pattern) (guard : d286120 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286119 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35599 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35601 (p : Pattern) (guard : d286121 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286120 p = 1 := by simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35600 p hg
    simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35602 (p : Pattern) (guard : d316323 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316322 p = 1 := by simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35597 p hg
    simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286121 p = 1 := by simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35601 p hg
    simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35603 (p : Pattern) (guard : d316324 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316323 p = 1 := by simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35602 p hg
    simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35604 (p : Pattern) (guard : d316325 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316324 p = 1 := by simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35603 p hg
    simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35605 (p : Pattern) (guard : d316326 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316325 p = 1 := by simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35604 p hg
    simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35606 (p : Pattern) (guard : d316327 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316326 p = 1 := by simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35605 p hg
    simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35607 (p : Pattern) (guard : d316328 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316328, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316328, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316327 p = 1 := by simpa only [d316328, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35606 p hg
    simpa only [d316328, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35608 (p : Pattern) (guard : d316329 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d316329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316328 p = 1 := by simpa only [d316329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35607 p hg
    simpa only [d316329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35609 (p : Pattern) (guard : d316330 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d316329 p = 1 := by simpa only [d316330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35608 p hg
    simpa only [d316330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d316330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35610 (p : Pattern) (guard : d286105 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35151 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35611 (p : Pattern) (guard : d316315 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316244 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35380 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286105 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35610 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35612 (p : Pattern) (guard : d316316 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316315 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35611 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35613 (p : Pattern) (guard : d316317 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316316 p = 1 := by simpa only [d316317, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35612 p hg
    simpa only [d316317, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316317, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d316317, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35614 (p : Pattern) (guard : d316318 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316318, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d316318, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316317 p = 1 := by simpa only [d316318, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35613 p hg
    simpa only [d316318, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35615 (p : Pattern) (guard : d286110 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d286105 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35610 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35616 (p : Pattern) (guard : d286111 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d286110 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35615 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35617 (p : Pattern) (guard : d286112 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d286111 p = 1 := by simpa only [d286112, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35616 p hg
    simpa only [d286112, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286112, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d286112, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35618 (p : Pattern) (guard : d286113 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286113, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d286113, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286112 p = 1 := by simpa only [d286113, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35617 p hg
    simpa only [d286113, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35619 (p : Pattern) (guard : d316319 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316318 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35614 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286113 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35618 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35620 (p : Pattern) (guard : d316320 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316319 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35619 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35621 (p : Pattern) (guard : d316321 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316320 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35620 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35622 (p : Pattern) (guard : d316322 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316321 p = 1 := by simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35621 p hg
    simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35623 (p : Pattern) (guard : d286118 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d286113 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35618 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35624 (p : Pattern) (guard : d286119 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286118 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35623 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35625 (p : Pattern) (guard : d286120 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286119 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35624 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35626 (p : Pattern) (guard : d286121 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286120 p = 1 := by simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35625 p hg
    simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35627 (p : Pattern) (guard : d316323 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316322 p = 1 := by simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35622 p hg
    simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286121 p = 1 := by simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35626 p hg
    simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35628 (p : Pattern) (guard : d316324 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316323 p = 1 := by simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35627 p hg
    simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35629 (p : Pattern) (guard : d316325 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316324 p = 1 := by simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35628 p hg
    simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35630 (p : Pattern) (guard : d316326 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316325 p = 1 := by simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35629 p hg
    simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35631 (p : Pattern) (guard : d316327 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316326 p = 1 := by simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35630 p hg
    simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35632 (p : Pattern) (guard : d316331 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316321 p = 1 := by simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35596 p hg
    simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35633 (p : Pattern) (guard : d286131 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286120 p = 1 := by simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35600 p hg
    simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35634 (p : Pattern) (guard : d316332 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316331 p = 1 := by simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35632 p hg
    simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286131 p = 1 := by simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35633 p hg
    simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35635 (p : Pattern) (guard : d316333 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316332 p = 1 := by simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35634 p hg
    simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35636 (p : Pattern) (guard : d316334 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316333 p = 1 := by simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35635 p hg
    simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35637 (p : Pattern) (guard : d316335 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316334 p = 1 := by simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35636 p hg
    simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35638 (p : Pattern) (guard : d316336 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316335 p = 1 := by simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35637 p hg
    simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35639 (p : Pattern) (guard : d316337 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d316327 p = 1 := by simpa only [d316337, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35631 p hg
    simpa only [d316337, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316336 p = 1 := by simpa only [d316337, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35638 p hg
    simpa only [d316337, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35640 (p : Pattern) (guard : d316338 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d316328 p = 1 := by simpa only [d316338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35607 p hg
    simpa only [d316338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316337 p = 1 := by simpa only [d316338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35639 p hg
    simpa only [d316338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35641 (p : Pattern) (guard : d316339 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d316338 p = 1 := by simpa only [d316339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35640 p hg
    simpa only [d316339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d316339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35642 (p : Pattern) (guard : d316340 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d316330 p = 1 := by simpa only [d316340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35609 p hg
    simpa only [d316340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316339 p = 1 := by simpa only [d316340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35641 p hg
    simpa only [d316340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35643 (p : Pattern) (guard : d316341 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316320 p = 1 := by simpa only [d316341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35595 p hg
    simpa only [d316341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35644 (p : Pattern) (guard : d316342 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316341 p = 1 := by simpa only [d316342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35643 p hg
    simpa only [d316342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35645 (p : Pattern) (guard : d286143 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286119 p = 1 := by simpa only [d286143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35599 p hg
    simpa only [d286143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35646 (p : Pattern) (guard : d286144 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286143 p = 1 := by simpa only [d286144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35645 p hg
    simpa only [d286144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35647 (p : Pattern) (guard : d316343 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316342 p = 1 := by simpa only [d316343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35644 p hg
    simpa only [d316343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286144 p = 1 := by simpa only [d316343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35646 p hg
    simpa only [d316343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35648 (p : Pattern) (guard : d316344 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316343 p = 1 := by simpa only [d316344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35647 p hg
    simpa only [d316344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35649 (p : Pattern) (guard : d316345 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316344 p = 1 := by simpa only [d316345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35648 p hg
    simpa only [d316345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35650 (p : Pattern) (guard : d316346 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316345 p = 1 := by simpa only [d316346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35649 p hg
    simpa only [d316346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35651 (p : Pattern) (guard : d316347 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316319 p = 1 := by simpa only [d316347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35594 p hg
    simpa only [d316347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35652 (p : Pattern) (guard : d316348 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316347 p = 1 := by simpa only [d316348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35651 p hg
    simpa only [d316348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35653 (p : Pattern) (guard : d316349 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316348 p = 1 := by simpa only [d316349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35652 p hg
    simpa only [d316349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35654 (p : Pattern) (guard : d286152 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286118 p = 1 := by simpa only [d286152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35598 p hg
    simpa only [d286152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35655 (p : Pattern) (guard : d286153 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286152 p = 1 := by simpa only [d286153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35654 p hg
    simpa only [d286153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35656 (p : Pattern) (guard : d286154 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d286154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286153 p = 1 := by simpa only [d286154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35655 p hg
    simpa only [d286154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35657 (p : Pattern) (guard : d316350 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316349 p = 1 := by simpa only [d316350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35653 p hg
    simpa only [d316350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286154 p = 1 := by simpa only [d316350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35656 p hg
    simpa only [d316350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35658 (p : Pattern) (guard : d316351 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316350 p = 1 := by simpa only [d316351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35657 p hg
    simpa only [d316351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35659 (p : Pattern) (guard : d316352 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316351 p = 1 := by simpa only [d316352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35658 p hg
    simpa only [d316352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35660 (p : Pattern) (guard : d316353 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286613 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35318 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35661 (p : Pattern) (guard : d825 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare35662 (p : Pattern) (guard : d5121 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35661 p hg
    simpa only [d5121, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d5121, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35663 (p : Pattern) (guard : d34352 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5121 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35662 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35664 (p : Pattern) (guard : d34353 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d34352 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35663 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35665 (p : Pattern) (guard : d34354 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d34353 p = 1 := by simpa only [d34354, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35664 p hg
    simpa only [d34354, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34354, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d34354, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35666 (p : Pattern) (guard : d316354 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35665 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316230 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35324 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35667 (p : Pattern) (guard : d316355 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316353 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35660 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316354 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35666 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35668 (p : Pattern) (guard : d316356 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316355 p = 1 := by simpa only [d316356, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35667 p hg
    simpa only [d316356, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316356, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d316356, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35669 (p : Pattern) (guard : d316357 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35668 p hg
    simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316233 p = 1 := by simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35327 p hg
    simpa only [d316357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35670 (p : Pattern) (guard : d316358 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316357 p = 1 := by simpa only [d316358, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35669 p hg
    simpa only [d316358, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316358, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316358, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35671 (p : Pattern) (guard : d316359 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316358 p = 1 := by simpa only [d316359, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35670 p hg
    simpa only [d316359, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316359, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316359, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35672 (p : Pattern) (guard : d316360 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316360, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316360, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316359 p = 1 := by simpa only [d316360, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35671 p hg
    simpa only [d316360, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35673 (p : Pattern) (guard : d316361 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316360 p = 1 := by simpa only [d316361, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35672 p hg
    simpa only [d316361, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316361, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316361, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35674 (p : Pattern) (guard : d1540 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare35675 (p : Pattern) (guard : d1541 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35674 p hg
    simpa only [d1541, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d1541, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35676 (p : Pattern) (guard : d258089 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35675 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35677 (p : Pattern) (guard : d316362 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258089 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35676 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35678 (p : Pattern) (guard : d316363 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316362 p = 1 := by simpa only [d316363, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35677 p hg
    simpa only [d316363, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316363, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d316363, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35679 (p : Pattern) (guard : d316364 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316363 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35678 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34875 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35680 (p : Pattern) (guard : d316365 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316364 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35679 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35681 (p : Pattern) (guard : d316366 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316365 p = 1 := by simpa only [d316366, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35680 p hg
    simpa only [d316366, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316366, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d316366, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35682 (p : Pattern) (guard : d316367 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35327 p hg
    simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35681 p hg
    simpa only [d316367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35683 (p : Pattern) (guard : d316368 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316367 p = 1 := by simpa only [d316368, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35682 p hg
    simpa only [d316368, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316368, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316368, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35684 (p : Pattern) (guard : d316369 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316368 p = 1 := by simpa only [d316369, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35683 p hg
    simpa only [d316369, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316369, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316369, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35685 (p : Pattern) (guard : d316370 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316370, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316370, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316369 p = 1 := by simpa only [d316370, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35684 p hg
    simpa only [d316370, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35686 (p : Pattern) (guard : d316371 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316370 p = 1 := by simpa only [d316371, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35685 p hg
    simpa only [d316371, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316371, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316371, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35687 (p : Pattern) (guard : d316372 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316361 p = 1 := by simpa only [d316372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35673 p hg
    simpa only [d316372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316371 p = 1 := by simpa only [d316372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35686 p hg
    simpa only [d316372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35688 (p : Pattern) (guard : d316373 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35318 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35678 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35689 (p : Pattern) (guard : d316374 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316373 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35688 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35690 (p : Pattern) (guard : d316375 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316374 p = 1 := by simpa only [d316375, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35689 p hg
    simpa only [d316375, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316375, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d316375, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35691 (p : Pattern) (guard : d316376 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316375 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35690 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35681 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35692 (p : Pattern) (guard : d316377 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316376 p = 1 := by simpa only [d316377, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35691 p hg
    simpa only [d316377, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316377, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316377, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35693 (p : Pattern) (guard : d316378 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316377 p = 1 := by simpa only [d316378, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35692 p hg
    simpa only [d316378, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316378, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316378, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35694 (p : Pattern) (guard : d316379 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316379, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316379, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316378 p = 1 := by simpa only [d316379, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35693 p hg
    simpa only [d316379, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35695 (p : Pattern) (guard : d316380 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316379 p = 1 := by simpa only [d316380, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35694 p hg
    simpa only [d316380, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316380, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316380, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35696 (p : Pattern) (guard : d316381 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316380 p = 1 := by simpa only [d316381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35695 p hg
    simpa only [d316381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285997 p = 1 := by simpa only [d316381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35340 p hg
    simpa only [d316381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35697 (p : Pattern) (guard : d316382 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316372 p = 1 := by simpa only [d316382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35687 p hg
    simpa only [d316382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316381 p = 1 := by simpa only [d316382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35696 p hg
    simpa only [d316382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35698 (p : Pattern) (guard : d316383 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316382 p = 1 := by simpa only [d316383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35697 p hg
    simpa only [d316383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316240 p = 1 := by simpa only [d316383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35342 p hg
    simpa only [d316383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35699 (p : Pattern) (guard : d316384 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316384, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d316384, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316383 p = 1 := by simpa only [d316384, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35698 p hg
    simpa only [d316384, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35700 (p : Pattern) (guard : d316385 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316385, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d316385, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316384 p = 1 := by simpa only [d316385, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35699 p hg
    simpa only [d316385, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35701 (p : Pattern) (guard : d286188 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d285998 p = 1 := by simpa only [d286188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35341 p hg
    simpa only [d286188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257193 p = 1 := by simpa only [d286188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34891 p hg
    simpa only [d286188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35702 (p : Pattern) (guard : d316386 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316240 p = 1 := by simpa only [d316386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35342 p hg
    simpa only [d316386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286188 p = 1 := by simpa only [d316386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35701 p hg
    simpa only [d316386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35703 (p : Pattern) (guard : d316387 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316387, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d316387, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316386 p = 1 := by simpa only [d316387, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35702 p hg
    simpa only [d316387, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35704 (p : Pattern) (guard : d316388 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316388, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d316388, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316387 p = 1 := by simpa only [d316388, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35703 p hg
    simpa only [d316388, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35705 (p : Pattern) (guard : d316389 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316385 p = 1 := by simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35700 p hg
    simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316388 p = 1 := by simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35704 p hg
    simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35706 (p : Pattern) (guard : d316390 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316389 p = 1 := by simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35705 p hg
    simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316244 p = 1 := by simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35346 p hg
    simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35707 (p : Pattern) (guard : d316391 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316390 p = 1 := by simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35706 p hg
    simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35708 (p : Pattern) (guard : d316392 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316391 p = 1 := by simpa only [d316392, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35707 p hg
    simpa only [d316392, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316392, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d316392, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35709 (p : Pattern) (guard : d316393 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316393, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d316393, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316392 p = 1 := by simpa only [d316393, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35708 p hg
    simpa only [d316393, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35710 (p : Pattern) (guard : d316394 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316393 p = 1 := by simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35709 p hg
    simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316318 p = 1 := by simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35589 p hg
    simpa only [d316394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35711 (p : Pattern) (guard : d316395 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316394 p = 1 := by simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35710 p hg
    simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35712 (p : Pattern) (guard : d316396 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316395 p = 1 := by simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35711 p hg
    simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35713 (p : Pattern) (guard : d316397 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316396 p = 1 := by simpa only [d316397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35712 p hg
    simpa only [d316397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35714 (p : Pattern) (guard : d316398 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316397 p = 1 := by simpa only [d316398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35713 p hg
    simpa only [d316398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316322 p = 1 := by simpa only [d316398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35597 p hg
    simpa only [d316398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35715 (p : Pattern) (guard : d316399 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316398 p = 1 := by simpa only [d316399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35714 p hg
    simpa only [d316399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35716 (p : Pattern) (guard : d316400 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316318 p = 1 := by simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35589 p hg
    simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35717 (p : Pattern) (guard : d316401 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316400 p = 1 := by simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35716 p hg
    simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35718 (p : Pattern) (guard : d316402 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316401 p = 1 := by simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35717 p hg
    simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35719 (p : Pattern) (guard : d316403 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316402 p = 1 := by simpa only [d316403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35718 p hg
    simpa only [d316403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35720 (p : Pattern) (guard : d316404 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316403 p = 1 := by simpa only [d316404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35719 p hg
    simpa only [d316404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35721 (p : Pattern) (guard : d316405 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316404 p = 1 := by simpa only [d316405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35720 p hg
    simpa only [d316405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d316405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35722 (p : Pattern) (guard : d316406 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316399 p = 1 := by simpa only [d316406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35715 p hg
    simpa only [d316406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316405 p = 1 := by simpa only [d316406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35721 p hg
    simpa only [d316406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35723 (p : Pattern) (guard : d316407 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d316352 p = 1 := by simpa only [d316407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35659 p hg
    simpa only [d316407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316406 p = 1 := by simpa only [d316407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35722 p hg
    simpa only [d316407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35724 (p : Pattern) (guard : d316408 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d316346 p = 1 := by simpa only [d316408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35650 p hg
    simpa only [d316408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316407 p = 1 := by simpa only [d316408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35723 p hg
    simpa only [d316408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35725 (p : Pattern) (guard : d316409 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316409, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316409, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316408 p = 1 := by simpa only [d316409, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35724 p hg
    simpa only [d316409, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35726 (p : Pattern) (guard : d316341 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316320 p = 1 := by simpa only [d316341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35620 p hg
    simpa only [d316341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35727 (p : Pattern) (guard : d316342 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316341 p = 1 := by simpa only [d316342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35726 p hg
    simpa only [d316342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35728 (p : Pattern) (guard : d286143 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286119 p = 1 := by simpa only [d286143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35624 p hg
    simpa only [d286143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35729 (p : Pattern) (guard : d286144 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286143 p = 1 := by simpa only [d286144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35728 p hg
    simpa only [d286144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35730 (p : Pattern) (guard : d316343 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316342 p = 1 := by simpa only [d316343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35727 p hg
    simpa only [d316343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286144 p = 1 := by simpa only [d316343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35729 p hg
    simpa only [d316343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35731 (p : Pattern) (guard : d316344 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316343 p = 1 := by simpa only [d316344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35730 p hg
    simpa only [d316344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35732 (p : Pattern) (guard : d316345 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316344 p = 1 := by simpa only [d316345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35731 p hg
    simpa only [d316345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35733 (p : Pattern) (guard : d316346 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316345 p = 1 := by simpa only [d316346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35732 p hg
    simpa only [d316346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35734 (p : Pattern) (guard : d316347 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316319 p = 1 := by simpa only [d316347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35619 p hg
    simpa only [d316347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35735 (p : Pattern) (guard : d316348 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316347 p = 1 := by simpa only [d316348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35734 p hg
    simpa only [d316348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35736 (p : Pattern) (guard : d316349 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316348 p = 1 := by simpa only [d316349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35735 p hg
    simpa only [d316349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35737 (p : Pattern) (guard : d286152 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286118 p = 1 := by simpa only [d286152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35623 p hg
    simpa only [d286152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35738 (p : Pattern) (guard : d286153 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286152 p = 1 := by simpa only [d286153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35737 p hg
    simpa only [d286153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35739 (p : Pattern) (guard : d286154 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286153 p = 1 := by simpa only [d286154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35738 p hg
    simpa only [d286154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35740 (p : Pattern) (guard : d316350 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316349 p = 1 := by simpa only [d316350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35736 p hg
    simpa only [d316350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286154 p = 1 := by simpa only [d316350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35739 p hg
    simpa only [d316350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35741 (p : Pattern) (guard : d316351 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316350 p = 1 := by simpa only [d316351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35740 p hg
    simpa only [d316351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35742 (p : Pattern) (guard : d316352 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316351 p = 1 := by simpa only [d316352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35741 p hg
    simpa only [d316352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35743 (p : Pattern) (guard : d316385 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316385, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d316385, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316384 p = 1 := by simpa only [d316385, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35699 p hg
    simpa only [d316385, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35744 (p : Pattern) (guard : d316388 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316388, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d316388, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316387 p = 1 := by simpa only [d316388, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35703 p hg
    simpa only [d316388, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35745 (p : Pattern) (guard : d316389 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316385 p = 1 := by simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35743 p hg
    simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316388 p = 1 := by simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35744 p hg
    simpa only [d316389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35746 (p : Pattern) (guard : d316390 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316389 p = 1 := by simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35745 p hg
    simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316244 p = 1 := by simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35380 p hg
    simpa only [d316390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35747 (p : Pattern) (guard : d316391 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316390 p = 1 := by simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35746 p hg
    simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d316391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35748 (p : Pattern) (guard : d316392 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316391 p = 1 := by simpa only [d316392, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35747 p hg
    simpa only [d316392, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316392, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d316392, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35749 (p : Pattern) (guard : d316393 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316393, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d316393, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316392 p = 1 := by simpa only [d316393, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35748 p hg
    simpa only [d316393, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
