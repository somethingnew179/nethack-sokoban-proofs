import NetHack.Soko22Hazard87.Compare129
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32500 (p : Pattern) (guard : d205936 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d205936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205894 p = 1 := by simpa only [d205936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32499 p hg
    simpa only [d205936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32501 (p : Pattern) (guard : d205895 p = 1) : d50030 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d205894 p = 1 := by simpa only [d205895, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32172 p hg
    simpa only [d205895, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205895, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d205895, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32502 (p : Pattern) (guard : d205937 p = 1) : d50031 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d205936 p = 1 := by simpa only [d205937, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32500 p hg
    simpa only [d205937, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205895 p = 1 := by simpa only [d205937, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32501 p hg
    simpa only [d205937, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32503 (p : Pattern) (guard : d205892 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d29090 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32123 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32504 (p : Pattern) (guard : d205893 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d205892 p = 1 := by simpa only [d205893, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32503 p hg
    simpa only [d205893, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205893, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32125 p hg
    simpa only [d205893, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32505 (p : Pattern) (guard : d205894 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d205893 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32504 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32506 (p : Pattern) (guard : d205895 p = 1) : d49865 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d205894 p = 1 := by simpa only [d205895, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32505 p hg
    simpa only [d205895, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205895, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d205895, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32507 (p : Pattern) (guard : d205896 p = 1) : d49866 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d205895 p = 1 := by simpa only [d205896, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32506 p hg
    simpa only [d205896, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205896, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d205896, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32508 (p : Pattern) (guard : d205938 p = 1) : d50032 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d205937 p = 1 := by simpa only [d205938, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32502 p hg
    simpa only [d205938, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205896 p = 1 := by simpa only [d205938, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32507 p hg
    simpa only [d205938, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32509 (p : Pattern) (guard : d205939 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d205938 p = 1 := by simpa only [d205939, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32508 p hg
    simpa only [d205939, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205939, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32132 p hg
    simpa only [d205939, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32510 (p : Pattern) (guard : d294734 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205939 p = 1 := by simpa only [d294734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32509 p hg
    simpa only [d294734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32511 (p : Pattern) (guard : d294735 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294551 p = 1 := by simpa only [d294735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32134 p hg
    simpa only [d294735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294734 p = 1 := by simpa only [d294735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32510 p hg
    simpa only [d294735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32512 (p : Pattern) (guard : d294736 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294733 p = 1 := by simpa only [d294736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32496 p hg
    simpa only [d294736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294735 p = 1 := by simpa only [d294736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32511 p hg
    simpa only [d294736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32513 (p : Pattern) (guard : d294737 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294737, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d294737, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294736 p = 1 := by simpa only [d294737, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32512 p hg
    simpa only [d294737, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32514 (p : Pattern) (guard : d294738 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294738, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d294738, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294737 p = 1 := by simpa only [d294738, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32513 p hg
    simpa only [d294738, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32515 (p : Pattern) (guard : d205940 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d205939 p = 1 := by simpa only [d205940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32509 p hg
    simpa only [d205940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d205940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32516 (p : Pattern) (guard : d294739 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294734 p = 1 := by simpa only [d294739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32510 p hg
    simpa only [d294739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205940 p = 1 := by simpa only [d294739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32515 p hg
    simpa only [d294739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32517 (p : Pattern) (guard : d294740 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294735 p = 1 := by simpa only [d294740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32511 p hg
    simpa only [d294740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294739 p = 1 := by simpa only [d294740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32516 p hg
    simpa only [d294740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32518 (p : Pattern) (guard : d294741 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294741, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d294741, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294740 p = 1 := by simpa only [d294741, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32517 p hg
    simpa only [d294741, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32519 (p : Pattern) (guard : d294742 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294742, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d294742, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294741 p = 1 := by simpa only [d294742, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32518 p hg
    simpa only [d294742, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32520 (p : Pattern) (guard : d294743 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294738 p = 1 := by simpa only [d294743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32514 p hg
    simpa only [d294743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294742 p = 1 := by simpa only [d294743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32519 p hg
    simpa only [d294743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32521 (p : Pattern) (guard : d205941 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d205940 p = 1 := by simpa only [d205941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32515 p hg
    simpa only [d205941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d205941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32522 (p : Pattern) (guard : d294744 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294739 p = 1 := by simpa only [d294744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32516 p hg
    simpa only [d294744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205941 p = 1 := by simpa only [d294744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32521 p hg
    simpa only [d294744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32523 (p : Pattern) (guard : d294745 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294745, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d294745, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294744 p = 1 := by simpa only [d294745, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32522 p hg
    simpa only [d294745, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32524 (p : Pattern) (guard : d294746 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294746, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d294746, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294745 p = 1 := by simpa only [d294746, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32523 p hg
    simpa only [d294746, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32525 (p : Pattern) (guard : d294747 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294742 p = 1 := by simpa only [d294747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32519 p hg
    simpa only [d294747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294746 p = 1 := by simpa only [d294747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32524 p hg
    simpa only [d294747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32526 (p : Pattern) (guard : d294748 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294743 p = 1 := by simpa only [d294748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32520 p hg
    simpa only [d294748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294747 p = 1 := by simpa only [d294748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32525 p hg
    simpa only [d294748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32527 (p : Pattern) (guard : d294749 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294748 p = 1 := by simpa only [d294749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32526 p hg
    simpa only [d294749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32528 (p : Pattern) (guard : d294750 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294749 p = 1 := by simpa only [d294750, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32527 p hg
    simpa only [d294750, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294750, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d294750, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32529 (p : Pattern) (guard : d294751 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294751, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294751, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294750 p = 1 := by simpa only [d294751, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32528 p hg
    simpa only [d294751, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32530 (p : Pattern) (guard : d294752 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294746 p = 1 := by simpa only [d294752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32524 p hg
    simpa only [d294752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32531 (p : Pattern) (guard : d294753 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294747 p = 1 := by simpa only [d294753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32525 p hg
    simpa only [d294753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294752 p = 1 := by simpa only [d294753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32530 p hg
    simpa only [d294753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32532 (p : Pattern) (guard : d294754 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294753 p = 1 := by simpa only [d294754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32531 p hg
    simpa only [d294754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32533 (p : Pattern) (guard : d294755 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294754 p = 1 := by simpa only [d294755, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32532 p hg
    simpa only [d294755, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294755, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d294755, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32534 (p : Pattern) (guard : d294756 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294756, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294756, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294755 p = 1 := by simpa only [d294756, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32533 p hg
    simpa only [d294756, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32535 (p : Pattern) (guard : d294757 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294751 p = 1 := by simpa only [d294757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32529 p hg
    simpa only [d294757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294756 p = 1 := by simpa only [d294757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32534 p hg
    simpa only [d294757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32536 (p : Pattern) (guard : d294758 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294757 p = 1 := by simpa only [d294758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32535 p hg
    simpa only [d294758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32537 (p : Pattern) (guard : d294759 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294758 p = 1 := by simpa only [d294759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32536 p hg
    simpa only [d294759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32538 (p : Pattern) (guard : d294760 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294759 p = 1 := by simpa only [d294760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32537 p hg
    simpa only [d294760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32539 (p : Pattern) (guard : d294761 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294752 p = 1 := by simpa only [d294761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32530 p hg
    simpa only [d294761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32540 (p : Pattern) (guard : d294762 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294761 p = 1 := by simpa only [d294762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32539 p hg
    simpa only [d294762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32541 (p : Pattern) (guard : d294763 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294762 p = 1 := by simpa only [d294763, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32540 p hg
    simpa only [d294763, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294763, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d294763, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32542 (p : Pattern) (guard : d294764 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294764, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294764, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294763 p = 1 := by simpa only [d294764, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32541 p hg
    simpa only [d294764, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32543 (p : Pattern) (guard : d294765 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294756 p = 1 := by simpa only [d294765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32534 p hg
    simpa only [d294765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294764 p = 1 := by simpa only [d294765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32542 p hg
    simpa only [d294765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32544 (p : Pattern) (guard : d294766 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294765 p = 1 := by simpa only [d294766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32543 p hg
    simpa only [d294766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32545 (p : Pattern) (guard : d294767 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294766 p = 1 := by simpa only [d294767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32544 p hg
    simpa only [d294767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32546 (p : Pattern) (guard : d294768 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294767 p = 1 := by simpa only [d294768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32545 p hg
    simpa only [d294768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32547 (p : Pattern) (guard : d294769 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294760 p = 1 := by simpa only [d294769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32538 p hg
    simpa only [d294769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294768 p = 1 := by simpa only [d294769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32546 p hg
    simpa only [d294769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32548 (p : Pattern) (guard : d294770 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294769 p = 1 := by simpa only [d294770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32547 p hg
    simpa only [d294770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32549 (p : Pattern) (guard : d294771 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294756 p = 1 := by simpa only [d294771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32534 p hg
    simpa only [d294771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32550 (p : Pattern) (guard : d294772 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294771 p = 1 := by simpa only [d294772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32549 p hg
    simpa only [d294772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32551 (p : Pattern) (guard : d294773 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294772 p = 1 := by simpa only [d294773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32550 p hg
    simpa only [d294773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32552 (p : Pattern) (guard : d294774 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294773 p = 1 := by simpa only [d294774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32551 p hg
    simpa only [d294774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32553 (p : Pattern) (guard : d294775 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294774 p = 1 := by simpa only [d294775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32552 p hg
    simpa only [d294775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32554 (p : Pattern) (guard : d294776 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294775 p = 1 := by simpa only [d294776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32553 p hg
    simpa only [d294776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32555 (p : Pattern) (guard : d294777 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294770 p = 1 := by simpa only [d294777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32548 p hg
    simpa only [d294777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294776 p = 1 := by simpa only [d294777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32554 p hg
    simpa only [d294777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32556 (p : Pattern) (guard : d294778 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294777 p = 1 := by simpa only [d294778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32555 p hg
    simpa only [d294778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32557 (p : Pattern) (guard : d294779 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294778 p = 1 := by simpa only [d294779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32556 p hg
    simpa only [d294779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32558 (p : Pattern) (guard : d294780 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294780, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294780, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294779 p = 1 := by simpa only [d294780, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32557 p hg
    simpa only [d294780, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32559 (p : Pattern) (guard : d294781 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d294781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294780 p = 1 := by simpa only [d294781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32558 p hg
    simpa only [d294781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32560 (p : Pattern) (guard : d294782 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294764 p = 1 := by simpa only [d294782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32542 p hg
    simpa only [d294782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32561 (p : Pattern) (guard : d294783 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294782 p = 1 := by simpa only [d294783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32560 p hg
    simpa only [d294783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32562 (p : Pattern) (guard : d294784 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294783 p = 1 := by simpa only [d294784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32561 p hg
    simpa only [d294784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32563 (p : Pattern) (guard : d294785 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294784 p = 1 := by simpa only [d294785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32562 p hg
    simpa only [d294785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32564 (p : Pattern) (guard : d294786 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294785 p = 1 := by simpa only [d294786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32563 p hg
    simpa only [d294786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32565 (p : Pattern) (guard : d294787 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294786 p = 1 := by simpa only [d294787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32564 p hg
    simpa only [d294787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32566 (p : Pattern) (guard : d294788 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294787 p = 1 := by simpa only [d294788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32565 p hg
    simpa only [d294788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32567 (p : Pattern) (guard : d294789 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294788 p = 1 := by simpa only [d294789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32566 p hg
    simpa only [d294789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32568 (p : Pattern) (guard : d294790 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294789 p = 1 := by simpa only [d294790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32567 p hg
    simpa only [d294790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32569 (p : Pattern) (guard : d294791 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294791, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294791, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294790 p = 1 := by simpa only [d294791, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32568 p hg
    simpa only [d294791, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32570 (p : Pattern) (guard : d294792 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d294792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294791 p = 1 := by simpa only [d294792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32569 p hg
    simpa only [d294792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32571 (p : Pattern) (guard : d294793 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294781 p = 1 := by simpa only [d294793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32559 p hg
    simpa only [d294793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294792 p = 1 := by simpa only [d294793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32570 p hg
    simpa only [d294793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32572 (p : Pattern) (guard : d294794 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294793 p = 1 := by simpa only [d294794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32571 p hg
    simpa only [d294794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d294794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32573 (p : Pattern) (guard : d294795 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294794 p = 1 := by simpa only [d294795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32572 p hg
    simpa only [d294795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d294795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32574 (p : Pattern) (guard : d294796 p = 1) : d50100 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d294795 p = 1 := by simpa only [d294796, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32573 p hg
    simpa only [d294796, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294796, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32160 p hg
    simpa only [d294796, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32575 (p : Pattern) (guard : d294797 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d294727 p = 1 := by simpa only [d294797, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32471 p hg
    simpa only [d294797, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294796 p = 1 := by simpa only [d294797, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32574 p hg
    simpa only [d294797, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32576 (p : Pattern) (guard : d294798 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294797 p = 1 := by simpa only [d294798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32575 p hg
    simpa only [d294798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32577 (p : Pattern) (guard : d294799 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294798 p = 1 := by simpa only [d294799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32576 p hg
    simpa only [d294799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32578 (p : Pattern) (guard : d294800 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294799 p = 1 := by simpa only [d294800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32577 p hg
    simpa only [d294800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32579 (p : Pattern) (guard : d294801 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294800 p = 1 := by simpa only [d294801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32578 p hg
    simpa only [d294801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32580 (p : Pattern) (guard : d294802 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294801 p = 1 := by simpa only [d294802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32579 p hg
    simpa only [d294802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32581 (p : Pattern) (guard : d294803 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294802 p = 1 := by simpa only [d294803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32580 p hg
    simpa only [d294803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32582 (p : Pattern) (guard : d294804 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294803 p = 1 := by simpa only [d294804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32581 p hg
    simpa only [d294804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32583 (p : Pattern) (guard : d294805 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d294583 p = 1 := by simpa only [d294805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32169 p hg
    simpa only [d294805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294804 p = 1 := by simpa only [d294805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32582 p hg
    simpa only [d294805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32584 (p : Pattern) (guard : d293369 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d205998 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32271 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32585 (p : Pattern) (guard : d293370 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293369 p = 1 := by simpa only [d293370, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32584 p hg
    simpa only [d293370, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293370, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31982 p hg
    simpa only [d293370, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32586 (p : Pattern) (guard : d293371 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293370 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32585 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31984 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32587 (p : Pattern) (guard : d293372 p = 1) : d49838 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293371 p = 1 := by simpa only [d293372, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32586 p hg
    simpa only [d293372, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293372, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31986 p hg
    simpa only [d293372, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32588 (p : Pattern) (guard : d293373 p = 1) : d49841 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293372 p = 1 := by simpa only [d293373, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32587 p hg
    simpa only [d293373, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293373, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31988 p hg
    simpa only [d293373, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32589 (p : Pattern) (guard : d293374 p = 1) : d49864 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293374, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31973 p hg
    simpa only [d293374, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293373 p = 1 := by simpa only [d293374, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32588 p hg
    simpa only [d293374, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32590 (p : Pattern) (guard : d293375 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293374 p = 1 := by simpa only [d293375, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32589 p hg
    simpa only [d293375, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293375, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31991 p hg
    simpa only [d293375, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32591 (p : Pattern) (guard : d294806 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293375 p = 1 := by simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32590 p hg
    simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32592 (p : Pattern) (guard : d294807 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294654 p = 1 := by simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32279 p hg
    simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294806 p = 1 := by simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32591 p hg
    simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32593 (p : Pattern) (guard : d293631 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293375 p = 1 := by simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32590 p hg
    simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32594 (p : Pattern) (guard : d294808 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294806 p = 1 := by simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32591 p hg
    simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293631 p = 1 := by simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32593 p hg
    simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32595 (p : Pattern) (guard : d294809 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294807 p = 1 := by simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32592 p hg
    simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294808 p = 1 := by simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32594 p hg
    simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32596 (p : Pattern) (guard : d294810 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294810, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d294810, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294809 p = 1 := by simpa only [d294810, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32595 p hg
    simpa only [d294810, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32597 (p : Pattern) (guard : d294811 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294811, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d294811, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294810 p = 1 := by simpa only [d294811, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32596 p hg
    simpa only [d294811, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32598 (p : Pattern) (guard : d294812 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293631 p = 1 := by simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32593 p hg
    simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32599 (p : Pattern) (guard : d294813 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294808 p = 1 := by simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32594 p hg
    simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294812 p = 1 := by simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32598 p hg
    simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32600 (p : Pattern) (guard : d294814 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294814, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d294814, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294813 p = 1 := by simpa only [d294814, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32599 p hg
    simpa only [d294814, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32601 (p : Pattern) (guard : d294815 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294815, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d294815, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294814 p = 1 := by simpa only [d294815, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32600 p hg
    simpa only [d294815, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32602 (p : Pattern) (guard : d294816 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294811 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32597 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294815 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32601 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32603 (p : Pattern) (guard : d294817 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294815 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32601 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32604 (p : Pattern) (guard : d294818 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294816 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32602 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294817 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32603 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32605 (p : Pattern) (guard : d294819 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294818 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32604 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32606 (p : Pattern) (guard : d294820 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294819 p = 1 := by simpa only [d294820, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32605 p hg
    simpa only [d294820, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294820, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294820, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32607 (p : Pattern) (guard : d294821 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294821, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294821, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294820 p = 1 := by simpa only [d294821, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32606 p hg
    simpa only [d294821, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32608 (p : Pattern) (guard : d294822 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294817 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32603 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32609 (p : Pattern) (guard : d294823 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294822 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32608 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32610 (p : Pattern) (guard : d294824 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294823 p = 1 := by simpa only [d294824, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32609 p hg
    simpa only [d294824, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294824, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294824, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32611 (p : Pattern) (guard : d294825 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294825, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294825, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294824 p = 1 := by simpa only [d294825, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32610 p hg
    simpa only [d294825, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32612 (p : Pattern) (guard : d294826 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294821 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32607 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294825 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32611 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32613 (p : Pattern) (guard : d294827 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294826 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32612 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32614 (p : Pattern) (guard : d294828 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294827 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32613 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32615 (p : Pattern) (guard : d294829 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294828 p = 1 := by simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32614 p hg
    simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32616 (p : Pattern) (guard : d294830 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294825 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32611 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32617 (p : Pattern) (guard : d294831 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294830 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32616 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32618 (p : Pattern) (guard : d294832 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294831 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32617 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32619 (p : Pattern) (guard : d294833 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294832 p = 1 := by simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32618 p hg
    simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32620 (p : Pattern) (guard : d294834 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294829 p = 1 := by simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32615 p hg
    simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294833 p = 1 := by simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32619 p hg
    simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32621 (p : Pattern) (guard : d294835 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294834 p = 1 := by simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32620 p hg
    simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32622 (p : Pattern) (guard : d294836 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294835 p = 1 := by simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32621 p hg
    simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32623 (p : Pattern) (guard : d294837 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294836 p = 1 := by simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32622 p hg
    simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32624 (p : Pattern) (guard : d294838 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294837 p = 1 := by simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32623 p hg
    simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32625 (p : Pattern) (guard : d294839 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294839, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294839, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294838 p = 1 := by simpa only [d294839, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32624 p hg
    simpa only [d294839, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32626 (p : Pattern) (guard : d294840 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294839 p = 1 := by simpa only [d294840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32625 p hg
    simpa only [d294840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32627 (p : Pattern) (guard : d294841 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294840 p = 1 := by simpa only [d294841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32626 p hg
    simpa only [d294841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32628 (p : Pattern) (guard : d294811 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294811, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d294811, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294810 p = 1 := by simpa only [d294811, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32596 p hg
    simpa only [d294811, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32629 (p : Pattern) (guard : d294815 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294815, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d294815, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294814 p = 1 := by simpa only [d294815, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32600 p hg
    simpa only [d294815, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32630 (p : Pattern) (guard : d294816 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294811 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32628 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294815 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32629 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32631 (p : Pattern) (guard : d294817 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294815 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32629 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32632 (p : Pattern) (guard : d294818 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294816 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32630 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294817 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32631 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32633 (p : Pattern) (guard : d294819 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294818 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32632 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32634 (p : Pattern) (guard : d294820 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294819 p = 1 := by simpa only [d294820, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32633 p hg
    simpa only [d294820, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294820, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294820, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32635 (p : Pattern) (guard : d294821 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294821, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d294821, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294820 p = 1 := by simpa only [d294821, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32634 p hg
    simpa only [d294821, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32636 (p : Pattern) (guard : d294822 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294817 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32631 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32637 (p : Pattern) (guard : d294823 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294822 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32636 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32638 (p : Pattern) (guard : d294824 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294823 p = 1 := by simpa only [d294824, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32637 p hg
    simpa only [d294824, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294824, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294824, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32639 (p : Pattern) (guard : d294825 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294825, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d294825, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294824 p = 1 := by simpa only [d294825, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32638 p hg
    simpa only [d294825, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32640 (p : Pattern) (guard : d294826 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294821 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32635 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294825 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32639 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32641 (p : Pattern) (guard : d294827 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294826 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32640 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32642 (p : Pattern) (guard : d294828 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294827 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32641 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32643 (p : Pattern) (guard : d294829 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294828 p = 1 := by simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32642 p hg
    simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32644 (p : Pattern) (guard : d294830 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294825 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32639 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32645 (p : Pattern) (guard : d294831 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294830 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32644 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32646 (p : Pattern) (guard : d294832 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294831 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32645 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32647 (p : Pattern) (guard : d294833 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294832 p = 1 := by simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32646 p hg
    simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32648 (p : Pattern) (guard : d294834 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294829 p = 1 := by simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32643 p hg
    simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294833 p = 1 := by simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32647 p hg
    simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32649 (p : Pattern) (guard : d294835 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294834 p = 1 := by simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32648 p hg
    simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32650 (p : Pattern) (guard : d294836 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294835 p = 1 := by simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32649 p hg
    simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32651 (p : Pattern) (guard : d294837 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294836 p = 1 := by simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32650 p hg
    simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32652 (p : Pattern) (guard : d294838 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294837 p = 1 := by simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32651 p hg
    simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32653 (p : Pattern) (guard : d294842 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294828 p = 1 := by simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32614 p hg
    simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32654 (p : Pattern) (guard : d294843 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294832 p = 1 := by simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32618 p hg
    simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32655 (p : Pattern) (guard : d294844 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294842 p = 1 := by simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32653 p hg
    simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294843 p = 1 := by simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32654 p hg
    simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32656 (p : Pattern) (guard : d294845 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294844 p = 1 := by simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32655 p hg
    simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32657 (p : Pattern) (guard : d294846 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294845 p = 1 := by simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32656 p hg
    simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32658 (p : Pattern) (guard : d294847 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294846 p = 1 := by simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32657 p hg
    simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32659 (p : Pattern) (guard : d294848 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294847 p = 1 := by simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32658 p hg
    simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32660 (p : Pattern) (guard : d294849 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294838 p = 1 := by simpa only [d294849, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32652 p hg
    simpa only [d294849, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294848 p = 1 := by simpa only [d294849, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32659 p hg
    simpa only [d294849, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32661 (p : Pattern) (guard : d294850 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d294839 p = 1 := by simpa only [d294850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32625 p hg
    simpa only [d294850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294849 p = 1 := by simpa only [d294850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32660 p hg
    simpa only [d294850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32662 (p : Pattern) (guard : d294851 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294850 p = 1 := by simpa only [d294851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32661 p hg
    simpa only [d294851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32663 (p : Pattern) (guard : d294852 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294841 p = 1 := by simpa only [d294852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32627 p hg
    simpa only [d294852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294851 p = 1 := by simpa only [d294852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32662 p hg
    simpa only [d294852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32664 (p : Pattern) (guard : d294853 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294827 p = 1 := by simpa only [d294853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32613 p hg
    simpa only [d294853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32665 (p : Pattern) (guard : d294854 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294853 p = 1 := by simpa only [d294854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32664 p hg
    simpa only [d294854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32666 (p : Pattern) (guard : d294855 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294831 p = 1 := by simpa only [d294855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32617 p hg
    simpa only [d294855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32667 (p : Pattern) (guard : d294856 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294855 p = 1 := by simpa only [d294856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32666 p hg
    simpa only [d294856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32668 (p : Pattern) (guard : d294857 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294854 p = 1 := by simpa only [d294857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32665 p hg
    simpa only [d294857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294856 p = 1 := by simpa only [d294857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32667 p hg
    simpa only [d294857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32669 (p : Pattern) (guard : d294858 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294857 p = 1 := by simpa only [d294858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32668 p hg
    simpa only [d294858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32670 (p : Pattern) (guard : d294859 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294858 p = 1 := by simpa only [d294859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32669 p hg
    simpa only [d294859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32671 (p : Pattern) (guard : d294860 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294859 p = 1 := by simpa only [d294860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32670 p hg
    simpa only [d294860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32672 (p : Pattern) (guard : d294861 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294826 p = 1 := by simpa only [d294861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32612 p hg
    simpa only [d294861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32673 (p : Pattern) (guard : d294862 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294861 p = 1 := by simpa only [d294862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d294862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32674 (p : Pattern) (guard : d294863 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294862 p = 1 := by simpa only [d294863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32673 p hg
    simpa only [d294863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32675 (p : Pattern) (guard : d294864 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294830 p = 1 := by simpa only [d294864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32616 p hg
    simpa only [d294864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32676 (p : Pattern) (guard : d294865 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294864 p = 1 := by simpa only [d294865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32675 p hg
    simpa only [d294865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32677 (p : Pattern) (guard : d294866 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294865 p = 1 := by simpa only [d294866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32676 p hg
    simpa only [d294866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32678 (p : Pattern) (guard : d294867 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294863 p = 1 := by simpa only [d294867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32674 p hg
    simpa only [d294867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294866 p = 1 := by simpa only [d294867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32677 p hg
    simpa only [d294867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32679 (p : Pattern) (guard : d294868 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294867 p = 1 := by simpa only [d294868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32678 p hg
    simpa only [d294868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32680 (p : Pattern) (guard : d294869 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294868 p = 1 := by simpa only [d294869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32679 p hg
    simpa only [d294869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32681 (p : Pattern) (guard : d1532 p = 1) : d47617 p ≤ (1 : Int) + d47617 p := by
  omega
theorem compare32682 (p : Pattern) (guard : d25764 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d25764, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32681 p hg
    simpa only [d25764, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25764, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31976 p hg
    simpa only [d25764, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32683 (p : Pattern) (guard : d25765 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25764 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32682 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32684 (p : Pattern) (guard : d25766 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25765 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32683 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32685 (p : Pattern) (guard : d31739 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25766 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32684 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32686 (p : Pattern) (guard : d294870 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31739 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32685 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32687 (p : Pattern) (guard : d294871 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294870 p = 1 := by simpa only [d294871, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32686 p hg
    simpa only [d294871, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294871, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31982 p hg
    simpa only [d294871, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32688 (p : Pattern) (guard : d294872 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294871 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32687 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31984 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32689 (p : Pattern) (guard : d294873 p = 1) : d49838 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294872 p = 1 := by simpa only [d294873, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32688 p hg
    simpa only [d294873, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294873, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31986 p hg
    simpa only [d294873, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32690 (p : Pattern) (guard : d294874 p = 1) : d49841 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294873 p = 1 := by simpa only [d294874, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32689 p hg
    simpa only [d294874, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294874, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31988 p hg
    simpa only [d294874, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32691 (p : Pattern) (guard : d294875 p = 1) : d49864 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294875, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31973 p hg
    simpa only [d294875, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294874 p = 1 := by simpa only [d294875, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32690 p hg
    simpa only [d294875, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32692 (p : Pattern) (guard : d294876 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294875 p = 1 := by simpa only [d294876, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32691 p hg
    simpa only [d294876, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294876, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31991 p hg
    simpa only [d294876, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32693 (p : Pattern) (guard : d294877 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294876 p = 1 := by simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32692 p hg
    simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32694 (p : Pattern) (guard : d294878 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294877 p = 1 := by simpa only [d294878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32693 p hg
    simpa only [d294878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32695 (p : Pattern) (guard : d294879 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294878 p = 1 := by simpa only [d294879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32694 p hg
    simpa only [d294879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294807 p = 1 := by simpa only [d294879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32592 p hg
    simpa only [d294879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32696 (p : Pattern) (guard : d294880 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294880, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d294880, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294879 p = 1 := by simpa only [d294880, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32695 p hg
    simpa only [d294880, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32697 (p : Pattern) (guard : d294881 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294881, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d294881, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294880 p = 1 := by simpa only [d294881, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32696 p hg
    simpa only [d294881, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32698 (p : Pattern) (guard : d294882 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294881 p = 1 := by simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32697 p hg
    simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294811 p = 1 := by simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32597 p hg
    simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32699 (p : Pattern) (guard : d294883 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294882 p = 1 := by simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32698 p hg
    simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294816 p = 1 := by simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32602 p hg
    simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32700 (p : Pattern) (guard : d294884 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294883 p = 1 := by simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32699 p hg
    simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32701 (p : Pattern) (guard : d294885 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294884 p = 1 := by simpa only [d294885, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32700 p hg
    simpa only [d294885, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294885, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294885, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32702 (p : Pattern) (guard : d294886 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294886, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294886, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294885 p = 1 := by simpa only [d294886, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32701 p hg
    simpa only [d294886, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32703 (p : Pattern) (guard : d294887 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294886 p = 1 := by simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32702 p hg
    simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294821 p = 1 := by simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32607 p hg
    simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32704 (p : Pattern) (guard : d294888 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294887 p = 1 := by simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32703 p hg
    simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32705 (p : Pattern) (guard : d294889 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294888 p = 1 := by simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32704 p hg
    simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32706 (p : Pattern) (guard : d294890 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294889 p = 1 := by simpa only [d294890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32705 p hg
    simpa only [d294890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32707 (p : Pattern) (guard : d294891 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294890 p = 1 := by simpa only [d294891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32706 p hg
    simpa only [d294891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294829 p = 1 := by simpa only [d294891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32615 p hg
    simpa only [d294891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32708 (p : Pattern) (guard : d294892 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294891 p = 1 := by simpa only [d294892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32707 p hg
    simpa only [d294892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32709 (p : Pattern) (guard : d294893 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294821 p = 1 := by simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32607 p hg
    simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32710 (p : Pattern) (guard : d294894 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294893 p = 1 := by simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32709 p hg
    simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32711 (p : Pattern) (guard : d294895 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294894 p = 1 := by simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32710 p hg
    simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32712 (p : Pattern) (guard : d294896 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294895 p = 1 := by simpa only [d294896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32711 p hg
    simpa only [d294896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32713 (p : Pattern) (guard : d294897 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294896 p = 1 := by simpa only [d294897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32712 p hg
    simpa only [d294897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32714 (p : Pattern) (guard : d294898 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294897 p = 1 := by simpa only [d294898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32713 p hg
    simpa only [d294898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32715 (p : Pattern) (guard : d294899 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294892 p = 1 := by simpa only [d294899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32708 p hg
    simpa only [d294899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294898 p = 1 := by simpa only [d294899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32714 p hg
    simpa only [d294899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32716 (p : Pattern) (guard : d294900 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d294869 p = 1 := by simpa only [d294900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32680 p hg
    simpa only [d294900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294899 p = 1 := by simpa only [d294900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32715 p hg
    simpa only [d294900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32717 (p : Pattern) (guard : d294901 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d294860 p = 1 := by simpa only [d294901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32671 p hg
    simpa only [d294901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294900 p = 1 := by simpa only [d294901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32716 p hg
    simpa only [d294901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32718 (p : Pattern) (guard : d294902 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294902, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294902, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294901 p = 1 := by simpa only [d294902, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32717 p hg
    simpa only [d294902, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32719 (p : Pattern) (guard : d294853 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294827 p = 1 := by simpa only [d294853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32641 p hg
    simpa only [d294853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32720 (p : Pattern) (guard : d294854 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294853 p = 1 := by simpa only [d294854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32719 p hg
    simpa only [d294854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32721 (p : Pattern) (guard : d294855 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294831 p = 1 := by simpa only [d294855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32645 p hg
    simpa only [d294855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32722 (p : Pattern) (guard : d294856 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294855 p = 1 := by simpa only [d294856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32721 p hg
    simpa only [d294856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32723 (p : Pattern) (guard : d294857 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294854 p = 1 := by simpa only [d294857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32720 p hg
    simpa only [d294857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294856 p = 1 := by simpa only [d294857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32722 p hg
    simpa only [d294857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32724 (p : Pattern) (guard : d294858 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294857 p = 1 := by simpa only [d294858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32723 p hg
    simpa only [d294858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32725 (p : Pattern) (guard : d294859 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294858 p = 1 := by simpa only [d294859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32724 p hg
    simpa only [d294859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32726 (p : Pattern) (guard : d294860 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294859 p = 1 := by simpa only [d294860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32725 p hg
    simpa only [d294860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32727 (p : Pattern) (guard : d294861 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294826 p = 1 := by simpa only [d294861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32640 p hg
    simpa only [d294861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32728 (p : Pattern) (guard : d294862 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294861 p = 1 := by simpa only [d294862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32727 p hg
    simpa only [d294862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32729 (p : Pattern) (guard : d294863 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294862 p = 1 := by simpa only [d294863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32728 p hg
    simpa only [d294863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32730 (p : Pattern) (guard : d294864 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294830 p = 1 := by simpa only [d294864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32644 p hg
    simpa only [d294864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32731 (p : Pattern) (guard : d294865 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294864 p = 1 := by simpa only [d294865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32730 p hg
    simpa only [d294865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32732 (p : Pattern) (guard : d294866 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294865 p = 1 := by simpa only [d294866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32731 p hg
    simpa only [d294866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32733 (p : Pattern) (guard : d294867 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294863 p = 1 := by simpa only [d294867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32729 p hg
    simpa only [d294867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294866 p = 1 := by simpa only [d294867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32732 p hg
    simpa only [d294867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32734 (p : Pattern) (guard : d294868 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294867 p = 1 := by simpa only [d294868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32733 p hg
    simpa only [d294868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32735 (p : Pattern) (guard : d294869 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294868 p = 1 := by simpa only [d294869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32734 p hg
    simpa only [d294869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32736 (p : Pattern) (guard : d294881 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294881, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d294881, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294880 p = 1 := by simpa only [d294881, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32696 p hg
    simpa only [d294881, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32737 (p : Pattern) (guard : d294882 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294881 p = 1 := by simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32736 p hg
    simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294811 p = 1 := by simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32628 p hg
    simpa only [d294882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32738 (p : Pattern) (guard : d294883 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294882 p = 1 := by simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32737 p hg
    simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294816 p = 1 := by simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32630 p hg
    simpa only [d294883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32739 (p : Pattern) (guard : d294884 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294883 p = 1 := by simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32738 p hg
    simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32740 (p : Pattern) (guard : d294885 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294884 p = 1 := by simpa only [d294885, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32739 p hg
    simpa only [d294885, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294885, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294885, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32741 (p : Pattern) (guard : d294886 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294886, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d294886, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294885 p = 1 := by simpa only [d294886, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32740 p hg
    simpa only [d294886, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32742 (p : Pattern) (guard : d294887 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294886 p = 1 := by simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32741 p hg
    simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294821 p = 1 := by simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32635 p hg
    simpa only [d294887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32743 (p : Pattern) (guard : d294888 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294887 p = 1 := by simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32742 p hg
    simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32744 (p : Pattern) (guard : d294889 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294888 p = 1 := by simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32743 p hg
    simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32745 (p : Pattern) (guard : d294890 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294889 p = 1 := by simpa only [d294890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32744 p hg
    simpa only [d294890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32746 (p : Pattern) (guard : d294891 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294890 p = 1 := by simpa only [d294891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32745 p hg
    simpa only [d294891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294829 p = 1 := by simpa only [d294891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32643 p hg
    simpa only [d294891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32747 (p : Pattern) (guard : d294892 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294891 p = 1 := by simpa only [d294892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32746 p hg
    simpa only [d294892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32748 (p : Pattern) (guard : d294893 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294821 p = 1 := by simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32635 p hg
    simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32749 (p : Pattern) (guard : d294894 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294893 p = 1 := by simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32748 p hg
    simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294894, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
