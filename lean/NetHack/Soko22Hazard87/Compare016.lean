import NetHack.Soko22Hazard87.Compare015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4000 (p : Pattern) (guard : d62791 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 245 with
  | false =>
    have hg : d62790 p = 1 := by simpa only [d62791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3999 p hg
    simpa only [d62791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4001 (p : Pattern) (guard : d62792 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 200 with
  | false =>
    have hg : d62791 p = 1 := by simpa only [d62792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4000 p hg
    simpa only [d62792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4002 (p : Pattern) (guard : d62793 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 199 with
  | false =>
    have hg : d62792 p = 1 := by simpa only [d62793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4001 p hg
    simpa only [d62793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4003 (p : Pattern) (guard : d62794 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 186 with
  | false =>
    have hg : d62793 p = 1 := by simpa only [d62794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4002 p hg
    simpa only [d62794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4004 (p : Pattern) (guard : d62795 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 185 with
  | false =>
    have hg : d62794 p = 1 := by simpa only [d62795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4003 p hg
    simpa only [d62795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4005 (p : Pattern) (guard : d62796 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 184 with
  | false =>
    have hg : d62795 p = 1 := by simpa only [d62796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4004 p hg
    simpa only [d62796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4006 (p : Pattern) (guard : d62797 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 181 with
  | false =>
    have hg : d62796 p = 1 := by simpa only [d62797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4005 p hg
    simpa only [d62797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4007 (p : Pattern) (guard : d62798 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 177 with
  | false =>
    have hg : d62797 p = 1 := by simpa only [d62798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4006 p hg
    simpa only [d62798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4008 (p : Pattern) (guard : d62799 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 164 with
  | false =>
    have hg : d62798 p = 1 := by simpa only [d62799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4007 p hg
    simpa only [d62799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4009 (p : Pattern) (guard : d62800 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 156 with
  | false =>
    have hg : d62799 p = 1 := by simpa only [d62800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4008 p hg
    simpa only [d62800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4010 (p : Pattern) (guard : d62801 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 155 with
  | false =>
    have hg : d62800 p = 1 := by simpa only [d62801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4009 p hg
    simpa only [d62801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4011 (p : Pattern) (guard : d62802 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 134 with
  | false =>
    have hg : d62801 p = 1 := by simpa only [d62802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4010 p hg
    simpa only [d62802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4012 (p : Pattern) (guard : d62803 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 133 with
  | false =>
    have hg : d62802 p = 1 := by simpa only [d62803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4011 p hg
    simpa only [d62803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4013 (p : Pattern) (guard : d62804 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 120 with
  | false =>
    have hg : d62803 p = 1 := by simpa only [d62804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4012 p hg
    simpa only [d62804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4014 (p : Pattern) (guard : d62805 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 118 with
  | false =>
    have hg : d62804 p = 1 := by simpa only [d62805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4013 p hg
    simpa only [d62805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4015 (p : Pattern) (guard : d62806 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 114 with
  | false =>
    have hg : d62805 p = 1 := by simpa only [d62806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4014 p hg
    simpa only [d62806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4016 (p : Pattern) (guard : d62807 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 111 with
  | false =>
    have hg : d62806 p = 1 := by simpa only [d62807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4015 p hg
    simpa only [d62807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4017 (p : Pattern) (guard : d62808 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 98 with
  | false =>
    have hg : d62807 p = 1 := by simpa only [d62808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4016 p hg
    simpa only [d62808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4018 (p : Pattern) (guard : d62809 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 97 with
  | false =>
    have hg : d62808 p = 1 := by simpa only [d62809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4017 p hg
    simpa only [d62809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4019 (p : Pattern) (guard : d62810 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 94 with
  | false =>
    have hg : d62809 p = 1 := by simpa only [d62810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4018 p hg
    simpa only [d62810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4020 (p : Pattern) (guard : d62811 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 76 with
  | false =>
    have hg : d62810 p = 1 := by simpa only [d62811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4019 p hg
    simpa only [d62811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4021 (p : Pattern) (guard : d62812 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 67 with
  | false =>
    have hg : d62811 p = 1 := by simpa only [d62812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4020 p hg
    simpa only [d62812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4022 (p : Pattern) (guard : d62813 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 52 with
  | false =>
    have hg : d62812 p = 1 := by simpa only [d62813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4021 p hg
    simpa only [d62813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4023 (p : Pattern) (guard : d62814 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 47 with
  | false =>
    have hg : d62813 p = 1 := by simpa only [d62814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4022 p hg
    simpa only [d62814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4024 (p : Pattern) (guard : d62815 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 46 with
  | false =>
    have hg : d62814 p = 1 := by simpa only [d62815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4023 p hg
    simpa only [d62815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4025 (p : Pattern) (guard : d62816 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 45 with
  | false =>
    have hg : d62815 p = 1 := by simpa only [d62816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4024 p hg
    simpa only [d62816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4026 (p : Pattern) (guard : d62817 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 30 with
  | false =>
    have hg : d62816 p = 1 := by simpa only [d62817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4025 p hg
    simpa only [d62817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4027 (p : Pattern) (guard : d62818 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 29 with
  | false =>
    have hg : d62817 p = 1 := by simpa only [d62818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4026 p hg
    simpa only [d62818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4028 (p : Pattern) (guard : d62819 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 28 with
  | false =>
    have hg : d62818 p = 1 := by simpa only [d62819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4027 p hg
    simpa only [d62819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4029 (p : Pattern) (guard : d62820 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 27 with
  | false =>
    have hg : d62819 p = 1 := by simpa only [d62820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4028 p hg
    simpa only [d62820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4030 (p : Pattern) (guard : d62821 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 25 with
  | false =>
    have hg : d62820 p = 1 := by simpa only [d62821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4029 p hg
    simpa only [d62821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4031 (p : Pattern) (guard : d66943 p = 1) : d47911 p ≤ (0 : Int) + d47911 p := by
  omega
theorem compare4032 (p : Pattern) (guard : d68219 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare4033 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d72606 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4034 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d72606 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4035 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d48087 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4036 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d48087 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4037 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d48083 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4038 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d48083 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4039 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4040 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4041 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-1 : Int) + d48083 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4042 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-2 : Int) + d48083 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4043 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4044 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4045 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4046 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-2 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4047 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-1 : Int) + d73782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4048 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-2 : Int) + d73782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4049 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4050 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4051 (p : Pattern) (guard : d0 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4052 (p : Pattern) (guard : d0 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4053 (p : Pattern) (guard : d0 p = 1) : d48045 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4054 (p : Pattern) (guard : d3497 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d47 p = 1 := by simpa only [d3497, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2516 p hg
    simpa only [d3497, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d3497, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d3497, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4055 (p : Pattern) (guard : d3498 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d3497 p = 1 := by simpa only [d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4054 p hg
    simpa only [d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4056 (p : Pattern) (guard : d3499 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d3498 p = 1 := by simpa only [d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4055 p hg
    simpa only [d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4057 (p : Pattern) (guard : d3500 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d3499 p = 1 := by simpa only [d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4056 p hg
    simpa only [d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4058 (p : Pattern) (guard : d3501 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d3500 p = 1 := by simpa only [d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4057 p hg
    simpa only [d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4059 (p : Pattern) (guard : d0 p = 1) : d48084 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4060 (p : Pattern) (guard : d3502 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d3501 p = 1 := by simpa only [d3502, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4058 p hg
    simpa only [d3502, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d3502, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d3502, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4061 (p : Pattern) (guard : d0 p = 1) : d48086 p ≤ (0 : Int) + d47865 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4062 (p : Pattern) (guard : d3503 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d3502 p = 1 := by simpa only [d3503, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4060 p hg
    simpa only [d3503, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d3503, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d3503, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4063 (p : Pattern) (guard : d3504 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d3503 p = 1 := by simpa only [d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4062 p hg
    simpa only [d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4064 (p : Pattern) (guard : d3505 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d3504 p = 1 := by simpa only [d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4063 p hg
    simpa only [d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4065 (p : Pattern) (guard : d3506 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d3505 p = 1 := by simpa only [d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4066 (p : Pattern) (guard : d3507 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d3506 p = 1 := by simpa only [d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4065 p hg
    simpa only [d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4067 (p : Pattern) (guard : d213 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d213, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2319 p hg
    simpa only [d213, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d213, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d213, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4068 (p : Pattern) (guard : d2525 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d213 p = 1 := by simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4067 p hg
    simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4069 (p : Pattern) (guard : d2526 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2525 p = 1 := by simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4068 p hg
    simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4070 (p : Pattern) (guard : d3508 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2526 p = 1 := by simpa only [d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4069 p hg
    simpa only [d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4071 (p : Pattern) (guard : d62554 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51642 p = 1 := by simpa only [d62554, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d62554, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62554, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d62554, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4072 (p : Pattern) (guard : d62555 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62554 p = 1 := by simpa only [d62555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4071 p hg
    simpa only [d62555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4073 (p : Pattern) (guard : d72921 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d62555 p = 1 := by simpa only [d72921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4072 p hg
    simpa only [d72921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4074 (p : Pattern) (guard : d72922 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d72921 p = 1 := by simpa only [d72922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4073 p hg
    simpa only [d72922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4075 (p : Pattern) (guard : d72923 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d3508 p = 1 := by simpa only [d72923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4070 p hg
    simpa only [d72923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72922 p = 1 := by simpa only [d72923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4074 p hg
    simpa only [d72923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4076 (p : Pattern) (guard : d72924 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d72923 p = 1 := by simpa only [d72924, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4075 p hg
    simpa only [d72924, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72924, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d72924, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4077 (p : Pattern) (guard : d72925 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d72924 p = 1 := by simpa only [d72925, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4076 p hg
    simpa only [d72925, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72925, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d72925, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4078 (p : Pattern) (guard : d72926 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72925 p = 1 := by simpa only [d72926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4077 p hg
    simpa only [d72926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4079 (p : Pattern) (guard : d72927 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72926 p = 1 := by simpa only [d72927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4078 p hg
    simpa only [d72927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4080 (p : Pattern) (guard : d72928 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72927 p = 1 := by simpa only [d72928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4079 p hg
    simpa only [d72928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4081 (p : Pattern) (guard : d72929 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72928 p = 1 := by simpa only [d72929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d72929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4082 (p : Pattern) (guard : d72930 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d3507 p = 1 := by simpa only [d72930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4066 p hg
    simpa only [d72930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72929 p = 1 := by simpa only [d72930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4081 p hg
    simpa only [d72930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4083 (p : Pattern) (guard : d2536 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d2536, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2334 p hg
    simpa only [d2536, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2536, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d2536, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4084 (p : Pattern) (guard : d2537 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2536 p = 1 := by simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4083 p hg
    simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4085 (p : Pattern) (guard : d2538 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2537 p = 1 := by simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4086 (p : Pattern) (guard : d3521 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2538 p = 1 := by simpa only [d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4085 p hg
    simpa only [d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4087 (p : Pattern) (guard : d62566 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51659 p = 1 := by simpa only [d62566, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2640 p hg
    simpa only [d62566, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62566, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d62566, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4088 (p : Pattern) (guard : d62567 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62566 p = 1 := by simpa only [d62567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4087 p hg
    simpa only [d62567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4089 (p : Pattern) (guard : d72931 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d62567 p = 1 := by simpa only [d72931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4088 p hg
    simpa only [d72931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4090 (p : Pattern) (guard : d72932 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d72931 p = 1 := by simpa only [d72932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4089 p hg
    simpa only [d72932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4091 (p : Pattern) (guard : d72933 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d3521 p = 1 := by simpa only [d72933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4086 p hg
    simpa only [d72933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72932 p = 1 := by simpa only [d72933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4090 p hg
    simpa only [d72933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4092 (p : Pattern) (guard : d72934 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d72933 p = 1 := by simpa only [d72934, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4091 p hg
    simpa only [d72934, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72934, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d72934, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4093 (p : Pattern) (guard : d72935 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d72934 p = 1 := by simpa only [d72935, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4092 p hg
    simpa only [d72935, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72935, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d72935, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4094 (p : Pattern) (guard : d72936 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72935 p = 1 := by simpa only [d72936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4093 p hg
    simpa only [d72936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4095 (p : Pattern) (guard : d72937 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72936 p = 1 := by simpa only [d72937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4094 p hg
    simpa only [d72937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4096 (p : Pattern) (guard : d72938 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72937 p = 1 := by simpa only [d72938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4095 p hg
    simpa only [d72938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4097 (p : Pattern) (guard : d72939 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72938 p = 1 := by simpa only [d72939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4096 p hg
    simpa only [d72939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4098 (p : Pattern) (guard : d72940 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72939 p = 1 := by simpa only [d72940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4097 p hg
    simpa only [d72940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4099 (p : Pattern) (guard : d72941 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d72930 p = 1 := by simpa only [d72941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4082 p hg
    simpa only [d72941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72940 p = 1 := by simpa only [d72941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4098 p hg
    simpa only [d72941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4100 (p : Pattern) (guard : d2549 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d496 p = 1 := by simpa only [d2549, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d2549, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2549, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d2549, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4101 (p : Pattern) (guard : d2550 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2549 p = 1 := by simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4100 p hg
    simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4102 (p : Pattern) (guard : d2551 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2550 p = 1 := by simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4101 p hg
    simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4103 (p : Pattern) (guard : d3536 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2551 p = 1 := by simpa only [d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4102 p hg
    simpa only [d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4104 (p : Pattern) (guard : d62579 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51684 p = 1 := by simpa only [d62579, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2740 p hg
    simpa only [d62579, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62579, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d62579, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4105 (p : Pattern) (guard : d62580 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62579 p = 1 := by simpa only [d62580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4104 p hg
    simpa only [d62580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4106 (p : Pattern) (guard : d72942 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d62580 p = 1 := by simpa only [d72942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4105 p hg
    simpa only [d72942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4107 (p : Pattern) (guard : d72943 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d72942 p = 1 := by simpa only [d72943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4106 p hg
    simpa only [d72943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4108 (p : Pattern) (guard : d72944 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d3536 p = 1 := by simpa only [d72944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4103 p hg
    simpa only [d72944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72943 p = 1 := by simpa only [d72944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4107 p hg
    simpa only [d72944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4109 (p : Pattern) (guard : d72945 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d72944 p = 1 := by simpa only [d72945, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4108 p hg
    simpa only [d72945, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72945, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d72945, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4110 (p : Pattern) (guard : d72946 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d72945 p = 1 := by simpa only [d72946, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4109 p hg
    simpa only [d72946, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72946, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d72946, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4111 (p : Pattern) (guard : d72947 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72946 p = 1 := by simpa only [d72947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4110 p hg
    simpa only [d72947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4112 (p : Pattern) (guard : d72948 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72947 p = 1 := by simpa only [d72948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4111 p hg
    simpa only [d72948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4113 (p : Pattern) (guard : d72949 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72948 p = 1 := by simpa only [d72949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4112 p hg
    simpa only [d72949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4114 (p : Pattern) (guard : d72950 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72949 p = 1 := by simpa only [d72950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4113 p hg
    simpa only [d72950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4115 (p : Pattern) (guard : d72951 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72950 p = 1 := by simpa only [d72951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4114 p hg
    simpa only [d72951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4116 (p : Pattern) (guard : d72952 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72951 p = 1 := by simpa only [d72952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4115 p hg
    simpa only [d72952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4117 (p : Pattern) (guard : d72953 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d72941 p = 1 := by simpa only [d72953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4099 p hg
    simpa only [d72953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72952 p = 1 := by simpa only [d72953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4116 p hg
    simpa only [d72953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4118 (p : Pattern) (guard : d2563 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d788 p = 1 := by simpa only [d2563, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d2563, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2563, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d2563, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4119 (p : Pattern) (guard : d2564 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2563 p = 1 := by simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4118 p hg
    simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4120 (p : Pattern) (guard : d2565 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2564 p = 1 := by simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4119 p hg
    simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4121 (p : Pattern) (guard : d3553 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2565 p = 1 := by simpa only [d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4120 p hg
    simpa only [d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4122 (p : Pattern) (guard : d62593 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51710 p = 1 := by simpa only [d62593, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d62593, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62593, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d62593, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4123 (p : Pattern) (guard : d62594 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62593 p = 1 := by simpa only [d62594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4122 p hg
    simpa only [d62594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4124 (p : Pattern) (guard : d72954 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d62594 p = 1 := by simpa only [d72954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4123 p hg
    simpa only [d72954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4125 (p : Pattern) (guard : d72955 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d72954 p = 1 := by simpa only [d72955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4124 p hg
    simpa only [d72955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4126 (p : Pattern) (guard : d72956 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d3553 p = 1 := by simpa only [d72956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4121 p hg
    simpa only [d72956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72955 p = 1 := by simpa only [d72956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4125 p hg
    simpa only [d72956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4127 (p : Pattern) (guard : d72957 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d72956 p = 1 := by simpa only [d72957, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4126 p hg
    simpa only [d72957, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72957, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d72957, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4128 (p : Pattern) (guard : d72958 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d72957 p = 1 := by simpa only [d72958, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4127 p hg
    simpa only [d72958, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72958, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d72958, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4129 (p : Pattern) (guard : d72959 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72958 p = 1 := by simpa only [d72959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4128 p hg
    simpa only [d72959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4130 (p : Pattern) (guard : d72960 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72959 p = 1 := by simpa only [d72960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4129 p hg
    simpa only [d72960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4131 (p : Pattern) (guard : d72961 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72960 p = 1 := by simpa only [d72961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4130 p hg
    simpa only [d72961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4132 (p : Pattern) (guard : d72962 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72961 p = 1 := by simpa only [d72962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4131 p hg
    simpa only [d72962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4133 (p : Pattern) (guard : d72963 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72962 p = 1 := by simpa only [d72963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4132 p hg
    simpa only [d72963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4134 (p : Pattern) (guard : d72964 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72963 p = 1 := by simpa only [d72964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4133 p hg
    simpa only [d72964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4135 (p : Pattern) (guard : d72965 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72964 p = 1 := by simpa only [d72965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4134 p hg
    simpa only [d72965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4136 (p : Pattern) (guard : d72966 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d72953 p = 1 := by simpa only [d72966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4117 p hg
    simpa only [d72966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72965 p = 1 := by simpa only [d72966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4135 p hg
    simpa only [d72966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4137 (p : Pattern) (guard : d2578 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d2578, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2379 p hg
    simpa only [d2578, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2578, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d2578, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4138 (p : Pattern) (guard : d2579 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2578 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4137 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4139 (p : Pattern) (guard : d2580 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2579 p = 1 := by simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4138 p hg
    simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4140 (p : Pattern) (guard : d3571 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2580 p = 1 := by simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4139 p hg
    simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4141 (p : Pattern) (guard : d62608 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51737 p = 1 := by simpa only [d62608, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3007 p hg
    simpa only [d62608, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62608, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d62608, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4142 (p : Pattern) (guard : d62609 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62608 p = 1 := by simpa only [d62609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4141 p hg
    simpa only [d62609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4143 (p : Pattern) (guard : d72967 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d62609 p = 1 := by simpa only [d72967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4142 p hg
    simpa only [d72967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4144 (p : Pattern) (guard : d72968 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d72967 p = 1 := by simpa only [d72968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d72968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4145 (p : Pattern) (guard : d72969 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d3571 p = 1 := by simpa only [d72969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4140 p hg
    simpa only [d72969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72968 p = 1 := by simpa only [d72969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4144 p hg
    simpa only [d72969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4146 (p : Pattern) (guard : d72970 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d72969 p = 1 := by simpa only [d72970, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4145 p hg
    simpa only [d72970, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72970, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d72970, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4147 (p : Pattern) (guard : d72971 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d72970 p = 1 := by simpa only [d72971, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4146 p hg
    simpa only [d72971, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72971, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d72971, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4148 (p : Pattern) (guard : d72972 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72971 p = 1 := by simpa only [d72972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4147 p hg
    simpa only [d72972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4149 (p : Pattern) (guard : d72973 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72972 p = 1 := by simpa only [d72973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4148 p hg
    simpa only [d72973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4150 (p : Pattern) (guard : d72974 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72973 p = 1 := by simpa only [d72974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4149 p hg
    simpa only [d72974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4151 (p : Pattern) (guard : d72975 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72974 p = 1 := by simpa only [d72975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4150 p hg
    simpa only [d72975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4152 (p : Pattern) (guard : d72976 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72975 p = 1 := by simpa only [d72976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4151 p hg
    simpa only [d72976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4153 (p : Pattern) (guard : d72977 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72976 p = 1 := by simpa only [d72977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4152 p hg
    simpa only [d72977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4154 (p : Pattern) (guard : d72978 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72977 p = 1 := by simpa only [d72978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4153 p hg
    simpa only [d72978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4155 (p : Pattern) (guard : d72979 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72978 p = 1 := by simpa only [d72979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4154 p hg
    simpa only [d72979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4156 (p : Pattern) (guard : d72980 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d72966 p = 1 := by simpa only [d72980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4136 p hg
    simpa only [d72980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72979 p = 1 := by simpa only [d72980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4155 p hg
    simpa only [d72980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4157 (p : Pattern) (guard : d2594 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1628 p = 1 := by simpa only [d2594, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2396 p hg
    simpa only [d2594, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2594, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d2594, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4158 (p : Pattern) (guard : d2595 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2594 p = 1 := by simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4157 p hg
    simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4159 (p : Pattern) (guard : d2596 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2595 p = 1 := by simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4158 p hg
    simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4160 (p : Pattern) (guard : d3590 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2596 p = 1 := by simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4159 p hg
    simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4161 (p : Pattern) (guard : d62624 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51765 p = 1 := by simpa only [d62624, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3149 p hg
    simpa only [d62624, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62624, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d62624, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4162 (p : Pattern) (guard : d62625 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62624 p = 1 := by simpa only [d62625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4161 p hg
    simpa only [d62625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4163 (p : Pattern) (guard : d72981 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d62625 p = 1 := by simpa only [d72981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4162 p hg
    simpa only [d72981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4164 (p : Pattern) (guard : d72982 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d72981 p = 1 := by simpa only [d72982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4163 p hg
    simpa only [d72982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4165 (p : Pattern) (guard : d72983 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d3590 p = 1 := by simpa only [d72983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4160 p hg
    simpa only [d72983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72982 p = 1 := by simpa only [d72983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4164 p hg
    simpa only [d72983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4166 (p : Pattern) (guard : d72984 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d72983 p = 1 := by simpa only [d72984, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4165 p hg
    simpa only [d72984, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72984, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d72984, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4167 (p : Pattern) (guard : d72985 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d72984 p = 1 := by simpa only [d72985, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4166 p hg
    simpa only [d72985, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72985, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d72985, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4168 (p : Pattern) (guard : d72986 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72985 p = 1 := by simpa only [d72986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4167 p hg
    simpa only [d72986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4169 (p : Pattern) (guard : d72987 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72986 p = 1 := by simpa only [d72987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4168 p hg
    simpa only [d72987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4170 (p : Pattern) (guard : d72988 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72987 p = 1 := by simpa only [d72988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4169 p hg
    simpa only [d72988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4171 (p : Pattern) (guard : d72989 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72988 p = 1 := by simpa only [d72989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4170 p hg
    simpa only [d72989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4172 (p : Pattern) (guard : d72990 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72989 p = 1 := by simpa only [d72990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4171 p hg
    simpa only [d72990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4173 (p : Pattern) (guard : d72991 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72990 p = 1 := by simpa only [d72991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4172 p hg
    simpa only [d72991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4174 (p : Pattern) (guard : d72992 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72991 p = 1 := by simpa only [d72992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4173 p hg
    simpa only [d72992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4175 (p : Pattern) (guard : d72993 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72992 p = 1 := by simpa only [d72993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4174 p hg
    simpa only [d72993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4176 (p : Pattern) (guard : d72994 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d72994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d72994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72993 p = 1 := by simpa only [d72994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4175 p hg
    simpa only [d72994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4177 (p : Pattern) (guard : d72995 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d72980 p = 1 := by simpa only [d72995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4156 p hg
    simpa only [d72995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72994 p = 1 := by simpa only [d72995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4176 p hg
    simpa only [d72995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4178 (p : Pattern) (guard : d2611 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d2111 p = 1 := by simpa only [d2611, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d2611, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2611, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d2611, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4179 (p : Pattern) (guard : d2612 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2611 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4178 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4180 (p : Pattern) (guard : d2613 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2612 p = 1 := by simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4179 p hg
    simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4181 (p : Pattern) (guard : d3610 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2613 p = 1 := by simpa only [d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4180 p hg
    simpa only [d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4182 (p : Pattern) (guard : d62641 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51794 p = 1 := by simpa only [d62641, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3292 p hg
    simpa only [d62641, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62641, d48084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d62641, d48084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4183 (p : Pattern) (guard : d62642 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62641 p = 1 := by simpa only [d62642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4182 p hg
    simpa only [d62642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4184 (p : Pattern) (guard : d72996 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d62642 p = 1 := by simpa only [d72996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4183 p hg
    simpa only [d72996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4185 (p : Pattern) (guard : d72997 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d72996 p = 1 := by simpa only [d72997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4184 p hg
    simpa only [d72997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d72997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4186 (p : Pattern) (guard : d72998 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d3610 p = 1 := by simpa only [d72998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4181 p hg
    simpa only [d72998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72997 p = 1 := by simpa only [d72998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4185 p hg
    simpa only [d72998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4187 (p : Pattern) (guard : d72999 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d72998 p = 1 := by simpa only [d72999, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4186 p hg
    simpa only [d72999, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72999, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d72999, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4188 (p : Pattern) (guard : d73000 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d72999 p = 1 := by simpa only [d73000, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4187 p hg
    simpa only [d73000, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73000, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d73000, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4189 (p : Pattern) (guard : d73001 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73000 p = 1 := by simpa only [d73001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4188 p hg
    simpa only [d73001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4190 (p : Pattern) (guard : d73002 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73001 p = 1 := by simpa only [d73002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4189 p hg
    simpa only [d73002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4191 (p : Pattern) (guard : d73003 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73002 p = 1 := by simpa only [d73003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4190 p hg
    simpa only [d73003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4192 (p : Pattern) (guard : d73004 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73003 p = 1 := by simpa only [d73004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4191 p hg
    simpa only [d73004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4193 (p : Pattern) (guard : d73005 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73004 p = 1 := by simpa only [d73005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4192 p hg
    simpa only [d73005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4194 (p : Pattern) (guard : d73006 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73005 p = 1 := by simpa only [d73006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4193 p hg
    simpa only [d73006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4195 (p : Pattern) (guard : d73007 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73006 p = 1 := by simpa only [d73007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4194 p hg
    simpa only [d73007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4196 (p : Pattern) (guard : d73008 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73007 p = 1 := by simpa only [d73008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4195 p hg
    simpa only [d73008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4197 (p : Pattern) (guard : d73009 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73008 p = 1 := by simpa only [d73009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4196 p hg
    simpa only [d73009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4198 (p : Pattern) (guard : d73010 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73009 p = 1 := by simpa only [d73010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4197 p hg
    simpa only [d73010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4199 (p : Pattern) (guard : d73011 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d72995 p = 1 := by simpa only [d73011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4177 p hg
    simpa only [d73011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73010 p = 1 := by simpa only [d73011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4198 p hg
    simpa only [d73011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4200 (p : Pattern) (guard : d73012 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d73011 p = 1 := by simpa only [d73012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4199 p hg
    simpa only [d73012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4201 (p : Pattern) (guard : d73013 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d73012 p = 1 := by simpa only [d73013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4200 p hg
    simpa only [d73013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4202 (p : Pattern) (guard : d73014 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d73013 p = 1 := by simpa only [d73014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4201 p hg
    simpa only [d73014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4203 (p : Pattern) (guard : d73015 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d73014 p = 1 := by simpa only [d73015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4202 p hg
    simpa only [d73015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4204 (p : Pattern) (guard : d73016 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d73015 p = 1 := by simpa only [d73016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4203 p hg
    simpa only [d73016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4205 (p : Pattern) (guard : d73017 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d73016 p = 1 := by simpa only [d73017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4204 p hg
    simpa only [d73017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4206 (p : Pattern) (guard : d73018 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d73017 p = 1 := by simpa only [d73018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4205 p hg
    simpa only [d73018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4207 (p : Pattern) (guard : d73019 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d73018 p = 1 := by simpa only [d73019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4206 p hg
    simpa only [d73019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4208 (p : Pattern) (guard : d73020 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d73019 p = 1 := by simpa only [d73020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4207 p hg
    simpa only [d73020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4209 (p : Pattern) (guard : d73021 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d73020 p = 1 := by simpa only [d73021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4208 p hg
    simpa only [d73021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4210 (p : Pattern) (guard : d73022 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d73021 p = 1 := by simpa only [d73022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4209 p hg
    simpa only [d73022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4211 (p : Pattern) (guard : d73023 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d73022 p = 1 := by simpa only [d73023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4210 p hg
    simpa only [d73023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4212 (p : Pattern) (guard : d73024 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d73023 p = 1 := by simpa only [d73024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4211 p hg
    simpa only [d73024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4213 (p : Pattern) (guard : d73025 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d73024 p = 1 := by simpa only [d73025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d73025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4214 (p : Pattern) (guard : d73026 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d73025 p = 1 := by simpa only [d73026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4213 p hg
    simpa only [d73026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4215 (p : Pattern) (guard : d73027 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d73026 p = 1 := by simpa only [d73027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4214 p hg
    simpa only [d73027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4216 (p : Pattern) (guard : d73028 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d73027 p = 1 := by simpa only [d73028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d73028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4217 (p : Pattern) (guard : d73029 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d73028 p = 1 := by simpa only [d73029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4216 p hg
    simpa only [d73029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4218 (p : Pattern) (guard : d73030 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d73029 p = 1 := by simpa only [d73030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4217 p hg
    simpa only [d73030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4219 (p : Pattern) (guard : d73031 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d73030 p = 1 := by simpa only [d73031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4218 p hg
    simpa only [d73031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4220 (p : Pattern) (guard : d73032 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d73031 p = 1 := by simpa only [d73032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4219 p hg
    simpa only [d73032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4221 (p : Pattern) (guard : d73033 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d73032 p = 1 := by simpa only [d73033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4220 p hg
    simpa only [d73033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4222 (p : Pattern) (guard : d73034 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d73033 p = 1 := by simpa only [d73034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d73034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4223 (p : Pattern) (guard : d73035 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d73034 p = 1 := by simpa only [d73035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4222 p hg
    simpa only [d73035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4224 (p : Pattern) (guard : d73036 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d73035 p = 1 := by simpa only [d73036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4223 p hg
    simpa only [d73036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4225 (p : Pattern) (guard : d73037 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d73036 p = 1 := by simpa only [d73037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4224 p hg
    simpa only [d73037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4226 (p : Pattern) (guard : d73038 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d73037 p = 1 := by simpa only [d73038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4225 p hg
    simpa only [d73038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4227 (p : Pattern) (guard : d73039 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d73038 p = 1 := by simpa only [d73039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4226 p hg
    simpa only [d73039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4228 (p : Pattern) (guard : d73040 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d73039 p = 1 := by simpa only [d73040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4227 p hg
    simpa only [d73040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4229 (p : Pattern) (guard : d73041 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d73040 p = 1 := by simpa only [d73041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4228 p hg
    simpa only [d73041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4230 (p : Pattern) (guard : d73042 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d73041 p = 1 := by simpa only [d73042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d73042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4231 (p : Pattern) (guard : d73043 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d73042 p = 1 := by simpa only [d73043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d73043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4232 (p : Pattern) (guard : d73044 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d73043 p = 1 := by simpa only [d73044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4231 p hg
    simpa only [d73044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4233 (p : Pattern) (guard : d73045 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d73044 p = 1 := by simpa only [d73045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d73045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4234 (p : Pattern) (guard : d73046 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d73045 p = 1 := by simpa only [d73046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4233 p hg
    simpa only [d73046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4235 (p : Pattern) (guard : d73047 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d73046 p = 1 := by simpa only [d73047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d73047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4236 (p : Pattern) (guard : d73048 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d73047 p = 1 := by simpa only [d73048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4235 p hg
    simpa only [d73048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4237 (p : Pattern) (guard : d73049 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d73048 p = 1 := by simpa only [d73049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4236 p hg
    simpa only [d73049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4238 (p : Pattern) (guard : d73050 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d73049 p = 1 := by simpa only [d73050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4237 p hg
    simpa only [d73050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4239 (p : Pattern) (guard : d73051 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d73050 p = 1 := by simpa only [d73051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4238 p hg
    simpa only [d73051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4240 (p : Pattern) (guard : d73052 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d73051 p = 1 := by simpa only [d73052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4239 p hg
    simpa only [d73052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4241 (p : Pattern) (guard : d73053 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d73052 p = 1 := by simpa only [d73053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4240 p hg
    simpa only [d73053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4242 (p : Pattern) (guard : d73054 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d73053 p = 1 := by simpa only [d73054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4241 p hg
    simpa only [d73054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d73054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d73054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4243 (p : Pattern) (guard : d2527 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2526 p = 1 := by simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4069 p hg
    simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4244 (p : Pattern) (guard : d62702 p = 1) : d48084 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d62702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2527 p = 1 := by simpa only [d62702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4243 p hg
    simpa only [d62702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4245 (p : Pattern) (guard : d62703 p = 1) : d48084 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62702 p = 1 := by simpa only [d62703, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4244 p hg
    simpa only [d62703, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62703, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d62703, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4246 (p : Pattern) (guard : d62704 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62703 p = 1 := by simpa only [d62704, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4245 p hg
    simpa only [d62704, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62704, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d62704, d48087, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4247 (p : Pattern) (guard : d62705 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62704 p = 1 := by simpa only [d62705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4246 p hg
    simpa only [d62705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4248 (p : Pattern) (guard : d62706 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62705 p = 1 := by simpa only [d62706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4247 p hg
    simpa only [d62706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4249 (p : Pattern) (guard : d62707 p = 1) : d48087 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d62707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62706 p = 1 := by simpa only [d62707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4248 p hg
    simpa only [d62707, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
