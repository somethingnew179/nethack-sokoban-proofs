import NetHack.Soko22Hazard87.Compare139
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35000 (p : Pattern) (guard : d0 p = 1) : d50408 p ≤ (3 : Int) + d47786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35001 (p : Pattern) (guard : d0 p = 1) : d50419 p ≤ (3 : Int) + d47796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35002 (p : Pattern) (guard : d0 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35003 (p : Pattern) (guard : d0 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35004 (p : Pattern) (guard : d16 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare35005 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (3 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35006 (p : Pattern) (guard : d17 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35004 p hg
    simpa only [d17, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d17, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35007 (p : Pattern) (guard : d38813 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35006 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35008 (p : Pattern) (guard : d257183 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35007 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35009 (p : Pattern) (guard : d0 p = 1) : d50141 p ≤ (3 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35010 (p : Pattern) (guard : d257184 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35008 p hg
    simpa only [d257184, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d257184, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35011 (p : Pattern) (guard : d0 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35012 (p : Pattern) (guard : d257185 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35013 (p : Pattern) (guard : d257186 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257185 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35012 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35014 (p : Pattern) (guard : d0 p = 1) : d50142 p ≤ (3 : Int) + d47631 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35015 (p : Pattern) (guard : d257187 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257186 p = 1 := by simpa only [d257187, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35013 p hg
    simpa only [d257187, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257187, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d257187, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35016 (p : Pattern) (guard : d257188 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257187 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35015 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35017 (p : Pattern) (guard : d257230 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d257230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257188 p = 1 := by simpa only [d257230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35016 p hg
    simpa only [d257230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35018 (p : Pattern) (guard : d257189 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d257188 p = 1 := by simpa only [d257189, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34882 p hg
    simpa only [d257189, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257189, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d257189, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35019 (p : Pattern) (guard : d257231 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d257230 p = 1 := by simpa only [d257231, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35017 p hg
    simpa only [d257231, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257189 p = 1 := by simpa only [d257231, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35018 p hg
    simpa only [d257231, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35020 (p : Pattern) (guard : d0 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35021 (p : Pattern) (guard : d16 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare35022 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (3 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35023 (p : Pattern) (guard : d17 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35021 p hg
    simpa only [d17, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d17, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35024 (p : Pattern) (guard : d38813 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35023 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35025 (p : Pattern) (guard : d257183 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35024 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35026 (p : Pattern) (guard : d0 p = 1) : d50146 p ≤ (3 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35027 (p : Pattern) (guard : d257184 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35025 p hg
    simpa only [d257184, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d257184, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35028 (p : Pattern) (guard : d0 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35029 (p : Pattern) (guard : d257185 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35027 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35030 (p : Pattern) (guard : d257186 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257185 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35029 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35031 (p : Pattern) (guard : d0 p = 1) : d50147 p ≤ (3 : Int) + d47635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35032 (p : Pattern) (guard : d257187 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257186 p = 1 := by simpa only [d257187, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35030 p hg
    simpa only [d257187, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257187, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d257187, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35033 (p : Pattern) (guard : d0 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35034 (p : Pattern) (guard : d257188 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257187 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35032 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35035 (p : Pattern) (guard : d257189 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d257188 p = 1 := by simpa only [d257189, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35034 p hg
    simpa only [d257189, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257189, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d257189, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35036 (p : Pattern) (guard : d257190 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d257189 p = 1 := by simpa only [d257190, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35035 p hg
    simpa only [d257190, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257190, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d257190, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35037 (p : Pattern) (guard : d257232 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d257231 p = 1 := by simpa only [d257232, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35019 p hg
    simpa only [d257232, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257190 p = 1 := by simpa only [d257232, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35036 p hg
    simpa only [d257232, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35038 (p : Pattern) (guard : d0 p = 1) : d50425 p ≤ (3 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35039 (p : Pattern) (guard : d257233 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d257232 p = 1 := by simpa only [d257233, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35037 p hg
    simpa only [d257233, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257233, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d257233, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35040 (p : Pattern) (guard : d0 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35041 (p : Pattern) (guard : d257234 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d257233 p = 1 := by simpa only [d257234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35039 p hg
    simpa only [d257234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d257234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35042 (p : Pattern) (guard : d257235 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d257234 p = 1 := by simpa only [d257235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35041 p hg
    simpa only [d257235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d257235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35043 (p : Pattern) (guard : d257236 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d257235 p = 1 := by simpa only [d257236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35042 p hg
    simpa only [d257236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d257236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35044 (p : Pattern) (guard : d257237 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257237, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d257237, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257236 p = 1 := by simpa only [d257237, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35043 p hg
    simpa only [d257237, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35045 (p : Pattern) (guard : d257238 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257238, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d257238, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257237 p = 1 := by simpa only [d257238, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35044 p hg
    simpa only [d257238, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35046 (p : Pattern) (guard : d0 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35047 (p : Pattern) (guard : d257239 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d257238 p = 1 := by simpa only [d257239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35045 p hg
    simpa only [d257239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d257239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35048 (p : Pattern) (guard : d257240 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d257239 p = 1 := by simpa only [d257240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35047 p hg
    simpa only [d257240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d257240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35049 (p : Pattern) (guard : d257241 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d257240 p = 1 := by simpa only [d257241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35048 p hg
    simpa only [d257241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d257241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35050 (p : Pattern) (guard : d0 p = 1) : d50429 p ≤ (3 : Int) + d47806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35051 (p : Pattern) (guard : d257242 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d257241 p = 1 := by simpa only [d257242, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35049 p hg
    simpa only [d257242, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257242, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d257242, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35052 (p : Pattern) (guard : d257243 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257243, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d257243, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257242 p = 1 := by simpa only [d257243, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35051 p hg
    simpa only [d257243, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35053 (p : Pattern) (guard : d257244 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d257243 p = 1 := by simpa only [d257244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35052 p hg
    simpa only [d257244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35054 (p : Pattern) (guard : d257245 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d257244 p = 1 := by simpa only [d257245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35053 p hg
    simpa only [d257245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35055 (p : Pattern) (guard : d257246 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257245 p = 1 := by simpa only [d257246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35054 p hg
    simpa only [d257246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35056 (p : Pattern) (guard : d257247 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d257246 p = 1 := by simpa only [d257247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35055 p hg
    simpa only [d257247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35057 (p : Pattern) (guard : d257248 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257247 p = 1 := by simpa only [d257248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35056 p hg
    simpa only [d257248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35058 (p : Pattern) (guard : d257249 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d257248 p = 1 := by simpa only [d257249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35057 p hg
    simpa only [d257249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35059 (p : Pattern) (guard : d257250 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257249 p = 1 := by simpa only [d257250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35058 p hg
    simpa only [d257250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35060 (p : Pattern) (guard : d257251 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257250 p = 1 := by simpa only [d257251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35059 p hg
    simpa only [d257251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35061 (p : Pattern) (guard : d257252 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d257252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257251 p = 1 := by simpa only [d257252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35060 p hg
    simpa only [d257252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35062 (p : Pattern) (guard : d257253 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257253, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257253, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257252 p = 1 := by simpa only [d257253, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35061 p hg
    simpa only [d257253, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35063 (p : Pattern) (guard : d257254 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d257254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257253 p = 1 := by simpa only [d257254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35062 p hg
    simpa only [d257254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35064 (p : Pattern) (guard : d257255 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d257254 p = 1 := by simpa only [d257255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35063 p hg
    simpa only [d257255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d257255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35065 (p : Pattern) (guard : d257256 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d257255 p = 1 := by simpa only [d257256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35064 p hg
    simpa only [d257256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d257256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35066 (p : Pattern) (guard : d257257 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d257256 p = 1 := by simpa only [d257257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35065 p hg
    simpa only [d257257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d257257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35067 (p : Pattern) (guard : d0 p = 1) : d50491 p ≤ (3 : Int) + d47864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35068 (p : Pattern) (guard : d257258 p = 1) : d50492 p ≤ (3 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d257257 p = 1 := by simpa only [d257258, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35066 p hg
    simpa only [d257258, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257258, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d257258, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35069 (p : Pattern) (guard : d257259 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d257229 p = 1 := by simpa only [d257259, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34997 p hg
    simpa only [d257259, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257258 p = 1 := by simpa only [d257259, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35068 p hg
    simpa only [d257259, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35070 (p : Pattern) (guard : d257260 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d257260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257259 p = 1 := by simpa only [d257260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35069 p hg
    simpa only [d257260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35071 (p : Pattern) (guard : d257261 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d257261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257260 p = 1 := by simpa only [d257261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35070 p hg
    simpa only [d257261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35072 (p : Pattern) (guard : d257262 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d257262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257261 p = 1 := by simpa only [d257262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35071 p hg
    simpa only [d257262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35073 (p : Pattern) (guard : d257263 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d257263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257262 p = 1 := by simpa only [d257263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35072 p hg
    simpa only [d257263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35074 (p : Pattern) (guard : d257264 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d257264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257263 p = 1 := by simpa only [d257264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35073 p hg
    simpa only [d257264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35075 (p : Pattern) (guard : d257265 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257207 p = 1 := by simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34907 p hg
    simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35076 (p : Pattern) (guard : d257266 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257265 p = 1 := by simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35075 p hg
    simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35077 (p : Pattern) (guard : d257267 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257266 p = 1 := by simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35076 p hg
    simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35078 (p : Pattern) (guard : d257268 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257267 p = 1 := by simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35077 p hg
    simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35079 (p : Pattern) (guard : d257269 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257269, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257269, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257268 p = 1 := by simpa only [d257269, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35078 p hg
    simpa only [d257269, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35080 (p : Pattern) (guard : d257270 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d257270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257269 p = 1 := by simpa only [d257270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35079 p hg
    simpa only [d257270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35081 (p : Pattern) (guard : d257271 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d257270 p = 1 := by simpa only [d257271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35080 p hg
    simpa only [d257271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d257271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35082 (p : Pattern) (guard : d257265 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257207 p = 1 := by simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34926 p hg
    simpa only [d257265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35083 (p : Pattern) (guard : d257266 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257265 p = 1 := by simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35082 p hg
    simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35084 (p : Pattern) (guard : d257267 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257266 p = 1 := by simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35083 p hg
    simpa only [d257267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35085 (p : Pattern) (guard : d257268 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257267 p = 1 := by simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35084 p hg
    simpa only [d257268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35086 (p : Pattern) (guard : d257272 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257214 p = 1 := by simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34932 p hg
    simpa only [d257272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35087 (p : Pattern) (guard : d257273 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257272 p = 1 := by simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35086 p hg
    simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35088 (p : Pattern) (guard : d257274 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257273 p = 1 := by simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35087 p hg
    simpa only [d257274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35089 (p : Pattern) (guard : d257275 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257274 p = 1 := by simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35088 p hg
    simpa only [d257275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35090 (p : Pattern) (guard : d257276 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d257268 p = 1 := by simpa only [d257276, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35085 p hg
    simpa only [d257276, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257275 p = 1 := by simpa only [d257276, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35089 p hg
    simpa only [d257276, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35091 (p : Pattern) (guard : d257277 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d257269 p = 1 := by simpa only [d257277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35079 p hg
    simpa only [d257277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257276 p = 1 := by simpa only [d257277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35090 p hg
    simpa only [d257277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35092 (p : Pattern) (guard : d257278 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d257277 p = 1 := by simpa only [d257278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35091 p hg
    simpa only [d257278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d257278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35093 (p : Pattern) (guard : d257279 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d257271 p = 1 := by simpa only [d257279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35081 p hg
    simpa only [d257279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257278 p = 1 := by simpa only [d257279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35092 p hg
    simpa only [d257279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35094 (p : Pattern) (guard : d257280 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257204 p = 1 := by simpa only [d257280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d257280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35095 (p : Pattern) (guard : d257281 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257280 p = 1 := by simpa only [d257281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d257281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35096 (p : Pattern) (guard : d257282 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257281 p = 1 := by simpa only [d257282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35095 p hg
    simpa only [d257282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35097 (p : Pattern) (guard : d257283 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257282 p = 1 := by simpa only [d257283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35096 p hg
    simpa only [d257283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35098 (p : Pattern) (guard : d257284 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257283 p = 1 := by simpa only [d257284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35097 p hg
    simpa only [d257284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35099 (p : Pattern) (guard : d257285 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257284 p = 1 := by simpa only [d257285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35098 p hg
    simpa only [d257285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35100 (p : Pattern) (guard : d257286 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257203 p = 1 := by simpa only [d257286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34903 p hg
    simpa only [d257286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35101 (p : Pattern) (guard : d257287 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257286 p = 1 := by simpa only [d257287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35100 p hg
    simpa only [d257287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35102 (p : Pattern) (guard : d257288 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257287 p = 1 := by simpa only [d257288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35101 p hg
    simpa only [d257288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35103 (p : Pattern) (guard : d257289 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257288 p = 1 := by simpa only [d257289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35102 p hg
    simpa only [d257289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35104 (p : Pattern) (guard : d257290 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257289 p = 1 := by simpa only [d257290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35103 p hg
    simpa only [d257290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35105 (p : Pattern) (guard : d257291 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257290 p = 1 := by simpa only [d257291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35104 p hg
    simpa only [d257291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35106 (p : Pattern) (guard : d130 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare35107 (p : Pattern) (guard : d33213 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d33213, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35106 p hg
    simpa only [d33213, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33213, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d33213, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35108 (p : Pattern) (guard : d285865 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33213 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35107 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35109 (p : Pattern) (guard : d285866 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d285865 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35108 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35110 (p : Pattern) (guard : d285867 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d285866 p = 1 := by simpa only [d285867, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35109 p hg
    simpa only [d285867, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285867, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d285867, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35111 (p : Pattern) (guard : d285868 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d285867 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35110 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34875 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35112 (p : Pattern) (guard : d285869 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35111 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34877 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35113 (p : Pattern) (guard : d285870 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285869 p = 1 := by simpa only [d285870, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35112 p hg
    simpa only [d285870, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285870, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d285870, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35114 (p : Pattern) (guard : d285871 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285870 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35113 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34880 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35115 (p : Pattern) (guard : d285872 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285871 p = 1 := by simpa only [d285872, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d285872, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285872, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d285872, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35116 (p : Pattern) (guard : d285873 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285872 p = 1 := by simpa only [d285873, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35115 p hg
    simpa only [d285873, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285873, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d285873, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35117 (p : Pattern) (guard : d285874 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285874, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d285874, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285873 p = 1 := by simpa only [d285874, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35116 p hg
    simpa only [d285874, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35118 (p : Pattern) (guard : d285875 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285874 p = 1 := by simpa only [d285875, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35117 p hg
    simpa only [d285875, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285875, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d285875, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35119 (p : Pattern) (guard : d285876 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285875 p = 1 := by simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35118 p hg
    simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257192 p = 1 := by simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34889 p hg
    simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35120 (p : Pattern) (guard : d285877 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d285876 p = 1 := by simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35119 p hg
    simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257193 p = 1 := by simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34891 p hg
    simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35121 (p : Pattern) (guard : d285878 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d285877 p = 1 := by simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35120 p hg
    simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257194 p = 1 := by simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34892 p hg
    simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35122 (p : Pattern) (guard : d285879 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285879, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d285879, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285878 p = 1 := by simpa only [d285879, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35121 p hg
    simpa only [d285879, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35123 (p : Pattern) (guard : d285880 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285880, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d285880, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285879 p = 1 := by simpa only [d285880, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35122 p hg
    simpa only [d285880, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35124 (p : Pattern) (guard : d285881 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35123 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257197 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34895 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35125 (p : Pattern) (guard : d285882 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d285881 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35124 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257198 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35126 (p : Pattern) (guard : d285883 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d285882 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35125 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35127 (p : Pattern) (guard : d285884 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d285883 p = 1 := by simpa only [d285884, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35126 p hg
    simpa only [d285884, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285884, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d285884, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35128 (p : Pattern) (guard : d285885 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285885, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d285885, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285884 p = 1 := by simpa only [d285885, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35127 p hg
    simpa only [d285885, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35129 (p : Pattern) (guard : d285886 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285885 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35128 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257202 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34902 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35130 (p : Pattern) (guard : d285887 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d285886 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35129 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35131 (p : Pattern) (guard : d285888 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285887 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35132 (p : Pattern) (guard : d285889 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285888 p = 1 := by simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35131 p hg
    simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35133 (p : Pattern) (guard : d285890 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285889 p = 1 := by simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35132 p hg
    simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257206 p = 1 := by simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34906 p hg
    simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35134 (p : Pattern) (guard : d285891 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d285890 p = 1 := by simpa only [d285891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35133 p hg
    simpa only [d285891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35135 (p : Pattern) (guard : d285892 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285891 p = 1 := by simpa only [d285892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35134 p hg
    simpa only [d285892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257208 p = 1 := by simpa only [d285892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d285892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35136 (p : Pattern) (guard : d285893 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d257291 p = 1 := by simpa only [d285893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35105 p hg
    simpa only [d285893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285892 p = 1 := by simpa only [d285893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35135 p hg
    simpa only [d285893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35137 (p : Pattern) (guard : d285894 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d257285 p = 1 := by simpa only [d285894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d285894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285893 p = 1 := by simpa only [d285894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35136 p hg
    simpa only [d285894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35138 (p : Pattern) (guard : d285895 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285895, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285895, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285894 p = 1 := by simpa only [d285895, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35137 p hg
    simpa only [d285895, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35139 (p : Pattern) (guard : d257280 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257204 p = 1 := by simpa only [d257280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34923 p hg
    simpa only [d257280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35140 (p : Pattern) (guard : d257281 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257280 p = 1 := by simpa only [d257281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35139 p hg
    simpa only [d257281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35141 (p : Pattern) (guard : d257282 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257281 p = 1 := by simpa only [d257282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35140 p hg
    simpa only [d257282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35142 (p : Pattern) (guard : d257283 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257282 p = 1 := by simpa only [d257283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35141 p hg
    simpa only [d257283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35143 (p : Pattern) (guard : d257284 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257283 p = 1 := by simpa only [d257284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35142 p hg
    simpa only [d257284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35144 (p : Pattern) (guard : d257285 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257284 p = 1 := by simpa only [d257285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35143 p hg
    simpa only [d257285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35145 (p : Pattern) (guard : d257286 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257203 p = 1 := by simpa only [d257286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34922 p hg
    simpa only [d257286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35146 (p : Pattern) (guard : d257287 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257286 p = 1 := by simpa only [d257287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35145 p hg
    simpa only [d257287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35147 (p : Pattern) (guard : d257288 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257287 p = 1 := by simpa only [d257288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35146 p hg
    simpa only [d257288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35148 (p : Pattern) (guard : d257289 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257288 p = 1 := by simpa only [d257289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35147 p hg
    simpa only [d257289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35149 (p : Pattern) (guard : d257290 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257289 p = 1 := by simpa only [d257290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35148 p hg
    simpa only [d257290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35150 (p : Pattern) (guard : d257291 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257290 p = 1 := by simpa only [d257291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35149 p hg
    simpa only [d257291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35151 (p : Pattern) (guard : d285880 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285880, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d285880, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285879 p = 1 := by simpa only [d285880, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35122 p hg
    simpa only [d285880, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35152 (p : Pattern) (guard : d285881 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35151 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257197 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34915 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35153 (p : Pattern) (guard : d285882 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d285881 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35152 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257198 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34917 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35154 (p : Pattern) (guard : d285883 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d285882 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35153 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35155 (p : Pattern) (guard : d285884 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d285883 p = 1 := by simpa only [d285884, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35154 p hg
    simpa only [d285884, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285884, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d285884, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35156 (p : Pattern) (guard : d285885 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285885, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d285885, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285884 p = 1 := by simpa only [d285885, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35155 p hg
    simpa only [d285885, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35157 (p : Pattern) (guard : d285886 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285885 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35156 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257202 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34921 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35158 (p : Pattern) (guard : d285887 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d285886 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35157 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35159 (p : Pattern) (guard : d285888 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285887 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35158 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35160 (p : Pattern) (guard : d285889 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285888 p = 1 := by simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35159 p hg
    simpa only [d285889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35161 (p : Pattern) (guard : d285890 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285889 p = 1 := by simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35160 p hg
    simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257206 p = 1 := by simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34925 p hg
    simpa only [d285890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35162 (p : Pattern) (guard : d285891 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d285890 p = 1 := by simpa only [d285891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35161 p hg
    simpa only [d285891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35163 (p : Pattern) (guard : d285892 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285891 p = 1 := by simpa only [d285892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35162 p hg
    simpa only [d285892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257208 p = 1 := by simpa only [d285892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34927 p hg
    simpa only [d285892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35164 (p : Pattern) (guard : d285893 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d257291 p = 1 := by simpa only [d285893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35150 p hg
    simpa only [d285893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285892 p = 1 := by simpa only [d285893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35163 p hg
    simpa only [d285893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35165 (p : Pattern) (guard : d285894 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d257285 p = 1 := by simpa only [d285894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35144 p hg
    simpa only [d285894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285893 p = 1 := by simpa only [d285894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35164 p hg
    simpa only [d285894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35166 (p : Pattern) (guard : d257323 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d257280 p = 1 := by simpa only [d257323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d257323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35167 (p : Pattern) (guard : d257324 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257323 p = 1 := by simpa only [d257324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35166 p hg
    simpa only [d257324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35168 (p : Pattern) (guard : d257325 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257324 p = 1 := by simpa only [d257325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35167 p hg
    simpa only [d257325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35169 (p : Pattern) (guard : d257326 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257325 p = 1 := by simpa only [d257326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d257326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35170 (p : Pattern) (guard : d257327 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257326 p = 1 := by simpa only [d257327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35169 p hg
    simpa only [d257327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35171 (p : Pattern) (guard : d257328 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d257287 p = 1 := by simpa only [d257328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35101 p hg
    simpa only [d257328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35172 (p : Pattern) (guard : d257329 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257328 p = 1 := by simpa only [d257329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35171 p hg
    simpa only [d257329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35173 (p : Pattern) (guard : d257330 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257329 p = 1 := by simpa only [d257330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35172 p hg
    simpa only [d257330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35174 (p : Pattern) (guard : d257331 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257330 p = 1 := by simpa only [d257331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35173 p hg
    simpa only [d257331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35175 (p : Pattern) (guard : d285896 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d285888 p = 1 := by simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35131 p hg
    simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35176 (p : Pattern) (guard : d285897 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285896 p = 1 := by simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35175 p hg
    simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257213 p = 1 := by simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34931 p hg
    simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35177 (p : Pattern) (guard : d285898 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d285897 p = 1 := by simpa only [d285898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35176 p hg
    simpa only [d285898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d285898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35178 (p : Pattern) (guard : d285899 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285898 p = 1 := by simpa only [d285899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35177 p hg
    simpa only [d285899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257215 p = 1 := by simpa only [d285899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34933 p hg
    simpa only [d285899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35179 (p : Pattern) (guard : d285900 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d257331 p = 1 := by simpa only [d285900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35174 p hg
    simpa only [d285900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285899 p = 1 := by simpa only [d285900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d285900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35180 (p : Pattern) (guard : d285901 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d257327 p = 1 := by simpa only [d285901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35170 p hg
    simpa only [d285901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285900 p = 1 := by simpa only [d285901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35179 p hg
    simpa only [d285901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35181 (p : Pattern) (guard : d285902 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d285894 p = 1 := by simpa only [d285902, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d285902, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285901 p = 1 := by simpa only [d285902, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35180 p hg
    simpa only [d285902, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35182 (p : Pattern) (guard : d285903 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d285895 p = 1 := by simpa only [d285903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35138 p hg
    simpa only [d285903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285902 p = 1 := by simpa only [d285903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35181 p hg
    simpa only [d285903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35183 (p : Pattern) (guard : d257340 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d257268 p = 1 := by simpa only [d257340, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35085 p hg
    simpa only [d257340, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257340, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257340, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35184 (p : Pattern) (guard : d257341 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d257340 p = 1 := by simpa only [d257341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35183 p hg
    simpa only [d257341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d257341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35185 (p : Pattern) (guard : d285904 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d285903 p = 1 := by simpa only [d285904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35182 p hg
    simpa only [d285904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257341 p = 1 := by simpa only [d285904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35184 p hg
    simpa only [d285904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35186 (p : Pattern) (guard : d285905 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d285904 p = 1 := by simpa only [d285905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35185 p hg
    simpa only [d285905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d285905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35187 (p : Pattern) (guard : d285906 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d257279 p = 1 := by simpa only [d285906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d285906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285905 p = 1 := by simpa only [d285906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35186 p hg
    simpa only [d285906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35188 (p : Pattern) (guard : d130 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare35189 (p : Pattern) (guard : d33213 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d33213, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35188 p hg
    simpa only [d33213, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33213, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d33213, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35190 (p : Pattern) (guard : d285865 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33213 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35189 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35191 (p : Pattern) (guard : d285866 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d285865 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35190 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35192 (p : Pattern) (guard : d285867 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d285866 p = 1 := by simpa only [d285867, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35191 p hg
    simpa only [d285867, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285867, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d285867, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35193 (p : Pattern) (guard : d285868 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d285867 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35192 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34955 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35194 (p : Pattern) (guard : d285869 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35193 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34957 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35195 (p : Pattern) (guard : d285870 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285869 p = 1 := by simpa only [d285870, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35194 p hg
    simpa only [d285870, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285870, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d285870, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35196 (p : Pattern) (guard : d285871 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285870 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35195 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34960 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35197 (p : Pattern) (guard : d285872 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285871 p = 1 := by simpa only [d285872, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35196 p hg
    simpa only [d285872, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285872, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d285872, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35198 (p : Pattern) (guard : d285873 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285872 p = 1 := by simpa only [d285873, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35197 p hg
    simpa only [d285873, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285873, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d285873, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35199 (p : Pattern) (guard : d285874 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285874, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d285874, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285873 p = 1 := by simpa only [d285874, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35198 p hg
    simpa only [d285874, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35200 (p : Pattern) (guard : d285875 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285874 p = 1 := by simpa only [d285875, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35199 p hg
    simpa only [d285875, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285875, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d285875, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35201 (p : Pattern) (guard : d285876 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285875 p = 1 := by simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35200 p hg
    simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257192 p = 1 := by simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34969 p hg
    simpa only [d285876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35202 (p : Pattern) (guard : d285877 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d285876 p = 1 := by simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35201 p hg
    simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257193 p = 1 := by simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34971 p hg
    simpa only [d285877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35203 (p : Pattern) (guard : d285878 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d285877 p = 1 := by simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35202 p hg
    simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257194 p = 1 := by simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34972 p hg
    simpa only [d285878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35204 (p : Pattern) (guard : d285879 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285879, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d285879, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285878 p = 1 := by simpa only [d285879, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35203 p hg
    simpa only [d285879, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35205 (p : Pattern) (guard : d285880 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285880, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d285880, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285879 p = 1 := by simpa only [d285880, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35204 p hg
    simpa only [d285880, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35206 (p : Pattern) (guard : d285881 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35205 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257197 p = 1 := by simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34975 p hg
    simpa only [d285881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35207 (p : Pattern) (guard : d285882 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d285881 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35206 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257198 p = 1 := by simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34977 p hg
    simpa only [d285882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35208 (p : Pattern) (guard : d285883 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d285882 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35207 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d285883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35209 (p : Pattern) (guard : d285884 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d285883 p = 1 := by simpa only [d285884, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35208 p hg
    simpa only [d285884, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285884, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d285884, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35210 (p : Pattern) (guard : d285885 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285885, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d285885, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285884 p = 1 := by simpa only [d285885, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35209 p hg
    simpa only [d285885, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35211 (p : Pattern) (guard : d285886 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d285885 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35210 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257202 p = 1 := by simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34982 p hg
    simpa only [d285886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35212 (p : Pattern) (guard : d285887 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d285886 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35211 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d285887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35213 (p : Pattern) (guard : d285888 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d285887 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d285888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35214 (p : Pattern) (guard : d285896 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d285888 p = 1 := by simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35213 p hg
    simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d285896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35215 (p : Pattern) (guard : d285897 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d285896 p = 1 := by simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257213 p = 1 := by simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34986 p hg
    simpa only [d285897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35216 (p : Pattern) (guard : d285898 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d285897 p = 1 := by simpa only [d285898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35215 p hg
    simpa only [d285898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d285898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35217 (p : Pattern) (guard : d285899 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d285898 p = 1 := by simpa only [d285899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35216 p hg
    simpa only [d285899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257215 p = 1 := by simpa only [d285899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34988 p hg
    simpa only [d285899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35218 (p : Pattern) (guard : d285907 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d285907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285899 p = 1 := by simpa only [d285907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35217 p hg
    simpa only [d285907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35219 (p : Pattern) (guard : d285908 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d285908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285907 p = 1 := by simpa only [d285908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35218 p hg
    simpa only [d285908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35220 (p : Pattern) (guard : d285909 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285909, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d285909, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285908 p = 1 := by simpa only [d285909, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35219 p hg
    simpa only [d285909, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35221 (p : Pattern) (guard : d285910 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d285910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285909 p = 1 := by simpa only [d285910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35220 p hg
    simpa only [d285910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35222 (p : Pattern) (guard : d285911 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d285910 p = 1 := by simpa only [d285911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35221 p hg
    simpa only [d285911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d285911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35223 (p : Pattern) (guard : d285912 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d285911 p = 1 := by simpa only [d285912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35222 p hg
    simpa only [d285912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d285912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35224 (p : Pattern) (guard : d285913 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d285912 p = 1 := by simpa only [d285913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35223 p hg
    simpa only [d285913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d285913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35225 (p : Pattern) (guard : d285914 p = 1) : d50390 p ≤ (3 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d285906 p = 1 := by simpa only [d285914, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35187 p hg
    simpa only [d285914, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285913 p = 1 := by simpa only [d285914, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35224 p hg
    simpa only [d285914, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35226 (p : Pattern) (guard : d130 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare35227 (p : Pattern) (guard : d33213 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d33213, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35226 p hg
    simpa only [d33213, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33213, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d33213, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35228 (p : Pattern) (guard : d285865 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33213 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35227 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35229 (p : Pattern) (guard : d285866 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d285865 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35228 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35230 (p : Pattern) (guard : d285867 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d285866 p = 1 := by simpa only [d285867, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35229 p hg
    simpa only [d285867, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285867, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d285867, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35231 (p : Pattern) (guard : d285868 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d285867 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35230 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35232 (p : Pattern) (guard : d285869 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35231 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35012 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35233 (p : Pattern) (guard : d285870 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285869 p = 1 := by simpa only [d285870, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35232 p hg
    simpa only [d285870, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285870, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d285870, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35234 (p : Pattern) (guard : d285871 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285870 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35233 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35015 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35235 (p : Pattern) (guard : d285915 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d285915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285871 p = 1 := by simpa only [d285915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35234 p hg
    simpa only [d285915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35236 (p : Pattern) (guard : d285872 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285871 p = 1 := by simpa only [d285872, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d285872, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285872, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d285872, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35237 (p : Pattern) (guard : d285916 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285915 p = 1 := by simpa only [d285916, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35235 p hg
    simpa only [d285916, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285872 p = 1 := by simpa only [d285916, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35236 p hg
    simpa only [d285916, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35238 (p : Pattern) (guard : d130 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare35239 (p : Pattern) (guard : d33213 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d33213, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35238 p hg
    simpa only [d33213, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33213, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d33213, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35240 (p : Pattern) (guard : d285865 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33213 p = 1 := by simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35239 p hg
    simpa only [d285865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35241 (p : Pattern) (guard : d285866 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d285865 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35240 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d285866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35242 (p : Pattern) (guard : d285867 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d285866 p = 1 := by simpa only [d285867, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35241 p hg
    simpa only [d285867, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285867, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d285867, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35243 (p : Pattern) (guard : d285868 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d285867 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35242 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35027 p hg
    simpa only [d285868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35244 (p : Pattern) (guard : d285869 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35243 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35029 p hg
    simpa only [d285869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35245 (p : Pattern) (guard : d285870 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285869 p = 1 := by simpa only [d285870, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35244 p hg
    simpa only [d285870, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285870, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d285870, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35246 (p : Pattern) (guard : d285871 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285870 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35245 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35032 p hg
    simpa only [d285871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35247 (p : Pattern) (guard : d285872 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285871 p = 1 := by simpa only [d285872, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35246 p hg
    simpa only [d285872, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285872, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d285872, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35248 (p : Pattern) (guard : d285873 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285872 p = 1 := by simpa only [d285873, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35247 p hg
    simpa only [d285873, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285873, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d285873, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35249 (p : Pattern) (guard : d285917 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d285916 p = 1 := by simpa only [d285917, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35237 p hg
    simpa only [d285917, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285873 p = 1 := by simpa only [d285917, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35248 p hg
    simpa only [d285917, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
