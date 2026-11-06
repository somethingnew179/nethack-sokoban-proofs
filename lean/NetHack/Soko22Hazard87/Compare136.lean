import NetHack.Soko22Hazard87.Compare135
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34000 (p : Pattern) (guard : d294622 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294621 p = 1 := by simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33999 p hg
    simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34001 (p : Pattern) (guard : d294623 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294622 p = 1 := by simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34000 p hg
    simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34002 (p : Pattern) (guard : d294624 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294623 p = 1 := by simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34001 p hg
    simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34003 (p : Pattern) (guard : d294625 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294624 p = 1 := by simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34002 p hg
    simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34004 (p : Pattern) (guard : d295678 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295678, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295678, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294625 p = 1 := by simpa only [d295678, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34003 p hg
    simpa only [d295678, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34005 (p : Pattern) (guard : d295679 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295678 p = 1 := by simpa only [d295679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d295679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34006 (p : Pattern) (guard : d295680 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295679 p = 1 := by simpa only [d295680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34005 p hg
    simpa only [d295680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34007 (p : Pattern) (guard : d295681 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295680 p = 1 := by simpa only [d295681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34006 p hg
    simpa only [d295681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34008 (p : Pattern) (guard : d295682 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295681 p = 1 := by simpa only [d295682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34007 p hg
    simpa only [d295682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34009 (p : Pattern) (guard : d295683 p = 1) : d50002 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295677 p = 1 := by simpa only [d295683, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33934 p hg
    simpa only [d295683, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295682 p = 1 := by simpa only [d295683, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34008 p hg
    simpa only [d295683, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34010 (p : Pattern) (guard : d0 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34011 (p : Pattern) (guard : d0 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34012 (p : Pattern) (guard : d0 p = 1) : d50020 p ≤ (0 : Int) + d47786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34013 (p : Pattern) (guard : d0 p = 1) : d50029 p ≤ (0 : Int) + d47796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34014 (p : Pattern) (guard : d0 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34015 (p : Pattern) (guard : d0 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34016 (p : Pattern) (guard : d0 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34017 (p : Pattern) (guard : d17 p = 1) : d47630 p ≤ (0 : Int) + d47630 p := by
  omega
theorem compare34018 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34019 (p : Pattern) (guard : d18 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34017 p hg
    simpa only [d18, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34018 p hg
    simpa only [d18, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34020 (p : Pattern) (guard : d19 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34019 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34021 (p : Pattern) (guard : d20 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34020 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34022 (p : Pattern) (guard : d29090 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34021 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34023 (p : Pattern) (guard : d294503 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29090 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34022 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34024 (p : Pattern) (guard : d0 p = 1) : d49809 p ≤ (0 : Int) + d47631 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34025 (p : Pattern) (guard : d294504 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294503 p = 1 := by simpa only [d294504, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34023 p hg
    simpa only [d294504, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294504, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34024 p hg
    simpa only [d294504, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34026 (p : Pattern) (guard : d294505 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294504 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34025 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34027 (p : Pattern) (guard : d294547 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d294547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294505 p = 1 := by simpa only [d294547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34026 p hg
    simpa only [d294547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34028 (p : Pattern) (guard : d294506 p = 1) : d50030 p ≤ (0 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294505 p = 1 := by simpa only [d294506, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33842 p hg
    simpa only [d294506, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294506, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d294506, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34029 (p : Pattern) (guard : d294548 p = 1) : d50031 p ≤ (0 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294547 p = 1 := by simpa only [d294548, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34027 p hg
    simpa only [d294548, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294506 p = 1 := by simpa only [d294548, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34028 p hg
    simpa only [d294548, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34030 (p : Pattern) (guard : d0 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34031 (p : Pattern) (guard : d17 p = 1) : d47634 p ≤ (0 : Int) + d47634 p := by
  omega
theorem compare34032 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34033 (p : Pattern) (guard : d18 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34031 p hg
    simpa only [d18, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34032 p hg
    simpa only [d18, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34034 (p : Pattern) (guard : d19 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34033 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34035 (p : Pattern) (guard : d20 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34034 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34036 (p : Pattern) (guard : d29090 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34035 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34037 (p : Pattern) (guard : d294503 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29090 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34036 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34038 (p : Pattern) (guard : d0 p = 1) : d49812 p ≤ (0 : Int) + d47635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34039 (p : Pattern) (guard : d294504 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294503 p = 1 := by simpa only [d294504, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34037 p hg
    simpa only [d294504, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294504, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34038 p hg
    simpa only [d294504, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34040 (p : Pattern) (guard : d0 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34041 (p : Pattern) (guard : d294505 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294504 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34039 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34040 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34042 (p : Pattern) (guard : d294506 p = 1) : d49865 p ≤ (0 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294505 p = 1 := by simpa only [d294506, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34041 p hg
    simpa only [d294506, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294506, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294506, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34043 (p : Pattern) (guard : d294507 p = 1) : d49866 p ≤ (0 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294506 p = 1 := by simpa only [d294507, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34042 p hg
    simpa only [d294507, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294507, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294507, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34044 (p : Pattern) (guard : d294549 p = 1) : d50032 p ≤ (0 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294548 p = 1 := by simpa only [d294549, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34029 p hg
    simpa only [d294549, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294507 p = 1 := by simpa only [d294549, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34043 p hg
    simpa only [d294549, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34045 (p : Pattern) (guard : d0 p = 1) : d50035 p ≤ (0 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34046 (p : Pattern) (guard : d294550 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294549 p = 1 := by simpa only [d294550, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34044 p hg
    simpa only [d294550, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294550, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34045 p hg
    simpa only [d294550, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34047 (p : Pattern) (guard : d294551 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d294551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294550 p = 1 := by simpa only [d294551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34046 p hg
    simpa only [d294551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34048 (p : Pattern) (guard : d205892 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d29090 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34022 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34049 (p : Pattern) (guard : d205893 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d205892 p = 1 := by simpa only [d205893, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34048 p hg
    simpa only [d205893, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205893, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34024 p hg
    simpa only [d205893, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34050 (p : Pattern) (guard : d205894 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d205893 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34049 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34051 (p : Pattern) (guard : d205936 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d205936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205894 p = 1 := by simpa only [d205936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34050 p hg
    simpa only [d205936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34052 (p : Pattern) (guard : d205895 p = 1) : d50030 p ≤ (0 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d205894 p = 1 := by simpa only [d205895, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33853 p hg
    simpa only [d205895, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205895, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d205895, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34053 (p : Pattern) (guard : d205937 p = 1) : d50031 p ≤ (0 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d205936 p = 1 := by simpa only [d205937, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34051 p hg
    simpa only [d205937, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205895 p = 1 := by simpa only [d205937, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34052 p hg
    simpa only [d205937, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34054 (p : Pattern) (guard : d205892 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d29090 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34036 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34055 (p : Pattern) (guard : d205893 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d205892 p = 1 := by simpa only [d205893, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34054 p hg
    simpa only [d205893, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205893, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34038 p hg
    simpa only [d205893, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34056 (p : Pattern) (guard : d205894 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d205893 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34055 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34040 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34057 (p : Pattern) (guard : d205895 p = 1) : d49865 p ≤ (0 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d205894 p = 1 := by simpa only [d205895, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34056 p hg
    simpa only [d205895, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205895, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d205895, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34058 (p : Pattern) (guard : d205896 p = 1) : d49866 p ≤ (0 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d205895 p = 1 := by simpa only [d205896, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34057 p hg
    simpa only [d205896, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205896, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d205896, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34059 (p : Pattern) (guard : d205938 p = 1) : d50032 p ≤ (0 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d205937 p = 1 := by simpa only [d205938, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34053 p hg
    simpa only [d205938, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205896 p = 1 := by simpa only [d205938, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34058 p hg
    simpa only [d205938, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34060 (p : Pattern) (guard : d205939 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d205938 p = 1 := by simpa only [d205939, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34059 p hg
    simpa only [d205939, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205939, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34045 p hg
    simpa only [d205939, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34061 (p : Pattern) (guard : d294734 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d294734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205939 p = 1 := by simpa only [d294734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34060 p hg
    simpa only [d294734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34062 (p : Pattern) (guard : d294735 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294551 p = 1 := by simpa only [d294735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34047 p hg
    simpa only [d294735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294734 p = 1 := by simpa only [d294735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34061 p hg
    simpa only [d294735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34063 (p : Pattern) (guard : d205940 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d205939 p = 1 := by simpa only [d205940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34060 p hg
    simpa only [d205940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d205940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34064 (p : Pattern) (guard : d294739 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294734 p = 1 := by simpa only [d294739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34061 p hg
    simpa only [d294739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205940 p = 1 := by simpa only [d294739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34063 p hg
    simpa only [d294739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34065 (p : Pattern) (guard : d294740 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294735 p = 1 := by simpa only [d294740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34062 p hg
    simpa only [d294740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294739 p = 1 := by simpa only [d294740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34064 p hg
    simpa only [d294740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34066 (p : Pattern) (guard : d294741 p = 1) : d50037 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294741, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d294741, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294740 p = 1 := by simpa only [d294741, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34065 p hg
    simpa only [d294741, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34067 (p : Pattern) (guard : d294742 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294742, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d294742, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294741 p = 1 := by simpa only [d294742, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34066 p hg
    simpa only [d294742, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34068 (p : Pattern) (guard : d205941 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d205940 p = 1 := by simpa only [d205941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34063 p hg
    simpa only [d205941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d205941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34069 (p : Pattern) (guard : d294744 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294739 p = 1 := by simpa only [d294744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34064 p hg
    simpa only [d294744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205941 p = 1 := by simpa only [d294744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34068 p hg
    simpa only [d294744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34070 (p : Pattern) (guard : d294745 p = 1) : d50037 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294745, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d294745, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294744 p = 1 := by simpa only [d294745, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34069 p hg
    simpa only [d294745, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34071 (p : Pattern) (guard : d294746 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294746, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d294746, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294745 p = 1 := by simpa only [d294746, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34070 p hg
    simpa only [d294746, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34072 (p : Pattern) (guard : d294747 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294742 p = 1 := by simpa only [d294747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34067 p hg
    simpa only [d294747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294746 p = 1 := by simpa only [d294747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34071 p hg
    simpa only [d294747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34073 (p : Pattern) (guard : d0 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34074 (p : Pattern) (guard : d294752 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294746 p = 1 := by simpa only [d294752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34071 p hg
    simpa only [d294752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d294752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34075 (p : Pattern) (guard : d294753 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294747 p = 1 := by simpa only [d294753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34072 p hg
    simpa only [d294753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294752 p = 1 := by simpa only [d294753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34074 p hg
    simpa only [d294753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34076 (p : Pattern) (guard : d294754 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294753 p = 1 := by simpa only [d294754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34075 p hg
    simpa only [d294754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d294754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34077 (p : Pattern) (guard : d0 p = 1) : d50039 p ≤ (0 : Int) + d47806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34078 (p : Pattern) (guard : d294755 p = 1) : d50040 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294754 p = 1 := by simpa only [d294755, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34076 p hg
    simpa only [d294755, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294755, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34077 p hg
    simpa only [d294755, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34079 (p : Pattern) (guard : d294756 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294756, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d294756, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294755 p = 1 := by simpa only [d294756, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34078 p hg
    simpa only [d294756, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34080 (p : Pattern) (guard : d294761 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294752 p = 1 := by simpa only [d294761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34074 p hg
    simpa only [d294761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d294761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34081 (p : Pattern) (guard : d294762 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294761 p = 1 := by simpa only [d294762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34080 p hg
    simpa only [d294762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d294762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34082 (p : Pattern) (guard : d294763 p = 1) : d50040 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294762 p = 1 := by simpa only [d294763, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34081 p hg
    simpa only [d294763, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294763, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34077 p hg
    simpa only [d294763, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34083 (p : Pattern) (guard : d294764 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294764, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d294764, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294763 p = 1 := by simpa only [d294764, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34082 p hg
    simpa only [d294764, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34084 (p : Pattern) (guard : d294765 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294756 p = 1 := by simpa only [d294765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34079 p hg
    simpa only [d294765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294764 p = 1 := by simpa only [d294765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34083 p hg
    simpa only [d294765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34085 (p : Pattern) (guard : d294766 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294765 p = 1 := by simpa only [d294766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34084 p hg
    simpa only [d294766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34086 (p : Pattern) (guard : d294767 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294766 p = 1 := by simpa only [d294767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34085 p hg
    simpa only [d294767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34087 (p : Pattern) (guard : d294768 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294767 p = 1 := by simpa only [d294768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34086 p hg
    simpa only [d294768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34088 (p : Pattern) (guard : d294782 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294764 p = 1 := by simpa only [d294782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34083 p hg
    simpa only [d294782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34089 (p : Pattern) (guard : d294783 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294782 p = 1 := by simpa only [d294783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34088 p hg
    simpa only [d294783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34090 (p : Pattern) (guard : d294784 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294783 p = 1 := by simpa only [d294784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34089 p hg
    simpa only [d294784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34091 (p : Pattern) (guard : d294785 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294784 p = 1 := by simpa only [d294785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34090 p hg
    simpa only [d294785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34092 (p : Pattern) (guard : d295684 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294768 p = 1 := by simpa only [d295684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34087 p hg
    simpa only [d295684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294785 p = 1 := by simpa only [d295684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34091 p hg
    simpa only [d295684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34093 (p : Pattern) (guard : d295685 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295684 p = 1 := by simpa only [d295685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34092 p hg
    simpa only [d295685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34094 (p : Pattern) (guard : d295686 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295685 p = 1 := by simpa only [d295686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34093 p hg
    simpa only [d295686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34095 (p : Pattern) (guard : d295687 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295686 p = 1 := by simpa only [d295687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34094 p hg
    simpa only [d295687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34096 (p : Pattern) (guard : d295688 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295687 p = 1 := by simpa only [d295688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34095 p hg
    simpa only [d295688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34097 (p : Pattern) (guard : d295689 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295689, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295689, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295688 p = 1 := by simpa only [d295689, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34096 p hg
    simpa only [d295689, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34098 (p : Pattern) (guard : d295690 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295689 p = 1 := by simpa only [d295690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34097 p hg
    simpa only [d295690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34099 (p : Pattern) (guard : d295691 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295690 p = 1 := by simpa only [d295691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34098 p hg
    simpa only [d295691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34100 (p : Pattern) (guard : d295692 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295691 p = 1 := by simpa only [d295692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34099 p hg
    simpa only [d295692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34101 (p : Pattern) (guard : d295693 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295692 p = 1 := by simpa only [d295693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34100 p hg
    simpa only [d295693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34102 (p : Pattern) (guard : d0 p = 1) : d50099 p ≤ (0 : Int) + d47864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34103 (p : Pattern) (guard : d295694 p = 1) : d50100 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295693 p = 1 := by simpa only [d295694, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34101 p hg
    simpa only [d295694, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295694, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34102 p hg
    simpa only [d295694, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34104 (p : Pattern) (guard : d295695 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d295683 p = 1 := by simpa only [d295695, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34009 p hg
    simpa only [d295695, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295694 p = 1 := by simpa only [d295695, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34103 p hg
    simpa only [d295695, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34105 (p : Pattern) (guard : d295696 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295695 p = 1 := by simpa only [d295696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34104 p hg
    simpa only [d295696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34106 (p : Pattern) (guard : d295697 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295696 p = 1 := by simpa only [d295697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34105 p hg
    simpa only [d295697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34107 (p : Pattern) (guard : d295698 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295697 p = 1 := by simpa only [d295698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34106 p hg
    simpa only [d295698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34108 (p : Pattern) (guard : d295699 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295698 p = 1 := by simpa only [d295699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34107 p hg
    simpa only [d295699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34109 (p : Pattern) (guard : d295700 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295699 p = 1 := by simpa only [d295700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34108 p hg
    simpa only [d295700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34110 (p : Pattern) (guard : d295701 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295700 p = 1 := by simpa only [d295701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34109 p hg
    simpa only [d295701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34111 (p : Pattern) (guard : d295702 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295701 p = 1 := by simpa only [d295702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34110 p hg
    simpa only [d295702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34112 (p : Pattern) (guard : d295703 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295702 p = 1 := by simpa only [d295703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34111 p hg
    simpa only [d295703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34113 (p : Pattern) (guard : d131 p = 1) : d47617 p ≤ (0 : Int) + d47617 p := by
  omega
theorem compare34114 (p : Pattern) (guard : d25432 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d25432, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34113 p hg
    simpa only [d25432, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25432, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33833 p hg
    simpa only [d25432, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34115 (p : Pattern) (guard : d25433 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25432 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34114 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34116 (p : Pattern) (guard : d25434 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25433 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34115 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34117 (p : Pattern) (guard : d205998 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25434 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34116 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34118 (p : Pattern) (guard : d294647 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205998 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34117 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34119 (p : Pattern) (guard : d294648 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294647 p = 1 := by simpa only [d294648, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34118 p hg
    simpa only [d294648, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294648, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33839 p hg
    simpa only [d294648, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34120 (p : Pattern) (guard : d294649 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294648 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34119 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33841 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34121 (p : Pattern) (guard : d294650 p = 1) : d49838 p ≤ (0 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294649 p = 1 := by simpa only [d294650, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34120 p hg
    simpa only [d294650, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294650, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33843 p hg
    simpa only [d294650, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34122 (p : Pattern) (guard : d294651 p = 1) : d49841 p ≤ (0 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294650 p = 1 := by simpa only [d294651, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34121 p hg
    simpa only [d294651, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294651, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33845 p hg
    simpa only [d294651, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34123 (p : Pattern) (guard : d294652 p = 1) : d49864 p ≤ (0 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294652, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33830 p hg
    simpa only [d294652, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294651 p = 1 := by simpa only [d294652, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34122 p hg
    simpa only [d294652, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34124 (p : Pattern) (guard : d294653 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294652 p = 1 := by simpa only [d294653, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34123 p hg
    simpa only [d294653, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294653, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33848 p hg
    simpa only [d294653, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34125 (p : Pattern) (guard : d294654 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294653 p = 1 := by simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34124 p hg
    simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34126 (p : Pattern) (guard : d293369 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d205998 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34117 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34127 (p : Pattern) (guard : d293370 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293369 p = 1 := by simpa only [d293370, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34126 p hg
    simpa only [d293370, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293370, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33839 p hg
    simpa only [d293370, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34128 (p : Pattern) (guard : d293371 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293370 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34127 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33841 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34129 (p : Pattern) (guard : d293372 p = 1) : d49838 p ≤ (0 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293371 p = 1 := by simpa only [d293372, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34128 p hg
    simpa only [d293372, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293372, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33843 p hg
    simpa only [d293372, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34130 (p : Pattern) (guard : d293373 p = 1) : d49841 p ≤ (0 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293372 p = 1 := by simpa only [d293373, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34129 p hg
    simpa only [d293373, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293373, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33845 p hg
    simpa only [d293373, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34131 (p : Pattern) (guard : d293374 p = 1) : d49864 p ≤ (0 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293374, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33830 p hg
    simpa only [d293374, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293373 p = 1 := by simpa only [d293374, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34130 p hg
    simpa only [d293374, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34132 (p : Pattern) (guard : d293375 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293374 p = 1 := by simpa only [d293375, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34131 p hg
    simpa only [d293375, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293375, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33848 p hg
    simpa only [d293375, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34133 (p : Pattern) (guard : d294806 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293375 p = 1 := by simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34132 p hg
    simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34134 (p : Pattern) (guard : d294807 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294654 p = 1 := by simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34125 p hg
    simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294806 p = 1 := by simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34133 p hg
    simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34135 (p : Pattern) (guard : d293631 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293375 p = 1 := by simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34132 p hg
    simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34136 (p : Pattern) (guard : d294808 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294806 p = 1 := by simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34133 p hg
    simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293631 p = 1 := by simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34135 p hg
    simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34137 (p : Pattern) (guard : d294809 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294807 p = 1 := by simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34134 p hg
    simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294808 p = 1 := by simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34136 p hg
    simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34138 (p : Pattern) (guard : d294810 p = 1) : d49869 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294810, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33828 p hg
    simpa only [d294810, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294809 p = 1 := by simpa only [d294810, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34137 p hg
    simpa only [d294810, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34139 (p : Pattern) (guard : d294811 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294811, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d294811, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294810 p = 1 := by simpa only [d294811, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34138 p hg
    simpa only [d294811, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34140 (p : Pattern) (guard : d294812 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293631 p = 1 := by simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34135 p hg
    simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34141 (p : Pattern) (guard : d294813 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294808 p = 1 := by simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34136 p hg
    simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294812 p = 1 := by simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34140 p hg
    simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34142 (p : Pattern) (guard : d294814 p = 1) : d49869 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294814, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33828 p hg
    simpa only [d294814, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294813 p = 1 := by simpa only [d294814, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34141 p hg
    simpa only [d294814, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34143 (p : Pattern) (guard : d294815 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294815, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d294815, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294814 p = 1 := by simpa only [d294815, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34142 p hg
    simpa only [d294815, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34144 (p : Pattern) (guard : d294816 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294811 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34139 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294815 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34143 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34145 (p : Pattern) (guard : d294817 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294815 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34143 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34146 (p : Pattern) (guard : d294818 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294816 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34144 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294817 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34145 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34147 (p : Pattern) (guard : d294819 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294818 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34146 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34148 (p : Pattern) (guard : d294820 p = 1) : d49914 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294819 p = 1 := by simpa only [d294820, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34147 p hg
    simpa only [d294820, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294820, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d294820, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34149 (p : Pattern) (guard : d294821 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294821, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d294821, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294820 p = 1 := by simpa only [d294821, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34148 p hg
    simpa only [d294821, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34150 (p : Pattern) (guard : d294822 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294817 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34145 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34151 (p : Pattern) (guard : d294823 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294822 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34150 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34152 (p : Pattern) (guard : d294824 p = 1) : d49914 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294823 p = 1 := by simpa only [d294824, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34151 p hg
    simpa only [d294824, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294824, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d294824, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34153 (p : Pattern) (guard : d294825 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294825, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d294825, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294824 p = 1 := by simpa only [d294825, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34152 p hg
    simpa only [d294825, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34154 (p : Pattern) (guard : d294826 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294821 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34149 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294825 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34153 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34155 (p : Pattern) (guard : d294827 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294826 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34154 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34156 (p : Pattern) (guard : d294828 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294827 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34155 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34157 (p : Pattern) (guard : d294829 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294828 p = 1 := by simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34156 p hg
    simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34158 (p : Pattern) (guard : d294830 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294825 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34153 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34159 (p : Pattern) (guard : d294831 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294830 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34158 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34160 (p : Pattern) (guard : d294832 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294831 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34159 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34161 (p : Pattern) (guard : d294833 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294832 p = 1 := by simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34160 p hg
    simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34162 (p : Pattern) (guard : d294834 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294829 p = 1 := by simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34157 p hg
    simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294833 p = 1 := by simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34161 p hg
    simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34163 (p : Pattern) (guard : d294835 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294834 p = 1 := by simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34162 p hg
    simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34164 (p : Pattern) (guard : d294836 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294835 p = 1 := by simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34163 p hg
    simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34165 (p : Pattern) (guard : d294837 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294836 p = 1 := by simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34164 p hg
    simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34166 (p : Pattern) (guard : d294838 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294837 p = 1 := by simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34165 p hg
    simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34167 (p : Pattern) (guard : d294839 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294839, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294839, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294838 p = 1 := by simpa only [d294839, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34166 p hg
    simpa only [d294839, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34168 (p : Pattern) (guard : d294811 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294811, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d294811, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294810 p = 1 := by simpa only [d294811, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34138 p hg
    simpa only [d294811, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34169 (p : Pattern) (guard : d294815 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294815, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d294815, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294814 p = 1 := by simpa only [d294815, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34142 p hg
    simpa only [d294815, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34170 (p : Pattern) (guard : d294816 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294811 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34168 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294815 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34169 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34171 (p : Pattern) (guard : d294817 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294815 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34169 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34172 (p : Pattern) (guard : d294818 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294816 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34170 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294817 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34171 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34173 (p : Pattern) (guard : d294819 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294818 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34172 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34174 (p : Pattern) (guard : d294820 p = 1) : d49894 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294819 p = 1 := by simpa only [d294820, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34173 p hg
    simpa only [d294820, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294820, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d294820, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34175 (p : Pattern) (guard : d294821 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294821, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d294821, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294820 p = 1 := by simpa only [d294821, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34174 p hg
    simpa only [d294821, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34176 (p : Pattern) (guard : d294822 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294817 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34171 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34177 (p : Pattern) (guard : d294823 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294822 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34176 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34178 (p : Pattern) (guard : d294824 p = 1) : d49894 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294823 p = 1 := by simpa only [d294824, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34177 p hg
    simpa only [d294824, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294824, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d294824, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34179 (p : Pattern) (guard : d294825 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294825, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d294825, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294824 p = 1 := by simpa only [d294825, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34178 p hg
    simpa only [d294825, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34180 (p : Pattern) (guard : d294826 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294821 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34175 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294825 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34179 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34181 (p : Pattern) (guard : d294827 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294826 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34180 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34182 (p : Pattern) (guard : d294828 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294827 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34181 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34183 (p : Pattern) (guard : d294829 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294828 p = 1 := by simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34182 p hg
    simpa only [d294829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34184 (p : Pattern) (guard : d294830 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294825 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34179 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34185 (p : Pattern) (guard : d294831 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294830 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34184 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34186 (p : Pattern) (guard : d294832 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294831 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34185 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34187 (p : Pattern) (guard : d294833 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294832 p = 1 := by simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34186 p hg
    simpa only [d294833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34188 (p : Pattern) (guard : d294834 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294829 p = 1 := by simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34183 p hg
    simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294833 p = 1 := by simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34187 p hg
    simpa only [d294834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34189 (p : Pattern) (guard : d294835 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294834 p = 1 := by simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34188 p hg
    simpa only [d294835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34190 (p : Pattern) (guard : d294836 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294835 p = 1 := by simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34189 p hg
    simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34191 (p : Pattern) (guard : d294837 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294836 p = 1 := by simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34190 p hg
    simpa only [d294837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34192 (p : Pattern) (guard : d294838 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294837 p = 1 := by simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34191 p hg
    simpa only [d294838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34193 (p : Pattern) (guard : d294842 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294828 p = 1 := by simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34156 p hg
    simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34194 (p : Pattern) (guard : d294843 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294832 p = 1 := by simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34160 p hg
    simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34195 (p : Pattern) (guard : d294844 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294842 p = 1 := by simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34193 p hg
    simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294843 p = 1 := by simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34194 p hg
    simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34196 (p : Pattern) (guard : d294845 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294844 p = 1 := by simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34195 p hg
    simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34197 (p : Pattern) (guard : d294846 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294845 p = 1 := by simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34196 p hg
    simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34198 (p : Pattern) (guard : d294847 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294846 p = 1 := by simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34197 p hg
    simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34199 (p : Pattern) (guard : d294848 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294847 p = 1 := by simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34198 p hg
    simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34200 (p : Pattern) (guard : d294849 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294838 p = 1 := by simpa only [d294849, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34192 p hg
    simpa only [d294849, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294848 p = 1 := by simpa only [d294849, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34199 p hg
    simpa only [d294849, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34201 (p : Pattern) (guard : d294850 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d294839 p = 1 := by simpa only [d294850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34167 p hg
    simpa only [d294850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294849 p = 1 := by simpa only [d294850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34200 p hg
    simpa only [d294850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34202 (p : Pattern) (guard : d294851 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294850 p = 1 := by simpa only [d294851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34201 p hg
    simpa only [d294851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d294851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34203 (p : Pattern) (guard : d295704 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294851 p = 1 := by simpa only [d295704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34202 p hg
    simpa only [d295704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34204 (p : Pattern) (guard : d295705 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295704 p = 1 := by simpa only [d295705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34203 p hg
    simpa only [d295705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34205 (p : Pattern) (guard : d131 p = 1) : d47706 p ≤ (0 : Int) + d47706 p := by
  omega
theorem compare34206 (p : Pattern) (guard : d25432 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d25432, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34205 p hg
    simpa only [d25432, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25432, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33944 p hg
    simpa only [d25432, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34207 (p : Pattern) (guard : d25433 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25432 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34206 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34208 (p : Pattern) (guard : d25434 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25433 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34207 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34209 (p : Pattern) (guard : d205998 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25434 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34208 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34210 (p : Pattern) (guard : d294647 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205998 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34209 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34211 (p : Pattern) (guard : d294648 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294647 p = 1 := by simpa only [d294648, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34210 p hg
    simpa only [d294648, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294648, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33950 p hg
    simpa only [d294648, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34212 (p : Pattern) (guard : d294649 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294648 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34211 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33952 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34213 (p : Pattern) (guard : d294650 p = 1) : d49957 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294649 p = 1 := by simpa only [d294650, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34212 p hg
    simpa only [d294650, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294650, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d294650, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34214 (p : Pattern) (guard : d294651 p = 1) : d49958 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294650 p = 1 := by simpa only [d294651, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34213 p hg
    simpa only [d294651, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294651, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294651, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34215 (p : Pattern) (guard : d294652 p = 1) : d49978 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294652, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33941 p hg
    simpa only [d294652, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294651 p = 1 := by simpa only [d294652, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34214 p hg
    simpa only [d294652, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34216 (p : Pattern) (guard : d294653 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294652 p = 1 := by simpa only [d294653, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34215 p hg
    simpa only [d294653, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294653, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33958 p hg
    simpa only [d294653, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34217 (p : Pattern) (guard : d294654 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294653 p = 1 := by simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34216 p hg
    simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34218 (p : Pattern) (guard : d293369 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d205998 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34209 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34219 (p : Pattern) (guard : d293370 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293369 p = 1 := by simpa only [d293370, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34218 p hg
    simpa only [d293370, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293370, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33950 p hg
    simpa only [d293370, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34220 (p : Pattern) (guard : d293371 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293370 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34219 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33952 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34221 (p : Pattern) (guard : d293372 p = 1) : d49957 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293371 p = 1 := by simpa only [d293372, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34220 p hg
    simpa only [d293372, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293372, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d293372, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34222 (p : Pattern) (guard : d293373 p = 1) : d49958 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293372 p = 1 := by simpa only [d293373, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34221 p hg
    simpa only [d293373, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293373, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d293373, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34223 (p : Pattern) (guard : d293374 p = 1) : d49978 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293374, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33941 p hg
    simpa only [d293374, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293373 p = 1 := by simpa only [d293374, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34222 p hg
    simpa only [d293374, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34224 (p : Pattern) (guard : d293375 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293374 p = 1 := by simpa only [d293375, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34223 p hg
    simpa only [d293375, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293375, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33958 p hg
    simpa only [d293375, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34225 (p : Pattern) (guard : d294806 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293375 p = 1 := by simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34224 p hg
    simpa only [d294806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34226 (p : Pattern) (guard : d294807 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294654 p = 1 := by simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34217 p hg
    simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294806 p = 1 := by simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34225 p hg
    simpa only [d294807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34227 (p : Pattern) (guard : d293631 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293375 p = 1 := by simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34224 p hg
    simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d293631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34228 (p : Pattern) (guard : d294808 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294806 p = 1 := by simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34225 p hg
    simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293631 p = 1 := by simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34227 p hg
    simpa only [d294808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34229 (p : Pattern) (guard : d294809 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294807 p = 1 := by simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34226 p hg
    simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294808 p = 1 := by simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34228 p hg
    simpa only [d294809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34230 (p : Pattern) (guard : d294810 p = 1) : d49983 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294810, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d294810, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294809 p = 1 := by simpa only [d294810, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34229 p hg
    simpa only [d294810, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34231 (p : Pattern) (guard : d294811 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294811, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d294811, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294810 p = 1 := by simpa only [d294811, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34230 p hg
    simpa only [d294811, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34232 (p : Pattern) (guard : d294812 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293631 p = 1 := by simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34227 p hg
    simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d294812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34233 (p : Pattern) (guard : d294813 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294808 p = 1 := by simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34228 p hg
    simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294812 p = 1 := by simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34232 p hg
    simpa only [d294813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34234 (p : Pattern) (guard : d294814 p = 1) : d49983 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294814, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d294814, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294813 p = 1 := by simpa only [d294814, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34233 p hg
    simpa only [d294814, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34235 (p : Pattern) (guard : d294815 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294815, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d294815, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294814 p = 1 := by simpa only [d294815, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34234 p hg
    simpa only [d294815, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34236 (p : Pattern) (guard : d294816 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294811 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34231 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294815 p = 1 := by simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34235 p hg
    simpa only [d294816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34237 (p : Pattern) (guard : d294817 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294815 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34235 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d294817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34238 (p : Pattern) (guard : d294818 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294816 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34236 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294817 p = 1 := by simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34237 p hg
    simpa only [d294818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34239 (p : Pattern) (guard : d294819 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294818 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34238 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d294819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34240 (p : Pattern) (guard : d294820 p = 1) : d49999 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294819 p = 1 := by simpa only [d294820, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34239 p hg
    simpa only [d294820, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294820, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33984 p hg
    simpa only [d294820, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34241 (p : Pattern) (guard : d294821 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294821, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d294821, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294820 p = 1 := by simpa only [d294821, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34240 p hg
    simpa only [d294821, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34242 (p : Pattern) (guard : d294822 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294817 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34237 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d294822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34243 (p : Pattern) (guard : d294823 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294822 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34242 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d294823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34244 (p : Pattern) (guard : d294824 p = 1) : d49999 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294823 p = 1 := by simpa only [d294824, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34243 p hg
    simpa only [d294824, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294824, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33984 p hg
    simpa only [d294824, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34245 (p : Pattern) (guard : d294825 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294825, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d294825, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294824 p = 1 := by simpa only [d294825, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34244 p hg
    simpa only [d294825, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34246 (p : Pattern) (guard : d294826 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294821 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34241 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294825 p = 1 := by simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34245 p hg
    simpa only [d294826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34247 (p : Pattern) (guard : d294827 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294826 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34246 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34248 (p : Pattern) (guard : d294828 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294827 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34247 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34249 (p : Pattern) (guard : d294842 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294828 p = 1 := by simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34248 p hg
    simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294842, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
