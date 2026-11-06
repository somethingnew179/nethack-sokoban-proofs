import NetHack.Soko22Hazard87.Compare115
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29000 (p : Pattern) (guard : d258726 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258718 p = 1 := by simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28999 p hg
    simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29001 (p : Pattern) (guard : d258727 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258726 p = 1 := by simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29000 p hg
    simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29002 (p : Pattern) (guard : d258728 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258727 p = 1 := by simpa only [d258728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29001 p hg
    simpa only [d258728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29003 (p : Pattern) (guard : d258729 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258728 p = 1 := by simpa only [d258729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29002 p hg
    simpa only [d258729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29004 (p : Pattern) (guard : d258730 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258729 p = 1 := by simpa only [d258730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29003 p hg
    simpa only [d258730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29005 (p : Pattern) (guard : d258731 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258730 p = 1 := by simpa only [d258731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29004 p hg
    simpa only [d258731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29006 (p : Pattern) (guard : d258737 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258737, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258737, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258731 p = 1 := by simpa only [d258737, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29005 p hg
    simpa only [d258737, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29007 (p : Pattern) (guard : d258738 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d258738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258737 p = 1 := by simpa only [d258738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29006 p hg
    simpa only [d258738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29008 (p : Pattern) (guard : d258739 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258738 p = 1 := by simpa only [d258739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29007 p hg
    simpa only [d258739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d258739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29009 (p : Pattern) (guard : d258740 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258739 p = 1 := by simpa only [d258740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29008 p hg
    simpa only [d258740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d258740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29010 (p : Pattern) (guard : d258741 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d258740 p = 1 := by simpa only [d258741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29009 p hg
    simpa only [d258741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d258741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29011 (p : Pattern) (guard : d258742 p = 1) : d47768 p ≤ (-1 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d258736 p = 1 := by simpa only [d258742, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28955 p hg
    simpa only [d258742, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258741 p = 1 := by simpa only [d258742, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29010 p hg
    simpa only [d258742, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29012 (p : Pattern) (guard : d0 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29013 (p : Pattern) (guard : d0 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29014 (p : Pattern) (guard : d0 p = 1) : d47786 p ≤ (-1 : Int) + d253425 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29015 (p : Pattern) (guard : d0 p = 1) : d47796 p ≤ (-1 : Int) + d253433 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29016 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29017 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29018 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (-1 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29019 (p : Pattern) (guard : d44880 p = 1) : d2 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44880, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29018 p hg
    simpa only [d44880, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13 p = 1 := by simpa only [d44880, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4721 p hg
    simpa only [d44880, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29020 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (-1 : Int) + d47629 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29021 (p : Pattern) (guard : d46864 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29019 p hg
    simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29020 p hg
    simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29022 (p : Pattern) (guard : d46865 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29021 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29023 (p : Pattern) (guard : d46866 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29022 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29024 (p : Pattern) (guard : d258695 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46866 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29023 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29025 (p : Pattern) (guard : d258696 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258695 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29024 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29026 (p : Pattern) (guard : d258697 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258696 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29025 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29027 (p : Pattern) (guard : d258698 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258697 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29026 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29028 (p : Pattern) (guard : d258699 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258698 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29027 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29029 (p : Pattern) (guard : d0 p = 1) : d47631 p ≤ (-1 : Int) + d253284 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29030 (p : Pattern) (guard : d258700 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258699 p = 1 := by simpa only [d258700, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29028 p hg
    simpa only [d258700, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258700, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d258700, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29031 (p : Pattern) (guard : d258701 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258700 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29030 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29032 (p : Pattern) (guard : d258743 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d258743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258701 p = 1 := by simpa only [d258743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29031 p hg
    simpa only [d258743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29033 (p : Pattern) (guard : d258702 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258701 p = 1 := by simpa only [d258702, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28914 p hg
    simpa only [d258702, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258702, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258702, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29034 (p : Pattern) (guard : d258744 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258743 p = 1 := by simpa only [d258744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29032 p hg
    simpa only [d258744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258702 p = 1 := by simpa only [d258744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29033 p hg
    simpa only [d258744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29035 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29036 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (-1 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29037 (p : Pattern) (guard : d44880 p = 1) : d6 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44880, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29036 p hg
    simpa only [d44880, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13 p = 1 := by simpa only [d44880, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4737 p hg
    simpa only [d44880, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29038 (p : Pattern) (guard : d0 p = 1) : d47633 p ≤ (-1 : Int) + d47633 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29039 (p : Pattern) (guard : d46864 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29037 p hg
    simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29038 p hg
    simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29040 (p : Pattern) (guard : d46865 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29039 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29041 (p : Pattern) (guard : d46866 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29040 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29042 (p : Pattern) (guard : d258695 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46866 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29041 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29043 (p : Pattern) (guard : d258696 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258695 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29042 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29044 (p : Pattern) (guard : d258697 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258696 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29043 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29045 (p : Pattern) (guard : d258698 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258697 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29044 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29046 (p : Pattern) (guard : d258699 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258698 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29045 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29047 (p : Pattern) (guard : d0 p = 1) : d47635 p ≤ (-1 : Int) + d253286 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29048 (p : Pattern) (guard : d258700 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258699 p = 1 := by simpa only [d258700, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29046 p hg
    simpa only [d258700, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258700, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d258700, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29049 (p : Pattern) (guard : d0 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29050 (p : Pattern) (guard : d258701 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258700 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29048 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29049 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29051 (p : Pattern) (guard : d258702 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258701 p = 1 := by simpa only [d258702, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29050 p hg
    simpa only [d258702, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258702, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258702, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29052 (p : Pattern) (guard : d258703 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258702 p = 1 := by simpa only [d258703, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29051 p hg
    simpa only [d258703, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258703, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258703, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29053 (p : Pattern) (guard : d258745 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d258744 p = 1 := by simpa only [d258745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29034 p hg
    simpa only [d258745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258703 p = 1 := by simpa only [d258745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29052 p hg
    simpa only [d258745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29054 (p : Pattern) (guard : d0 p = 1) : d47802 p ≤ (-1 : Int) + d253439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29055 (p : Pattern) (guard : d258746 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258745 p = 1 := by simpa only [d258746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29053 p hg
    simpa only [d258746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d258746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29056 (p : Pattern) (guard : d0 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29057 (p : Pattern) (guard : d258747 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258746 p = 1 := by simpa only [d258747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29055 p hg
    simpa only [d258747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d258747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29058 (p : Pattern) (guard : d258748 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258747 p = 1 := by simpa only [d258748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29057 p hg
    simpa only [d258748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d258748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29059 (p : Pattern) (guard : d258749 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258748 p = 1 := by simpa only [d258749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29058 p hg
    simpa only [d258749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d258749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29060 (p : Pattern) (guard : d258750 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258750, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d258750, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258749 p = 1 := by simpa only [d258750, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29059 p hg
    simpa only [d258750, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29061 (p : Pattern) (guard : d258751 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258751, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d258751, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258750 p = 1 := by simpa only [d258751, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29060 p hg
    simpa only [d258751, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29062 (p : Pattern) (guard : d0 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29063 (p : Pattern) (guard : d258752 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258751 p = 1 := by simpa only [d258752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29061 p hg
    simpa only [d258752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d258752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29064 (p : Pattern) (guard : d258753 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258752 p = 1 := by simpa only [d258753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29063 p hg
    simpa only [d258753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d258753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29065 (p : Pattern) (guard : d258754 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258753 p = 1 := by simpa only [d258754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29064 p hg
    simpa only [d258754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d258754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29066 (p : Pattern) (guard : d0 p = 1) : d47806 p ≤ (-1 : Int) + d253443 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29067 (p : Pattern) (guard : d258755 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258754 p = 1 := by simpa only [d258755, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29065 p hg
    simpa only [d258755, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258755, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d258755, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29068 (p : Pattern) (guard : d258756 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258756, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d258756, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258755 p = 1 := by simpa only [d258756, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29067 p hg
    simpa only [d258756, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29069 (p : Pattern) (guard : d258757 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258756 p = 1 := by simpa only [d258757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29068 p hg
    simpa only [d258757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29070 (p : Pattern) (guard : d258758 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258757 p = 1 := by simpa only [d258758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29069 p hg
    simpa only [d258758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29071 (p : Pattern) (guard : d258759 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258758 p = 1 := by simpa only [d258759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29070 p hg
    simpa only [d258759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29072 (p : Pattern) (guard : d258760 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258759 p = 1 := by simpa only [d258760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29071 p hg
    simpa only [d258760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29073 (p : Pattern) (guard : d258761 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258760 p = 1 := by simpa only [d258761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29072 p hg
    simpa only [d258761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29074 (p : Pattern) (guard : d258762 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258761 p = 1 := by simpa only [d258762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29073 p hg
    simpa only [d258762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29075 (p : Pattern) (guard : d258763 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258762 p = 1 := by simpa only [d258763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29074 p hg
    simpa only [d258763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29076 (p : Pattern) (guard : d258764 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258763 p = 1 := by simpa only [d258764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29075 p hg
    simpa only [d258764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29077 (p : Pattern) (guard : d258765 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d258765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258764 p = 1 := by simpa only [d258765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29076 p hg
    simpa only [d258765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29078 (p : Pattern) (guard : d258766 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258766, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258766, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258765 p = 1 := by simpa only [d258766, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29077 p hg
    simpa only [d258766, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29079 (p : Pattern) (guard : d258767 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d258767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258766 p = 1 := by simpa only [d258767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29078 p hg
    simpa only [d258767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29080 (p : Pattern) (guard : d258768 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258767 p = 1 := by simpa only [d258768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29079 p hg
    simpa only [d258768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d258768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29081 (p : Pattern) (guard : d258769 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258768 p = 1 := by simpa only [d258769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29080 p hg
    simpa only [d258769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d258769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29082 (p : Pattern) (guard : d258770 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d258769 p = 1 := by simpa only [d258770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29081 p hg
    simpa only [d258770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d258770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29083 (p : Pattern) (guard : d0 p = 1) : d47864 p ≤ (-1 : Int) + d253501 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29084 (p : Pattern) (guard : d258771 p = 1) : d47865 p ≤ (-1 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d258770 p = 1 := by simpa only [d258771, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29082 p hg
    simpa only [d258771, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258771, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29083 p hg
    simpa only [d258771, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29085 (p : Pattern) (guard : d258772 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d258742 p = 1 := by simpa only [d258772, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29011 p hg
    simpa only [d258772, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258771 p = 1 := by simpa only [d258772, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29084 p hg
    simpa only [d258772, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29086 (p : Pattern) (guard : d258773 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258772 p = 1 := by simpa only [d258773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29085 p hg
    simpa only [d258773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29087 (p : Pattern) (guard : d258774 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258773 p = 1 := by simpa only [d258774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29086 p hg
    simpa only [d258774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29088 (p : Pattern) (guard : d258775 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258774 p = 1 := by simpa only [d258775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29087 p hg
    simpa only [d258775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29089 (p : Pattern) (guard : d258776 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258775 p = 1 := by simpa only [d258776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29088 p hg
    simpa only [d258776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29090 (p : Pattern) (guard : d258777 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258776 p = 1 := by simpa only [d258777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29089 p hg
    simpa only [d258777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29091 (p : Pattern) (guard : d258778 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d258778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258777 p = 1 := by simpa only [d258778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29090 p hg
    simpa only [d258778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29092 (p : Pattern) (guard : d258779 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258720 p = 1 := by simpa only [d258779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28939 p hg
    simpa only [d258779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29093 (p : Pattern) (guard : d258780 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258779 p = 1 := by simpa only [d258780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29092 p hg
    simpa only [d258780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29094 (p : Pattern) (guard : d258781 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258780 p = 1 := by simpa only [d258781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29093 p hg
    simpa only [d258781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29095 (p : Pattern) (guard : d258782 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258781 p = 1 := by simpa only [d258782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29094 p hg
    simpa only [d258782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29096 (p : Pattern) (guard : d258783 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258782 p = 1 := by simpa only [d258783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29095 p hg
    simpa only [d258783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29097 (p : Pattern) (guard : d258784 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258783 p = 1 := by simpa only [d258784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29096 p hg
    simpa only [d258784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29098 (p : Pattern) (guard : d258785 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258784 p = 1 := by simpa only [d258785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29097 p hg
    simpa only [d258785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29099 (p : Pattern) (guard : d258786 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258727 p = 1 := by simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28946 p hg
    simpa only [d258786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29100 (p : Pattern) (guard : d258787 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258786 p = 1 := by simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29099 p hg
    simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29101 (p : Pattern) (guard : d258788 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258787 p = 1 := by simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29100 p hg
    simpa only [d258788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29102 (p : Pattern) (guard : d258789 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258788 p = 1 := by simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29101 p hg
    simpa only [d258789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29103 (p : Pattern) (guard : d258790 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d258782 p = 1 := by simpa only [d258790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29095 p hg
    simpa only [d258790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258789 p = 1 := by simpa only [d258790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29102 p hg
    simpa only [d258790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29104 (p : Pattern) (guard : d258791 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d258783 p = 1 := by simpa only [d258791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29096 p hg
    simpa only [d258791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258790 p = 1 := by simpa only [d258791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29103 p hg
    simpa only [d258791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29105 (p : Pattern) (guard : d258792 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258791 p = 1 := by simpa only [d258792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29104 p hg
    simpa only [d258792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29106 (p : Pattern) (guard : d258793 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258785 p = 1 := by simpa only [d258793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29098 p hg
    simpa only [d258793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258792 p = 1 := by simpa only [d258793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29105 p hg
    simpa only [d258793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29107 (p : Pattern) (guard : d258794 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258717 p = 1 := by simpa only [d258794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28936 p hg
    simpa only [d258794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29108 (p : Pattern) (guard : d258795 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258794 p = 1 := by simpa only [d258795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29107 p hg
    simpa only [d258795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29109 (p : Pattern) (guard : d258796 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258795 p = 1 := by simpa only [d258796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29108 p hg
    simpa only [d258796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29110 (p : Pattern) (guard : d258797 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258796 p = 1 := by simpa only [d258797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29109 p hg
    simpa only [d258797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29111 (p : Pattern) (guard : d258798 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258797 p = 1 := by simpa only [d258798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29110 p hg
    simpa only [d258798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29112 (p : Pattern) (guard : d258799 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258798 p = 1 := by simpa only [d258799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29111 p hg
    simpa only [d258799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29113 (p : Pattern) (guard : d258800 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258716 p = 1 := by simpa only [d258800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28935 p hg
    simpa only [d258800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29114 (p : Pattern) (guard : d258801 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258800 p = 1 := by simpa only [d258801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29113 p hg
    simpa only [d258801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29115 (p : Pattern) (guard : d258802 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258801 p = 1 := by simpa only [d258802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29114 p hg
    simpa only [d258802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29116 (p : Pattern) (guard : d258803 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258802 p = 1 := by simpa only [d258803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29115 p hg
    simpa only [d258803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29117 (p : Pattern) (guard : d258804 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258803 p = 1 := by simpa only [d258804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29116 p hg
    simpa only [d258804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29118 (p : Pattern) (guard : d258805 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258804 p = 1 := by simpa only [d258805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29117 p hg
    simpa only [d258805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29119 (p : Pattern) (guard : d307 p = 1) : d4 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d307, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28900 p hg
    simpa only [d307, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d127 p = 1 := by simpa only [d307, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4812 p hg
    simpa only [d307, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29120 (p : Pattern) (guard : d1997 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29119 p hg
    simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28902 p hg
    simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29121 (p : Pattern) (guard : d258806 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29120 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46864 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28903 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29122 (p : Pattern) (guard : d258807 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29121 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46865 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28904 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29123 (p : Pattern) (guard : d258808 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258807 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29122 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29124 (p : Pattern) (guard : d258809 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258808 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29123 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29125 (p : Pattern) (guard : d258810 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258809 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29124 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29126 (p : Pattern) (guard : d258811 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258810 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29125 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29127 (p : Pattern) (guard : d258812 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29126 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258698 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28909 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29128 (p : Pattern) (guard : d258813 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258812 p = 1 := by simpa only [d258813, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29127 p hg
    simpa only [d258813, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258813, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d258813, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29129 (p : Pattern) (guard : d258814 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258813 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29128 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28912 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29130 (p : Pattern) (guard : d258815 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258814 p = 1 := by simpa only [d258815, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29129 p hg
    simpa only [d258815, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258815, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d258815, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29131 (p : Pattern) (guard : d258816 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258815 p = 1 := by simpa only [d258816, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29130 p hg
    simpa only [d258816, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258816, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d258816, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29132 (p : Pattern) (guard : d258817 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258817, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d258817, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258816 p = 1 := by simpa only [d258817, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29131 p hg
    simpa only [d258817, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29133 (p : Pattern) (guard : d258818 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258817 p = 1 := by simpa only [d258818, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29132 p hg
    simpa only [d258818, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258818, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d258818, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29134 (p : Pattern) (guard : d258819 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258818 p = 1 := by simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29133 p hg
    simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258705 p = 1 := by simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28921 p hg
    simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29135 (p : Pattern) (guard : d258820 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258819 p = 1 := by simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29134 p hg
    simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258706 p = 1 := by simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28923 p hg
    simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29136 (p : Pattern) (guard : d258821 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258820 p = 1 := by simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29135 p hg
    simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258707 p = 1 := by simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28924 p hg
    simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29137 (p : Pattern) (guard : d258822 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258822, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d258822, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258821 p = 1 := by simpa only [d258822, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29136 p hg
    simpa only [d258822, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29138 (p : Pattern) (guard : d258823 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258823, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d258823, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258822 p = 1 := by simpa only [d258823, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29137 p hg
    simpa only [d258823, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29139 (p : Pattern) (guard : d258824 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258823 p = 1 := by simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29138 p hg
    simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258710 p = 1 := by simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28927 p hg
    simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29140 (p : Pattern) (guard : d258825 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258824 p = 1 := by simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29139 p hg
    simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258711 p = 1 := by simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28929 p hg
    simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29141 (p : Pattern) (guard : d258826 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258825 p = 1 := by simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29140 p hg
    simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29142 (p : Pattern) (guard : d258827 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258826 p = 1 := by simpa only [d258827, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29141 p hg
    simpa only [d258827, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258827, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d258827, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29143 (p : Pattern) (guard : d258828 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258828, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d258828, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258827 p = 1 := by simpa only [d258828, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29142 p hg
    simpa only [d258828, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29144 (p : Pattern) (guard : d258829 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258828 p = 1 := by simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29143 p hg
    simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258715 p = 1 := by simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28934 p hg
    simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29145 (p : Pattern) (guard : d258830 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258829 p = 1 := by simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29144 p hg
    simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29146 (p : Pattern) (guard : d258831 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258830 p = 1 := by simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29145 p hg
    simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29147 (p : Pattern) (guard : d258832 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258831 p = 1 := by simpa only [d258832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29146 p hg
    simpa only [d258832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29148 (p : Pattern) (guard : d258833 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258832 p = 1 := by simpa only [d258833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29147 p hg
    simpa only [d258833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258719 p = 1 := by simpa only [d258833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28938 p hg
    simpa only [d258833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29149 (p : Pattern) (guard : d258834 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258833 p = 1 := by simpa only [d258834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29148 p hg
    simpa only [d258834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29150 (p : Pattern) (guard : d258835 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258834 p = 1 := by simpa only [d258835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29149 p hg
    simpa only [d258835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258721 p = 1 := by simpa only [d258835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28940 p hg
    simpa only [d258835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29151 (p : Pattern) (guard : d258836 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d258805 p = 1 := by simpa only [d258836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29118 p hg
    simpa only [d258836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258835 p = 1 := by simpa only [d258836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29150 p hg
    simpa only [d258836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29152 (p : Pattern) (guard : d258837 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d258799 p = 1 := by simpa only [d258837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29112 p hg
    simpa only [d258837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258836 p = 1 := by simpa only [d258837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29151 p hg
    simpa only [d258837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29153 (p : Pattern) (guard : d258838 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258837 p = 1 := by simpa only [d258838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29152 p hg
    simpa only [d258838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29154 (p : Pattern) (guard : d258839 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258794 p = 1 := by simpa only [d258839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29107 p hg
    simpa only [d258839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29155 (p : Pattern) (guard : d258840 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258839 p = 1 := by simpa only [d258840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29154 p hg
    simpa only [d258840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29156 (p : Pattern) (guard : d258841 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258840 p = 1 := by simpa only [d258841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29155 p hg
    simpa only [d258841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29157 (p : Pattern) (guard : d258842 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258841 p = 1 := by simpa only [d258842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29156 p hg
    simpa only [d258842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29158 (p : Pattern) (guard : d258843 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258842 p = 1 := by simpa only [d258843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29157 p hg
    simpa only [d258843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29159 (p : Pattern) (guard : d258844 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258801 p = 1 := by simpa only [d258844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29114 p hg
    simpa only [d258844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29160 (p : Pattern) (guard : d258845 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258844 p = 1 := by simpa only [d258845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29159 p hg
    simpa only [d258845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29161 (p : Pattern) (guard : d258846 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258845 p = 1 := by simpa only [d258846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29160 p hg
    simpa only [d258846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29162 (p : Pattern) (guard : d258847 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258846 p = 1 := by simpa only [d258847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29161 p hg
    simpa only [d258847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29163 (p : Pattern) (guard : d258848 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258831 p = 1 := by simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29146 p hg
    simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29164 (p : Pattern) (guard : d258849 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258848 p = 1 := by simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29163 p hg
    simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258726 p = 1 := by simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28945 p hg
    simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29165 (p : Pattern) (guard : d258850 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258849 p = 1 := by simpa only [d258850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29164 p hg
    simpa only [d258850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29166 (p : Pattern) (guard : d258851 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258850 p = 1 := by simpa only [d258851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29165 p hg
    simpa only [d258851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258728 p = 1 := by simpa only [d258851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28947 p hg
    simpa only [d258851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29167 (p : Pattern) (guard : d258852 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d258847 p = 1 := by simpa only [d258852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29162 p hg
    simpa only [d258852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258851 p = 1 := by simpa only [d258852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29166 p hg
    simpa only [d258852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29168 (p : Pattern) (guard : d258853 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d258843 p = 1 := by simpa only [d258853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29158 p hg
    simpa only [d258853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258852 p = 1 := by simpa only [d258853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29167 p hg
    simpa only [d258853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29169 (p : Pattern) (guard : d258854 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d258837 p = 1 := by simpa only [d258854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29152 p hg
    simpa only [d258854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258853 p = 1 := by simpa only [d258854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29168 p hg
    simpa only [d258854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29170 (p : Pattern) (guard : d258855 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d258838 p = 1 := by simpa only [d258855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29153 p hg
    simpa only [d258855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258854 p = 1 := by simpa only [d258855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29169 p hg
    simpa only [d258855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29171 (p : Pattern) (guard : d258856 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d258782 p = 1 := by simpa only [d258856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29095 p hg
    simpa only [d258856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29172 (p : Pattern) (guard : d258857 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d258856 p = 1 := by simpa only [d258857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29171 p hg
    simpa only [d258857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29173 (p : Pattern) (guard : d258858 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258855 p = 1 := by simpa only [d258858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29170 p hg
    simpa only [d258858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258857 p = 1 := by simpa only [d258858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29172 p hg
    simpa only [d258858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29174 (p : Pattern) (guard : d258859 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258858 p = 1 := by simpa only [d258859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29173 p hg
    simpa only [d258859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29175 (p : Pattern) (guard : d258860 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d258793 p = 1 := by simpa only [d258860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29106 p hg
    simpa only [d258860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258859 p = 1 := by simpa only [d258860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29174 p hg
    simpa only [d258860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29176 (p : Pattern) (guard : d307 p = 1) : d5 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d307, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28963 p hg
    simpa only [d307, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d127 p = 1 := by simpa only [d307, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4885 p hg
    simpa only [d307, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29177 (p : Pattern) (guard : d1997 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29176 p hg
    simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28965 p hg
    simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29178 (p : Pattern) (guard : d258806 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29177 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46864 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28966 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29179 (p : Pattern) (guard : d258807 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29178 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46865 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28967 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29180 (p : Pattern) (guard : d258808 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258807 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29179 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29181 (p : Pattern) (guard : d258809 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258808 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29180 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29182 (p : Pattern) (guard : d258810 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258809 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29181 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29183 (p : Pattern) (guard : d258811 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258810 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29182 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29184 (p : Pattern) (guard : d258812 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29183 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258698 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28972 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29185 (p : Pattern) (guard : d258813 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258812 p = 1 := by simpa only [d258813, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29184 p hg
    simpa only [d258813, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258813, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d258813, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29186 (p : Pattern) (guard : d258814 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258813 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29185 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28975 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29187 (p : Pattern) (guard : d258815 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258814 p = 1 := by simpa only [d258815, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29186 p hg
    simpa only [d258815, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258815, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258815, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29188 (p : Pattern) (guard : d258816 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258815 p = 1 := by simpa only [d258816, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29187 p hg
    simpa only [d258816, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258816, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258816, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29189 (p : Pattern) (guard : d258817 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258817, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d258817, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258816 p = 1 := by simpa only [d258817, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29188 p hg
    simpa only [d258817, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29190 (p : Pattern) (guard : d258818 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258817 p = 1 := by simpa only [d258818, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29189 p hg
    simpa only [d258818, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258818, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d258818, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29191 (p : Pattern) (guard : d258819 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258818 p = 1 := by simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29190 p hg
    simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258705 p = 1 := by simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28983 p hg
    simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29192 (p : Pattern) (guard : d258820 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258819 p = 1 := by simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29191 p hg
    simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258706 p = 1 := by simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28985 p hg
    simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29193 (p : Pattern) (guard : d258821 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258820 p = 1 := by simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29192 p hg
    simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258707 p = 1 := by simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28986 p hg
    simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29194 (p : Pattern) (guard : d258822 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258822, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d258822, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258821 p = 1 := by simpa only [d258822, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29193 p hg
    simpa only [d258822, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29195 (p : Pattern) (guard : d258823 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258823, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d258823, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258822 p = 1 := by simpa only [d258823, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29194 p hg
    simpa only [d258823, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29196 (p : Pattern) (guard : d258824 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258823 p = 1 := by simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29195 p hg
    simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258710 p = 1 := by simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28989 p hg
    simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29197 (p : Pattern) (guard : d258825 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258824 p = 1 := by simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29196 p hg
    simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258711 p = 1 := by simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28991 p hg
    simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29198 (p : Pattern) (guard : d258826 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258825 p = 1 := by simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29197 p hg
    simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29199 (p : Pattern) (guard : d258827 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258826 p = 1 := by simpa only [d258827, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29198 p hg
    simpa only [d258827, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258827, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d258827, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29200 (p : Pattern) (guard : d258828 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258828, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d258828, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258827 p = 1 := by simpa only [d258828, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29199 p hg
    simpa only [d258828, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29201 (p : Pattern) (guard : d258829 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258828 p = 1 := by simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29200 p hg
    simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258715 p = 1 := by simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28996 p hg
    simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29202 (p : Pattern) (guard : d258830 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258829 p = 1 := by simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29201 p hg
    simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29203 (p : Pattern) (guard : d258831 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258830 p = 1 := by simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29202 p hg
    simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29204 (p : Pattern) (guard : d258848 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258831 p = 1 := by simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29203 p hg
    simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29205 (p : Pattern) (guard : d258849 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258848 p = 1 := by simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29204 p hg
    simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258726 p = 1 := by simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29000 p hg
    simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29206 (p : Pattern) (guard : d258850 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258849 p = 1 := by simpa only [d258850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29205 p hg
    simpa only [d258850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29207 (p : Pattern) (guard : d258851 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258850 p = 1 := by simpa only [d258851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29206 p hg
    simpa only [d258851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258728 p = 1 := by simpa only [d258851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29002 p hg
    simpa only [d258851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29208 (p : Pattern) (guard : d258861 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258851 p = 1 := by simpa only [d258861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29207 p hg
    simpa only [d258861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29209 (p : Pattern) (guard : d258862 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258861 p = 1 := by simpa only [d258862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29208 p hg
    simpa only [d258862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29210 (p : Pattern) (guard : d258863 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258863, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258863, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258862 p = 1 := by simpa only [d258863, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d258863, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29211 (p : Pattern) (guard : d258864 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d258864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258863 p = 1 := by simpa only [d258864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29210 p hg
    simpa only [d258864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29212 (p : Pattern) (guard : d258865 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258864 p = 1 := by simpa only [d258865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29211 p hg
    simpa only [d258865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d258865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29213 (p : Pattern) (guard : d258866 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258865 p = 1 := by simpa only [d258866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29212 p hg
    simpa only [d258866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d258866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29214 (p : Pattern) (guard : d258867 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d258866 p = 1 := by simpa only [d258867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29213 p hg
    simpa only [d258867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d258867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29215 (p : Pattern) (guard : d258868 p = 1) : d47768 p ≤ (-1 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d258860 p = 1 := by simpa only [d258868, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29175 p hg
    simpa only [d258868, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258867 p = 1 := by simpa only [d258868, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29214 p hg
    simpa only [d258868, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29216 (p : Pattern) (guard : d307 p = 1) : d2 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d307, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29018 p hg
    simpa only [d307, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d127 p = 1 := by simpa only [d307, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4944 p hg
    simpa only [d307, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29217 (p : Pattern) (guard : d1997 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29216 p hg
    simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29020 p hg
    simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29218 (p : Pattern) (guard : d258806 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29217 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46864 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29021 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29219 (p : Pattern) (guard : d258807 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29218 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46865 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29022 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29220 (p : Pattern) (guard : d258808 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258807 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29219 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29221 (p : Pattern) (guard : d258809 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258808 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29220 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29222 (p : Pattern) (guard : d258810 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258809 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29221 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29223 (p : Pattern) (guard : d258811 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258810 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29222 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29224 (p : Pattern) (guard : d258812 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29223 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258698 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29027 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29225 (p : Pattern) (guard : d258813 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258812 p = 1 := by simpa only [d258813, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29224 p hg
    simpa only [d258813, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258813, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d258813, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29226 (p : Pattern) (guard : d258814 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258813 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29225 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29030 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29227 (p : Pattern) (guard : d258869 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d258869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258814 p = 1 := by simpa only [d258869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29226 p hg
    simpa only [d258869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29228 (p : Pattern) (guard : d258815 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258814 p = 1 := by simpa only [d258815, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29129 p hg
    simpa only [d258815, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258815, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258815, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29229 (p : Pattern) (guard : d258870 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258869 p = 1 := by simpa only [d258870, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29227 p hg
    simpa only [d258870, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258815 p = 1 := by simpa only [d258870, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29228 p hg
    simpa only [d258870, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29230 (p : Pattern) (guard : d307 p = 1) : d6 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d307, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29036 p hg
    simpa only [d307, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d127 p = 1 := by simpa only [d307, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4960 p hg
    simpa only [d307, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29231 (p : Pattern) (guard : d1997 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29230 p hg
    simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29038 p hg
    simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29232 (p : Pattern) (guard : d258806 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29231 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46864 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29039 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29233 (p : Pattern) (guard : d258807 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29232 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46865 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29040 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29234 (p : Pattern) (guard : d258808 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258807 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29233 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29235 (p : Pattern) (guard : d258809 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258808 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29234 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29236 (p : Pattern) (guard : d258810 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258809 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29237 (p : Pattern) (guard : d258811 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258810 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29236 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29238 (p : Pattern) (guard : d258812 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29237 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258698 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29045 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29239 (p : Pattern) (guard : d258813 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258812 p = 1 := by simpa only [d258813, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29238 p hg
    simpa only [d258813, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258813, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d258813, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29240 (p : Pattern) (guard : d258814 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258813 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29239 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29048 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29241 (p : Pattern) (guard : d258815 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258814 p = 1 := by simpa only [d258815, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29240 p hg
    simpa only [d258815, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258815, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258815, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29242 (p : Pattern) (guard : d258816 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258815 p = 1 := by simpa only [d258816, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29241 p hg
    simpa only [d258816, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258816, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258816, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29243 (p : Pattern) (guard : d258871 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d258870 p = 1 := by simpa only [d258871, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29229 p hg
    simpa only [d258871, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258816 p = 1 := by simpa only [d258871, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29242 p hg
    simpa only [d258871, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29244 (p : Pattern) (guard : d258872 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258871 p = 1 := by simpa only [d258872, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29243 p hg
    simpa only [d258872, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258872, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d258872, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29245 (p : Pattern) (guard : d258873 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258872 p = 1 := by simpa only [d258873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29244 p hg
    simpa only [d258873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258746 p = 1 := by simpa only [d258873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29055 p hg
    simpa only [d258873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29246 (p : Pattern) (guard : d258874 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258873 p = 1 := by simpa only [d258874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29245 p hg
    simpa only [d258874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258747 p = 1 := by simpa only [d258874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29057 p hg
    simpa only [d258874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29247 (p : Pattern) (guard : d258875 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258874 p = 1 := by simpa only [d258875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29246 p hg
    simpa only [d258875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258748 p = 1 := by simpa only [d258875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29058 p hg
    simpa only [d258875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29248 (p : Pattern) (guard : d258876 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258876, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d258876, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258875 p = 1 := by simpa only [d258876, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29247 p hg
    simpa only [d258876, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29249 (p : Pattern) (guard : d258877 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258877, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d258877, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258876 p = 1 := by simpa only [d258877, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29248 p hg
    simpa only [d258877, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
