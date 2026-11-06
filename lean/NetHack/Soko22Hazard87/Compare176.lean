import NetHack.Soko22Hazard87.Compare175
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44000 (p : Pattern) (guard : d366685 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366604 p = 1 := by simpa only [d366685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43906 p hg
    simpa only [d366685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44001 (p : Pattern) (guard : d366686 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366606 p = 1 := by simpa only [d366686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43908 p hg
    simpa only [d366686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44002 (p : Pattern) (guard : d366687 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366685 p = 1 := by simpa only [d366687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44000 p hg
    simpa only [d366687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366686 p = 1 := by simpa only [d366687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44001 p hg
    simpa only [d366687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44003 (p : Pattern) (guard : d366688 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366687 p = 1 := by simpa only [d366688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44002 p hg
    simpa only [d366688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44004 (p : Pattern) (guard : d366689 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366688 p = 1 := by simpa only [d366689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44003 p hg
    simpa only [d366689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44005 (p : Pattern) (guard : d366690 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366689 p = 1 := by simpa only [d366690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44004 p hg
    simpa only [d366690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44006 (p : Pattern) (guard : d366691 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366613 p = 1 := by simpa only [d366691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43915 p hg
    simpa only [d366691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44007 (p : Pattern) (guard : d366692 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366616 p = 1 := by simpa only [d366692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43918 p hg
    simpa only [d366692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44008 (p : Pattern) (guard : d366693 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366691 p = 1 := by simpa only [d366693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44006 p hg
    simpa only [d366693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366692 p = 1 := by simpa only [d366693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44007 p hg
    simpa only [d366693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44009 (p : Pattern) (guard : d366694 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366693 p = 1 := by simpa only [d366694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44008 p hg
    simpa only [d366694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44010 (p : Pattern) (guard : d366695 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366694 p = 1 := by simpa only [d366695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44009 p hg
    simpa only [d366695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44011 (p : Pattern) (guard : d366696 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366671 p = 1 := by simpa only [d366696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43953 p hg
    simpa only [d366696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44012 (p : Pattern) (guard : d366697 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366696 p = 1 := by simpa only [d366697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44011 p hg
    simpa only [d366697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366593 p = 1 := by simpa only [d366697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43895 p hg
    simpa only [d366697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44013 (p : Pattern) (guard : d366698 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366697 p = 1 := by simpa only [d366698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44012 p hg
    simpa only [d366698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44014 (p : Pattern) (guard : d366699 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366677 p = 1 := by simpa only [d366699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43959 p hg
    simpa only [d366699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44015 (p : Pattern) (guard : d366700 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366699 p = 1 := by simpa only [d366700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44014 p hg
    simpa only [d366700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44016 (p : Pattern) (guard : d366701 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366700 p = 1 := by simpa only [d366701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44015 p hg
    simpa only [d366701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44017 (p : Pattern) (guard : d366702 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366698 p = 1 := by simpa only [d366702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44013 p hg
    simpa only [d366702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366701 p = 1 := by simpa only [d366702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44016 p hg
    simpa only [d366702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44018 (p : Pattern) (guard : d366703 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d366695 p = 1 := by simpa only [d366703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44010 p hg
    simpa only [d366703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366702 p = 1 := by simpa only [d366703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44017 p hg
    simpa only [d366703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44019 (p : Pattern) (guard : d366704 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d366690 p = 1 := by simpa only [d366704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44005 p hg
    simpa only [d366704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366703 p = 1 := by simpa only [d366704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44018 p hg
    simpa only [d366704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44020 (p : Pattern) (guard : d366705 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366683 p = 1 := by simpa only [d366705, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43999 p hg
    simpa only [d366705, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366704 p = 1 := by simpa only [d366705, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44019 p hg
    simpa only [d366705, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44021 (p : Pattern) (guard : d366706 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366684 p = 1 := by simpa only [d366706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43966 p hg
    simpa only [d366706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366705 p = 1 := by simpa only [d366706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44020 p hg
    simpa only [d366706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44022 (p : Pattern) (guard : d366707 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366584 p = 1 := by simpa only [d366707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43871 p hg
    simpa only [d366707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44023 (p : Pattern) (guard : d366708 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366707 p = 1 := by simpa only [d366708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44022 p hg
    simpa only [d366708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44024 (p : Pattern) (guard : d366709 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366708 p = 1 := by simpa only [d366709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44023 p hg
    simpa only [d366709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44025 (p : Pattern) (guard : d366710 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366709 p = 1 := by simpa only [d366710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44024 p hg
    simpa only [d366710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44026 (p : Pattern) (guard : d366711 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366710 p = 1 := by simpa only [d366711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44025 p hg
    simpa only [d366711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44027 (p : Pattern) (guard : d366712 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366589 p = 1 := by simpa only [d366712, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43894 p hg
    simpa only [d366712, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366711 p = 1 := by simpa only [d366712, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44026 p hg
    simpa only [d366712, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44028 (p : Pattern) (guard : d366707 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366584 p = 1 := by simpa only [d366707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43889 p hg
    simpa only [d366707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44029 (p : Pattern) (guard : d366708 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366707 p = 1 := by simpa only [d366708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44028 p hg
    simpa only [d366708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44030 (p : Pattern) (guard : d366709 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366708 p = 1 := by simpa only [d366709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44029 p hg
    simpa only [d366709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44031 (p : Pattern) (guard : d366710 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366709 p = 1 := by simpa only [d366710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44030 p hg
    simpa only [d366710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44032 (p : Pattern) (guard : d366711 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366710 p = 1 := by simpa only [d366711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44031 p hg
    simpa only [d366711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44033 (p : Pattern) (guard : d366713 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366594 p = 1 := by simpa only [d366713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43896 p hg
    simpa only [d366713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44034 (p : Pattern) (guard : d366714 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366713 p = 1 := by simpa only [d366714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44033 p hg
    simpa only [d366714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44035 (p : Pattern) (guard : d366715 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366714 p = 1 := by simpa only [d366715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44034 p hg
    simpa only [d366715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44036 (p : Pattern) (guard : d366716 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366715 p = 1 := by simpa only [d366716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44035 p hg
    simpa only [d366716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44037 (p : Pattern) (guard : d366717 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366716 p = 1 := by simpa only [d366717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44036 p hg
    simpa only [d366717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44038 (p : Pattern) (guard : d366718 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366711 p = 1 := by simpa only [d366718, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44032 p hg
    simpa only [d366718, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366717 p = 1 := by simpa only [d366718, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44037 p hg
    simpa only [d366718, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44039 (p : Pattern) (guard : d366719 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366712 p = 1 := by simpa only [d366719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44027 p hg
    simpa only [d366719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366718 p = 1 := by simpa only [d366719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44038 p hg
    simpa only [d366719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44040 (p : Pattern) (guard : d366720 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366706 p = 1 := by simpa only [d366720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44021 p hg
    simpa only [d366720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366719 p = 1 := by simpa only [d366720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44039 p hg
    simpa only [d366720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44041 (p : Pattern) (guard : d366721 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366720 p = 1 := by simpa only [d366721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44040 p hg
    simpa only [d366721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44042 (p : Pattern) (guard : d366722 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d366603 p = 1 := by simpa only [d366722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43905 p hg
    simpa only [d366722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366721 p = 1 := by simpa only [d366722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44041 p hg
    simpa only [d366722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44043 (p : Pattern) (guard : d366626 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44044 (p : Pattern) (guard : d366627 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366627, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366627, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366626 p = 1 := by simpa only [d366627, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44043 p hg
    simpa only [d366627, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44045 (p : Pattern) (guard : d366628 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366627 p = 1 := by simpa only [d366628, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44044 p hg
    simpa only [d366628, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366628, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366628, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44046 (p : Pattern) (guard : d366634 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44047 (p : Pattern) (guard : d366635 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366635, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366635, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366634 p = 1 := by simpa only [d366635, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44046 p hg
    simpa only [d366635, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44048 (p : Pattern) (guard : d366636 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366635 p = 1 := by simpa only [d366636, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44047 p hg
    simpa only [d366636, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366636, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366636, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44049 (p : Pattern) (guard : d366637 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366628 p = 1 := by simpa only [d366637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44045 p hg
    simpa only [d366637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366636 p = 1 := by simpa only [d366637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44048 p hg
    simpa only [d366637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44050 (p : Pattern) (guard : d366643 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44051 (p : Pattern) (guard : d366644 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366644, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366644, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366643 p = 1 := by simpa only [d366644, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44050 p hg
    simpa only [d366644, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44052 (p : Pattern) (guard : d366645 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366644 p = 1 := by simpa only [d366645, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44051 p hg
    simpa only [d366645, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366645, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366645, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44053 (p : Pattern) (guard : d366539 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44054 (p : Pattern) (guard : d366540 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366540, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366540, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366539 p = 1 := by simpa only [d366540, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44053 p hg
    simpa only [d366540, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44055 (p : Pattern) (guard : d366541 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366540 p = 1 := by simpa only [d366541, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44054 p hg
    simpa only [d366541, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366541, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366541, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44056 (p : Pattern) (guard : d366646 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366645 p = 1 := by simpa only [d366646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44052 p hg
    simpa only [d366646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366541 p = 1 := by simpa only [d366646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44055 p hg
    simpa only [d366646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44057 (p : Pattern) (guard : d366647 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366637 p = 1 := by simpa only [d366647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44049 p hg
    simpa only [d366647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366646 p = 1 := by simpa only [d366647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44056 p hg
    simpa only [d366647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44058 (p : Pattern) (guard : d366518 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44059 (p : Pattern) (guard : d366519 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366519, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366519, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366518 p = 1 := by simpa only [d366519, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44058 p hg
    simpa only [d366519, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44060 (p : Pattern) (guard : d366520 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366519 p = 1 := by simpa only [d366520, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44059 p hg
    simpa only [d366520, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366520, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366520, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44061 (p : Pattern) (guard : d366530 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44062 (p : Pattern) (guard : d366531 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366531, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366531, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366530 p = 1 := by simpa only [d366531, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44061 p hg
    simpa only [d366531, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44063 (p : Pattern) (guard : d366532 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366531 p = 1 := by simpa only [d366532, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44062 p hg
    simpa only [d366532, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366532, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366532, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44064 (p : Pattern) (guard : d366533 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366520 p = 1 := by simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44060 p hg
    simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366532 p = 1 := by simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44063 p hg
    simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44065 (p : Pattern) (guard : d366547 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44066 (p : Pattern) (guard : d366548 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366548, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366548, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366547 p = 1 := by simpa only [d366548, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44065 p hg
    simpa only [d366548, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44067 (p : Pattern) (guard : d366549 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366548 p = 1 := by simpa only [d366549, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44066 p hg
    simpa only [d366549, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366549, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366549, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44068 (p : Pattern) (guard : d366550 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366541 p = 1 := by simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44055 p hg
    simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44067 p hg
    simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44069 (p : Pattern) (guard : d366551 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366533 p = 1 := by simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44064 p hg
    simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366550 p = 1 := by simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44068 p hg
    simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44070 (p : Pattern) (guard : d366648 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366647 p = 1 := by simpa only [d366648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44057 p hg
    simpa only [d366648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366551 p = 1 := by simpa only [d366648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44069 p hg
    simpa only [d366648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44071 (p : Pattern) (guard : d366649 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366649, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366649, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366648 p = 1 := by simpa only [d366649, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44070 p hg
    simpa only [d366649, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44072 (p : Pattern) (guard : d366650 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366650, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366650, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366649 p = 1 := by simpa only [d366650, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44071 p hg
    simpa only [d366650, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44073 (p : Pattern) (guard : d366656 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44074 (p : Pattern) (guard : d366657 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366657, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366657, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366656 p = 1 := by simpa only [d366657, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44073 p hg
    simpa only [d366657, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44075 (p : Pattern) (guard : d366658 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366657 p = 1 := by simpa only [d366658, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44074 p hg
    simpa only [d366658, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366658, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366658, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44076 (p : Pattern) (guard : d366659 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366658 p = 1 := by simpa only [d366659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44075 p hg
    simpa only [d366659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44067 p hg
    simpa only [d366659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44077 (p : Pattern) (guard : d366558 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366549 p = 1 := by simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44067 p hg
    simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44078 (p : Pattern) (guard : d366660 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366659 p = 1 := by simpa only [d366660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44076 p hg
    simpa only [d366660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366558 p = 1 := by simpa only [d366660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44077 p hg
    simpa only [d366660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44079 (p : Pattern) (guard : d366661 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366551 p = 1 := by simpa only [d366661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44069 p hg
    simpa only [d366661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366660 p = 1 := by simpa only [d366661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44078 p hg
    simpa only [d366661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44080 (p : Pattern) (guard : d366662 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366662, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366662, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366661 p = 1 := by simpa only [d366662, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44079 p hg
    simpa only [d366662, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44081 (p : Pattern) (guard : d366663 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366663, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366663, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366662 p = 1 := by simpa only [d366663, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44080 p hg
    simpa only [d366663, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44082 (p : Pattern) (guard : d366664 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366650 p = 1 := by simpa only [d366664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44072 p hg
    simpa only [d366664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366663 p = 1 := by simpa only [d366664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44081 p hg
    simpa only [d366664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44083 (p : Pattern) (guard : d366554 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44084 (p : Pattern) (guard : d366555 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366555, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366555, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366554 p = 1 := by simpa only [d366555, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44083 p hg
    simpa only [d366555, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44085 (p : Pattern) (guard : d366556 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366555 p = 1 := by simpa only [d366556, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44084 p hg
    simpa only [d366556, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366556, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366556, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44086 (p : Pattern) (guard : d366557 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366556 p = 1 := by simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44085 p hg
    simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44067 p hg
    simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44087 (p : Pattern) (guard : d366559 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366557 p = 1 := by simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44086 p hg
    simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366558 p = 1 := by simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44077 p hg
    simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44088 (p : Pattern) (guard : d366560 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366551 p = 1 := by simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44069 p hg
    simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366559 p = 1 := by simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44087 p hg
    simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44089 (p : Pattern) (guard : d366561 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366561, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366561, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366560 p = 1 := by simpa only [d366561, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44088 p hg
    simpa only [d366561, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44090 (p : Pattern) (guard : d366562 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366562, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366562, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366561 p = 1 := by simpa only [d366562, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44089 p hg
    simpa only [d366562, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44091 (p : Pattern) (guard : d366563 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366558 p = 1 := by simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44077 p hg
    simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44092 (p : Pattern) (guard : d366564 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366559 p = 1 := by simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44087 p hg
    simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366563 p = 1 := by simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44091 p hg
    simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44093 (p : Pattern) (guard : d366565 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366565, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366565, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366564 p = 1 := by simpa only [d366565, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44092 p hg
    simpa only [d366565, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44094 (p : Pattern) (guard : d366566 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366566, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366566, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366565 p = 1 := by simpa only [d366566, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44093 p hg
    simpa only [d366566, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44095 (p : Pattern) (guard : d366567 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366562 p = 1 := by simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44090 p hg
    simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366566 p = 1 := by simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44094 p hg
    simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44096 (p : Pattern) (guard : d366665 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366664 p = 1 := by simpa only [d366665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44082 p hg
    simpa only [d366665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366567 p = 1 := by simpa only [d366665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44095 p hg
    simpa only [d366665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44097 (p : Pattern) (guard : d366666 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366665 p = 1 := by simpa only [d366666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44096 p hg
    simpa only [d366666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44098 (p : Pattern) (guard : d366667 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366666 p = 1 := by simpa only [d366667, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44097 p hg
    simpa only [d366667, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366667, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d366667, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44099 (p : Pattern) (guard : d366668 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366668, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d366668, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366667 p = 1 := by simpa only [d366668, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44098 p hg
    simpa only [d366668, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44100 (p : Pattern) (guard : d366568 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366566 p = 1 := by simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44094 p hg
    simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44101 (p : Pattern) (guard : d366569 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366567 p = 1 := by simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44095 p hg
    simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366568 p = 1 := by simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44100 p hg
    simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44102 (p : Pattern) (guard : d366570 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366569 p = 1 := by simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44101 p hg
    simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44103 (p : Pattern) (guard : d366571 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366570 p = 1 := by simpa only [d366571, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44102 p hg
    simpa only [d366571, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366571, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d366571, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44104 (p : Pattern) (guard : d366572 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366572, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d366572, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366571 p = 1 := by simpa only [d366572, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44103 p hg
    simpa only [d366572, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44105 (p : Pattern) (guard : d366669 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366668 p = 1 := by simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44099 p hg
    simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366572 p = 1 := by simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44104 p hg
    simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44106 (p : Pattern) (guard : d366670 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366669 p = 1 := by simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44105 p hg
    simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44107 (p : Pattern) (guard : d366671 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366670 p = 1 := by simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44106 p hg
    simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44108 (p : Pattern) (guard : d366696 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366671 p = 1 := by simpa only [d366696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44107 p hg
    simpa only [d366696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44109 (p : Pattern) (guard : d366573 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366568 p = 1 := by simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44100 p hg
    simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44110 (p : Pattern) (guard : d366574 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366573 p = 1 := by simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44109 p hg
    simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44111 (p : Pattern) (guard : d366575 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366574 p = 1 := by simpa only [d366575, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44110 p hg
    simpa only [d366575, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366575, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d366575, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44112 (p : Pattern) (guard : d366576 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366576, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d366576, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366575 p = 1 := by simpa only [d366576, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44111 p hg
    simpa only [d366576, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44113 (p : Pattern) (guard : d366577 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366572 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44104 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366576 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44112 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44114 (p : Pattern) (guard : d366578 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366577 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44113 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44115 (p : Pattern) (guard : d366579 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366578 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44114 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44116 (p : Pattern) (guard : d366593 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366579 p = 1 := by simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44115 p hg
    simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44117 (p : Pattern) (guard : d366697 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366696 p = 1 := by simpa only [d366697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44108 p hg
    simpa only [d366697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366593 p = 1 := by simpa only [d366697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44116 p hg
    simpa only [d366697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44118 (p : Pattern) (guard : d366698 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366697 p = 1 := by simpa only [d366698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44117 p hg
    simpa only [d366698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44119 (p : Pattern) (guard : d366675 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366572 p = 1 := by simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44104 p hg
    simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44120 (p : Pattern) (guard : d366676 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366675 p = 1 := by simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44119 p hg
    simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44121 (p : Pattern) (guard : d366677 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366676 p = 1 := by simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44120 p hg
    simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44122 (p : Pattern) (guard : d366699 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366677 p = 1 := by simpa only [d366699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44121 p hg
    simpa only [d366699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44123 (p : Pattern) (guard : d366700 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366699 p = 1 := by simpa only [d366700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44122 p hg
    simpa only [d366700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44124 (p : Pattern) (guard : d366701 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366700 p = 1 := by simpa only [d366701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44123 p hg
    simpa only [d366701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44125 (p : Pattern) (guard : d366702 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366698 p = 1 := by simpa only [d366702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44118 p hg
    simpa only [d366702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366701 p = 1 := by simpa only [d366702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44124 p hg
    simpa only [d366702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44126 (p : Pattern) (guard : d366723 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366702 p = 1 := by simpa only [d366723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44125 p hg
    simpa only [d366723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44127 (p : Pattern) (guard : d366724 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366723 p = 1 := by simpa only [d366724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44126 p hg
    simpa only [d366724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44128 (p : Pattern) (guard : d366725 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366725, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366725, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366724 p = 1 := by simpa only [d366725, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44127 p hg
    simpa only [d366725, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44129 (p : Pattern) (guard : d366726 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366725 p = 1 := by simpa only [d366726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44128 p hg
    simpa only [d366726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44130 (p : Pattern) (guard : d366581 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366576 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44112 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44131 (p : Pattern) (guard : d366582 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366581 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44130 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44132 (p : Pattern) (guard : d366583 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366582 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44131 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44133 (p : Pattern) (guard : d366594 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366583 p = 1 := by simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44132 p hg
    simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44134 (p : Pattern) (guard : d366713 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366594 p = 1 := by simpa only [d366713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44133 p hg
    simpa only [d366713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44135 (p : Pattern) (guard : d366714 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366713 p = 1 := by simpa only [d366714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44134 p hg
    simpa only [d366714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44136 (p : Pattern) (guard : d366715 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366714 p = 1 := by simpa only [d366715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44135 p hg
    simpa only [d366715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44137 (p : Pattern) (guard : d366716 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366715 p = 1 := by simpa only [d366716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44136 p hg
    simpa only [d366716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44138 (p : Pattern) (guard : d366717 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366716 p = 1 := by simpa only [d366717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44137 p hg
    simpa only [d366717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44139 (p : Pattern) (guard : d366727 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366727, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366727, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366717 p = 1 := by simpa only [d366727, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44138 p hg
    simpa only [d366727, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44140 (p : Pattern) (guard : d366728 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366727 p = 1 := by simpa only [d366728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44139 p hg
    simpa only [d366728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44141 (p : Pattern) (guard : d366729 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366726 p = 1 := by simpa only [d366729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44129 p hg
    simpa only [d366729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366728 p = 1 := by simpa only [d366729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44140 p hg
    simpa only [d366729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44142 (p : Pattern) (guard : d366730 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366729 p = 1 := by simpa only [d366730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44141 p hg
    simpa only [d366730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44143 (p : Pattern) (guard : d366731 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d366730 p = 1 := by simpa only [d366731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44142 p hg
    simpa only [d366731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d366731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44144 (p : Pattern) (guard : d366732 p = 1) : d51470 p ≤ (8 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d366722 p = 1 := by simpa only [d366732, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44042 p hg
    simpa only [d366732, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366731 p = 1 := by simpa only [d366732, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44143 p hg
    simpa only [d366732, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44145 (p : Pattern) (guard : d43406 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d43406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d43406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42940 p = 1 := by simpa only [d43406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43394 p hg
    simpa only [d43406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44146 (p : Pattern) (guard : d43407 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43406 p = 1 := by simpa only [d43407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44145 p hg
    simpa only [d43407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d43407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44147 (p : Pattern) (guard : d43408 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d43407 p = 1 := by simpa only [d43408, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44146 p hg
    simpa only [d43408, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43408, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d43408, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44148 (p : Pattern) (guard : d43409 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d43409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d43409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43408 p = 1 := by simpa only [d43409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44147 p hg
    simpa only [d43409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44149 (p : Pattern) (guard : d332204 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d332204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d332204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43409 p = 1 := by simpa only [d332204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44148 p hg
    simpa only [d332204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44150 (p : Pattern) (guard : d332205 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d332204 p = 1 := by simpa only [d332205, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44149 p hg
    simpa only [d332205, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d332205, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d332205, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44151 (p : Pattern) (guard : d1087 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43000 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44152 (p : Pattern) (guard : d366506 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d42941 p = 1 := by simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43395 p hg
    simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44151 p hg
    simpa only [d366506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44153 (p : Pattern) (guard : d366507 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366506 p = 1 := by simpa only [d366507, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44152 p hg
    simpa only [d366507, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366507, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d366507, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44154 (p : Pattern) (guard : d366508 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366507 p = 1 := by simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44153 p hg
    simpa only [d366508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44155 (p : Pattern) (guard : d366621 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d43408 p = 1 := by simpa only [d366621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44147 p hg
    simpa only [d366621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366349 p = 1 := by simpa only [d366621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43719 p hg
    simpa only [d366621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44156 (p : Pattern) (guard : d366622 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366508 p = 1 := by simpa only [d366622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44154 p hg
    simpa only [d366622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366621 p = 1 := by simpa only [d366622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44155 p hg
    simpa only [d366622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44157 (p : Pattern) (guard : d366623 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366622 p = 1 := by simpa only [d366623, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44156 p hg
    simpa only [d366623, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366623, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366623, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44158 (p : Pattern) (guard : d366624 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d332205 p = 1 := by simpa only [d366624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44150 p hg
    simpa only [d366624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366623 p = 1 := by simpa only [d366624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44157 p hg
    simpa only [d366624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44159 (p : Pattern) (guard : d366733 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366733, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366733, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366624 p = 1 := by simpa only [d366733, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44158 p hg
    simpa only [d366733, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44160 (p : Pattern) (guard : d366625 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44161 (p : Pattern) (guard : d366734 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366733 p = 1 := by simpa only [d366734, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44159 p hg
    simpa only [d366734, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366625 p = 1 := by simpa only [d366734, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44160 p hg
    simpa only [d366734, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44162 (p : Pattern) (guard : d366626 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44163 (p : Pattern) (guard : d366735 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366734 p = 1 := by simpa only [d366735, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44161 p hg
    simpa only [d366735, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366626 p = 1 := by simpa only [d366735, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44162 p hg
    simpa only [d366735, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44164 (p : Pattern) (guard : d366736 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366735 p = 1 := by simpa only [d366736, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44163 p hg
    simpa only [d366736, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366736, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366736, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44165 (p : Pattern) (guard : d366509 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366508 p = 1 := by simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44154 p hg
    simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366350 p = 1 := by simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43720 p hg
    simpa only [d366509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44166 (p : Pattern) (guard : d366510 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366509 p = 1 := by simpa only [d366510, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44165 p hg
    simpa only [d366510, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366510, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366510, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44167 (p : Pattern) (guard : d32698 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43392 p hg
    simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44168 (p : Pattern) (guard : d308523 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32698 p = 1 := by simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44167 p hg
    simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44169 (p : Pattern) (guard : d308524 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d308523 p = 1 := by simpa only [d308524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44168 p hg
    simpa only [d308524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d308524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44170 (p : Pattern) (guard : d366629 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d308524 p = 1 := by simpa only [d366629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44169 p hg
    simpa only [d366629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366362 p = 1 := by simpa only [d366629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43736 p hg
    simpa only [d366629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44171 (p : Pattern) (guard : d366630 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366629 p = 1 := by simpa only [d366630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44170 p hg
    simpa only [d366630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44172 (p : Pattern) (guard : d366631 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366630 p = 1 := by simpa only [d366631, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44171 p hg
    simpa only [d366631, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366631, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366631, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44173 (p : Pattern) (guard : d366632 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366510 p = 1 := by simpa only [d366632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44166 p hg
    simpa only [d366632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366631 p = 1 := by simpa only [d366632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44172 p hg
    simpa only [d366632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44174 (p : Pattern) (guard : d366737 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366737, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366737, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366632 p = 1 := by simpa only [d366737, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44173 p hg
    simpa only [d366737, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44175 (p : Pattern) (guard : d366633 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44176 (p : Pattern) (guard : d366738 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366737 p = 1 := by simpa only [d366738, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44174 p hg
    simpa only [d366738, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366633 p = 1 := by simpa only [d366738, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44175 p hg
    simpa only [d366738, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44177 (p : Pattern) (guard : d366634 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44178 (p : Pattern) (guard : d366739 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366738 p = 1 := by simpa only [d366739, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44176 p hg
    simpa only [d366739, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366634 p = 1 := by simpa only [d366739, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44177 p hg
    simpa only [d366739, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44179 (p : Pattern) (guard : d366740 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366739 p = 1 := by simpa only [d366740, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44178 p hg
    simpa only [d366740, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366740, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366740, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44180 (p : Pattern) (guard : d366741 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366736 p = 1 := by simpa only [d366741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44164 p hg
    simpa only [d366741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366740 p = 1 := by simpa only [d366741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44179 p hg
    simpa only [d366741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44181 (p : Pattern) (guard : d366638 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308524 p = 1 := by simpa only [d366638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44169 p hg
    simpa only [d366638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44182 (p : Pattern) (guard : d366639 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366638 p = 1 := by simpa only [d366639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44181 p hg
    simpa only [d366639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44183 (p : Pattern) (guard : d366640 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366639 p = 1 := by simpa only [d366640, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44182 p hg
    simpa only [d366640, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366640, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366640, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44184 (p : Pattern) (guard : d366641 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366640 p = 1 := by simpa only [d366641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44183 p hg
    simpa only [d366641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366631 p = 1 := by simpa only [d366641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44172 p hg
    simpa only [d366641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44185 (p : Pattern) (guard : d366742 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366742, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366742, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366641 p = 1 := by simpa only [d366742, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44184 p hg
    simpa only [d366742, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44186 (p : Pattern) (guard : d366642 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44187 (p : Pattern) (guard : d366743 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366742 p = 1 := by simpa only [d366743, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44185 p hg
    simpa only [d366743, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366642 p = 1 := by simpa only [d366743, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44186 p hg
    simpa only [d366743, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44188 (p : Pattern) (guard : d366643 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44189 (p : Pattern) (guard : d366744 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366743 p = 1 := by simpa only [d366744, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44187 p hg
    simpa only [d366744, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366643 p = 1 := by simpa only [d366744, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44188 p hg
    simpa only [d366744, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44190 (p : Pattern) (guard : d366745 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366744 p = 1 := by simpa only [d366745, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44189 p hg
    simpa only [d366745, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366745, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366745, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44191 (p : Pattern) (guard : d366534 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366507 p = 1 := by simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44153 p hg
    simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366362 p = 1 := by simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43736 p hg
    simpa only [d366534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44192 (p : Pattern) (guard : d366535 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366534 p = 1 := by simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44191 p hg
    simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44193 (p : Pattern) (guard : d366536 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366535 p = 1 := by simpa only [d366536, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44192 p hg
    simpa only [d366536, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366536, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366536, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44194 (p : Pattern) (guard : d366523 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32153 p = 1 := by simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43734 p hg
    simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43001 p hg
    simpa only [d366523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44195 (p : Pattern) (guard : d366524 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366523 p = 1 := by simpa only [d366524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44194 p hg
    simpa only [d366524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d366524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44196 (p : Pattern) (guard : d366525 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366524 p = 1 := by simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44195 p hg
    simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43004 p hg
    simpa only [d366525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44197 (p : Pattern) (guard : d366526 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366525 p = 1 := by simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44196 p hg
    simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44198 (p : Pattern) (guard : d366527 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366526 p = 1 := by simpa only [d366527, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44197 p hg
    simpa only [d366527, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366527, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366527, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44199 (p : Pattern) (guard : d366537 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366536 p = 1 := by simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44193 p hg
    simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366527 p = 1 := by simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44198 p hg
    simpa only [d366537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44200 (p : Pattern) (guard : d366746 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366746, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366746, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366537 p = 1 := by simpa only [d366746, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44199 p hg
    simpa only [d366746, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44201 (p : Pattern) (guard : d366538 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44202 (p : Pattern) (guard : d366747 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366746 p = 1 := by simpa only [d366747, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44200 p hg
    simpa only [d366747, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366538 p = 1 := by simpa only [d366747, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44201 p hg
    simpa only [d366747, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44203 (p : Pattern) (guard : d366539 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44204 (p : Pattern) (guard : d366748 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366747 p = 1 := by simpa only [d366748, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44202 p hg
    simpa only [d366748, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366539 p = 1 := by simpa only [d366748, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44203 p hg
    simpa only [d366748, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44205 (p : Pattern) (guard : d366749 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366748 p = 1 := by simpa only [d366749, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44204 p hg
    simpa only [d366749, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366749, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366749, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44206 (p : Pattern) (guard : d366750 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366745 p = 1 := by simpa only [d366750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44190 p hg
    simpa only [d366750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366749 p = 1 := by simpa only [d366750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44205 p hg
    simpa only [d366750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44207 (p : Pattern) (guard : d366751 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366741 p = 1 := by simpa only [d366751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44180 p hg
    simpa only [d366751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366750 p = 1 := by simpa only [d366751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44206 p hg
    simpa only [d366751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44208 (p : Pattern) (guard : d366511 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d342818 p = 1 := by simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43185 p hg
    simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43001 p hg
    simpa only [d366511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44209 (p : Pattern) (guard : d366512 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366511 p = 1 := by simpa only [d366512, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44208 p hg
    simpa only [d366512, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366512, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d366512, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44210 (p : Pattern) (guard : d366513 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366507 p = 1 := by simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44153 p hg
    simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366512 p = 1 := by simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44209 p hg
    simpa only [d366513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44211 (p : Pattern) (guard : d366514 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366513 p = 1 := by simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44210 p hg
    simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366353 p = 1 := by simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43723 p hg
    simpa only [d366514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44212 (p : Pattern) (guard : d366515 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366514 p = 1 := by simpa only [d366515, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44211 p hg
    simpa only [d366515, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366515, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366515, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44213 (p : Pattern) (guard : d366516 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366510 p = 1 := by simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44166 p hg
    simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366515 p = 1 := by simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44212 p hg
    simpa only [d366516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44214 (p : Pattern) (guard : d366752 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366752, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366752, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366516 p = 1 := by simpa only [d366752, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44213 p hg
    simpa only [d366752, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44215 (p : Pattern) (guard : d366517 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44216 (p : Pattern) (guard : d366753 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366752 p = 1 := by simpa only [d366753, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44214 p hg
    simpa only [d366753, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366517 p = 1 := by simpa only [d366753, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44215 p hg
    simpa only [d366753, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44217 (p : Pattern) (guard : d366518 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44218 (p : Pattern) (guard : d366754 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366753 p = 1 := by simpa only [d366754, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44216 p hg
    simpa only [d366754, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366518 p = 1 := by simpa only [d366754, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44217 p hg
    simpa only [d366754, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44219 (p : Pattern) (guard : d366755 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366754 p = 1 := by simpa only [d366755, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44218 p hg
    simpa only [d366755, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366755, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366755, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44220 (p : Pattern) (guard : d366521 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366513 p = 1 := by simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44210 p hg
    simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342821 p = 1 := by simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43188 p hg
    simpa only [d366521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44221 (p : Pattern) (guard : d366522 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366521 p = 1 := by simpa only [d366522, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44220 p hg
    simpa only [d366522, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366522, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366522, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44222 (p : Pattern) (guard : d366528 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366522 p = 1 := by simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44221 p hg
    simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366527 p = 1 := by simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44198 p hg
    simpa only [d366528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44223 (p : Pattern) (guard : d366756 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366756, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366756, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366528 p = 1 := by simpa only [d366756, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44222 p hg
    simpa only [d366756, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44224 (p : Pattern) (guard : d366529 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44225 (p : Pattern) (guard : d366757 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366756 p = 1 := by simpa only [d366757, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44223 p hg
    simpa only [d366757, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366529 p = 1 := by simpa only [d366757, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44224 p hg
    simpa only [d366757, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44226 (p : Pattern) (guard : d366530 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44227 (p : Pattern) (guard : d366758 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366757 p = 1 := by simpa only [d366758, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44225 p hg
    simpa only [d366758, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366530 p = 1 := by simpa only [d366758, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44226 p hg
    simpa only [d366758, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44228 (p : Pattern) (guard : d366759 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366758 p = 1 := by simpa only [d366759, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44227 p hg
    simpa only [d366759, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366759, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366759, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44229 (p : Pattern) (guard : d366760 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366755 p = 1 := by simpa only [d366760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44219 p hg
    simpa only [d366760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366759 p = 1 := by simpa only [d366760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44228 p hg
    simpa only [d366760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44230 (p : Pattern) (guard : d366542 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366512 p = 1 := by simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44209 p hg
    simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43004 p hg
    simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44231 (p : Pattern) (guard : d366543 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366542 p = 1 := by simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44230 p hg
    simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342710 p = 1 := by simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43006 p hg
    simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44232 (p : Pattern) (guard : d366544 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366543 p = 1 := by simpa only [d366544, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44231 p hg
    simpa only [d366544, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366544, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366544, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44233 (p : Pattern) (guard : d366545 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366544 p = 1 := by simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44232 p hg
    simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43010 p hg
    simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44234 (p : Pattern) (guard : d366761 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366761, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366761, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366545 p = 1 := by simpa only [d366761, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44233 p hg
    simpa only [d366761, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44235 (p : Pattern) (guard : d366546 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44236 (p : Pattern) (guard : d366762 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366761 p = 1 := by simpa only [d366762, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44234 p hg
    simpa only [d366762, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366546 p = 1 := by simpa only [d366762, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44235 p hg
    simpa only [d366762, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44237 (p : Pattern) (guard : d366547 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44238 (p : Pattern) (guard : d366763 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366762 p = 1 := by simpa only [d366763, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44236 p hg
    simpa only [d366763, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366547 p = 1 := by simpa only [d366763, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44237 p hg
    simpa only [d366763, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44239 (p : Pattern) (guard : d366764 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366763 p = 1 := by simpa only [d366764, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44238 p hg
    simpa only [d366764, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366764, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366764, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44240 (p : Pattern) (guard : d366765 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366749 p = 1 := by simpa only [d366765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44205 p hg
    simpa only [d366765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366764 p = 1 := by simpa only [d366765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44239 p hg
    simpa only [d366765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44241 (p : Pattern) (guard : d366766 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366760 p = 1 := by simpa only [d366766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44229 p hg
    simpa only [d366766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366765 p = 1 := by simpa only [d366766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44240 p hg
    simpa only [d366766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44242 (p : Pattern) (guard : d366767 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366751 p = 1 := by simpa only [d366767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44207 p hg
    simpa only [d366767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366766 p = 1 := by simpa only [d366767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44241 p hg
    simpa only [d366767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44243 (p : Pattern) (guard : d366768 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366768, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d366768, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366767 p = 1 := by simpa only [d366768, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44242 p hg
    simpa only [d366768, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44244 (p : Pattern) (guard : d366769 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366769, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d366769, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366768 p = 1 := by simpa only [d366769, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44243 p hg
    simpa only [d366769, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44245 (p : Pattern) (guard : d366651 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366507 p = 1 := by simpa only [d366651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44153 p hg
    simpa only [d366651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366524 p = 1 := by simpa only [d366651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44195 p hg
    simpa only [d366651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44246 (p : Pattern) (guard : d366652 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366651 p = 1 := by simpa only [d366652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44245 p hg
    simpa only [d366652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44247 (p : Pattern) (guard : d366653 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366652 p = 1 := by simpa only [d366653, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44246 p hg
    simpa only [d366653, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366653, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366653, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44248 (p : Pattern) (guard : d366654 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366653 p = 1 := by simpa only [d366654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44247 p hg
    simpa only [d366654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366527 p = 1 := by simpa only [d366654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44198 p hg
    simpa only [d366654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44249 (p : Pattern) (guard : d366770 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366770, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366770, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366654 p = 1 := by simpa only [d366770, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44248 p hg
    simpa only [d366770, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
