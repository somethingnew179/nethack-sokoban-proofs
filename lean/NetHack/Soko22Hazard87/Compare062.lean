import NetHack.Soko22Hazard87.Compare061
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15500 (p : Pattern) (guard : d16826 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16825 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15499 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15501 (p : Pattern) (guard : d16827 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16826 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15500 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15502 (p : Pattern) (guard : d16831 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16817 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15462 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15503 (p : Pattern) (guard : d16832 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16821 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15466 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15504 (p : Pattern) (guard : d16833 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16831 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15502 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16832 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15503 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15505 (p : Pattern) (guard : d16834 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16833 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15504 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15506 (p : Pattern) (guard : d16835 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16834 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15505 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15507 (p : Pattern) (guard : d16836 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16835 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15506 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15508 (p : Pattern) (guard : d16837 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16836 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15507 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15509 (p : Pattern) (guard : d16838 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16827 p = 1 := by simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15501 p hg
    simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16837 p = 1 := by simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15508 p hg
    simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15510 (p : Pattern) (guard : d16839 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16828 p = 1 := by simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15473 p hg
    simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16838 p = 1 := by simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15509 p hg
    simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15511 (p : Pattern) (guard : d16840 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16839 p = 1 := by simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15510 p hg
    simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15512 (p : Pattern) (guard : d16841 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16830 p = 1 := by simpa only [d16841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15475 p hg
    simpa only [d16841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16840 p = 1 := by simpa only [d16841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15511 p hg
    simpa only [d16841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15513 (p : Pattern) (guard : d16842 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16816 p = 1 := by simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15461 p hg
    simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15514 (p : Pattern) (guard : d16843 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16842 p = 1 := by simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15513 p hg
    simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15515 (p : Pattern) (guard : d16844 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16820 p = 1 := by simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15465 p hg
    simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15516 (p : Pattern) (guard : d16845 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16844 p = 1 := by simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15515 p hg
    simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15517 (p : Pattern) (guard : d16846 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16843 p = 1 := by simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15514 p hg
    simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16845 p = 1 := by simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15516 p hg
    simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15518 (p : Pattern) (guard : d16847 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16846 p = 1 := by simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15517 p hg
    simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15519 (p : Pattern) (guard : d16848 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16847 p = 1 := by simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15518 p hg
    simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15520 (p : Pattern) (guard : d16849 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16848 p = 1 := by simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15519 p hg
    simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15521 (p : Pattern) (guard : d16850 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16815 p = 1 := by simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15460 p hg
    simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15522 (p : Pattern) (guard : d16851 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16850 p = 1 := by simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15521 p hg
    simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15523 (p : Pattern) (guard : d16852 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16851 p = 1 := by simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15522 p hg
    simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15524 (p : Pattern) (guard : d16853 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16819 p = 1 := by simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15464 p hg
    simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15525 (p : Pattern) (guard : d16854 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16853 p = 1 := by simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15524 p hg
    simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15526 (p : Pattern) (guard : d16855 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16854 p = 1 := by simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15525 p hg
    simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15527 (p : Pattern) (guard : d16856 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16852 p = 1 := by simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15523 p hg
    simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16855 p = 1 := by simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15526 p hg
    simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15528 (p : Pattern) (guard : d16857 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16856 p = 1 := by simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15527 p hg
    simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15529 (p : Pattern) (guard : d16858 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16857 p = 1 := by simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15528 p hg
    simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15530 (p : Pattern) (guard : d1667 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15531 (p : Pattern) (guard : d1668 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1667 p = 1 := by simpa only [d1668, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15530 p hg
    simpa only [d1668, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1668, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1668, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15532 (p : Pattern) (guard : d16859 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15533 (p : Pattern) (guard : d16860 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16859 p = 1 := by simpa only [d16860, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15532 p hg
    simpa only [d16860, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16860, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d16860, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15534 (p : Pattern) (guard : d16861 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1668 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15531 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16860 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15533 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15535 (p : Pattern) (guard : d15229 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15536 (p : Pattern) (guard : d15230 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15229 p = 1 := by simpa only [d15230, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15535 p hg
    simpa only [d15230, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15230, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d15230, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15537 (p : Pattern) (guard : d16862 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15230 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15536 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15152 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15418 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15538 (p : Pattern) (guard : d16863 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16861 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15534 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16862 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15537 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15539 (p : Pattern) (guard : d16864 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16863 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15538 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16791 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15422 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15540 (p : Pattern) (guard : d16865 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16865, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16865, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16864 p = 1 := by simpa only [d16865, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15539 p hg
    simpa only [d16865, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15541 (p : Pattern) (guard : d16866 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16866, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16866, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16865 p = 1 := by simpa only [d16866, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15540 p hg
    simpa only [d16866, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15542 (p : Pattern) (guard : d13348 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15543 (p : Pattern) (guard : d13349 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13348 p = 1 := by simpa only [d13349, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15542 p hg
    simpa only [d13349, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13349, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d13349, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15544 (p : Pattern) (guard : d16867 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13349 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15543 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15420 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15545 (p : Pattern) (guard : d16868 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16867 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15544 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15428 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15546 (p : Pattern) (guard : d16869 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15422 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16868 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15545 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15547 (p : Pattern) (guard : d16870 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16870, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16870, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16869 p = 1 := by simpa only [d16870, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15546 p hg
    simpa only [d16870, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15548 (p : Pattern) (guard : d16871 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16871, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16871, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16870 p = 1 := by simpa only [d16871, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15547 p hg
    simpa only [d16871, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15549 (p : Pattern) (guard : d16872 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16866 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15541 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16871 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15548 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15550 (p : Pattern) (guard : d16873 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16872 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15549 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16802 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15443 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15551 (p : Pattern) (guard : d16874 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16873 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15550 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15552 (p : Pattern) (guard : d16875 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16874 p = 1 := by simpa only [d16875, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15551 p hg
    simpa only [d16875, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16875, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16875, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15553 (p : Pattern) (guard : d16876 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16876, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16876, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16875 p = 1 := by simpa only [d16876, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15552 p hg
    simpa only [d16876, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15554 (p : Pattern) (guard : d16877 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16801 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15442 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15555 (p : Pattern) (guard : d16878 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15443 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16877 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15554 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15556 (p : Pattern) (guard : d16879 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16878 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15555 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15557 (p : Pattern) (guard : d16880 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16879 p = 1 := by simpa only [d16880, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15556 p hg
    simpa only [d16880, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16880, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16880, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15558 (p : Pattern) (guard : d16881 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16881, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16881, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16880 p = 1 := by simpa only [d16881, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15557 p hg
    simpa only [d16881, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15559 (p : Pattern) (guard : d16882 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16876 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15553 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16881 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15558 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15560 (p : Pattern) (guard : d16883 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16882 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15559 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15561 (p : Pattern) (guard : d16884 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16883 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15560 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15562 (p : Pattern) (guard : d16885 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16884 p = 1 := by simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15561 p hg
    simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15563 (p : Pattern) (guard : d16886 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16881 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15558 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15459 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15564 (p : Pattern) (guard : d16887 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16886 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15563 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15565 (p : Pattern) (guard : d16888 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16887 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15564 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15566 (p : Pattern) (guard : d16889 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16888 p = 1 := by simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15565 p hg
    simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15567 (p : Pattern) (guard : d16890 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16885 p = 1 := by simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15562 p hg
    simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16889 p = 1 := by simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15566 p hg
    simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15568 (p : Pattern) (guard : d128353 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16890 p = 1 := by simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15567 p hg
    simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15569 (p : Pattern) (guard : d13287 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15446 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15570 (p : Pattern) (guard : d16929 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15429 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13287 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15569 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15571 (p : Pattern) (guard : d16930 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16930, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16930, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16929 p = 1 := by simpa only [d16930, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15570 p hg
    simpa only [d16930, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15572 (p : Pattern) (guard : d16931 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16931, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16931, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16930 p = 1 := by simpa only [d16931, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15571 p hg
    simpa only [d16931, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15573 (p : Pattern) (guard : d16932 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16931 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15572 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15574 (p : Pattern) (guard : d16933 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15443 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16932 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15573 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15575 (p : Pattern) (guard : d16934 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16933 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15574 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15576 (p : Pattern) (guard : d16935 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16934 p = 1 := by simpa only [d16935, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15575 p hg
    simpa only [d16935, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16935, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16935, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15577 (p : Pattern) (guard : d16936 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16936, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16936, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16935 p = 1 := by simpa only [d16936, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15576 p hg
    simpa only [d16936, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15578 (p : Pattern) (guard : d16937 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16936 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15577 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15579 (p : Pattern) (guard : d16938 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16937 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15578 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15580 (p : Pattern) (guard : d16939 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16938 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15579 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15581 (p : Pattern) (guard : d16940 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16939 p = 1 := by simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15580 p hg
    simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15582 (p : Pattern) (guard : d16941 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16940 p = 1 := by simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15581 p hg
    simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15583 (p : Pattern) (guard : d16942 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16941 p = 1 := by simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15582 p hg
    simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15584 (p : Pattern) (guard : d128354 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128353 p = 1 := by simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15568 p hg
    simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16942 p = 1 := by simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15583 p hg
    simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15585 (p : Pattern) (guard : d128355 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16858 p = 1 := by simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15529 p hg
    simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128354 p = 1 := by simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15584 p hg
    simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15586 (p : Pattern) (guard : d128356 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16849 p = 1 := by simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15520 p hg
    simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128355 p = 1 := by simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15585 p hg
    simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15587 (p : Pattern) (guard : d128357 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128357, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128357, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128356 p = 1 := by simpa only [d128357, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15586 p hg
    simpa only [d128357, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15588 (p : Pattern) (guard : d16842 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16816 p = 1 := by simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15490 p hg
    simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15589 (p : Pattern) (guard : d16843 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16842 p = 1 := by simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15588 p hg
    simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15590 (p : Pattern) (guard : d16844 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16820 p = 1 := by simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15494 p hg
    simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15591 (p : Pattern) (guard : d16845 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16844 p = 1 := by simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15590 p hg
    simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15592 (p : Pattern) (guard : d16846 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16843 p = 1 := by simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15589 p hg
    simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16845 p = 1 := by simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15591 p hg
    simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15593 (p : Pattern) (guard : d16847 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16846 p = 1 := by simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15592 p hg
    simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15594 (p : Pattern) (guard : d16848 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16847 p = 1 := by simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15593 p hg
    simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15595 (p : Pattern) (guard : d16849 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16848 p = 1 := by simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15594 p hg
    simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15596 (p : Pattern) (guard : d16850 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16815 p = 1 := by simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15489 p hg
    simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15597 (p : Pattern) (guard : d16851 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16850 p = 1 := by simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15596 p hg
    simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15598 (p : Pattern) (guard : d16852 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16851 p = 1 := by simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15597 p hg
    simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15599 (p : Pattern) (guard : d16853 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16819 p = 1 := by simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15493 p hg
    simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15600 (p : Pattern) (guard : d16854 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16853 p = 1 := by simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15599 p hg
    simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15601 (p : Pattern) (guard : d16855 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16854 p = 1 := by simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15600 p hg
    simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15602 (p : Pattern) (guard : d16856 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16852 p = 1 := by simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15598 p hg
    simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16855 p = 1 := by simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15601 p hg
    simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15603 (p : Pattern) (guard : d16857 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16856 p = 1 := by simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15602 p hg
    simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15604 (p : Pattern) (guard : d16858 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16857 p = 1 := by simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15603 p hg
    simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15605 (p : Pattern) (guard : d16866 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16866, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16866, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16865 p = 1 := by simpa only [d16866, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15540 p hg
    simpa only [d16866, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15606 (p : Pattern) (guard : d16871 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16871, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16871, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16870 p = 1 := by simpa only [d16871, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15547 p hg
    simpa only [d16871, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15607 (p : Pattern) (guard : d16872 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16866 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15605 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16871 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15606 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15608 (p : Pattern) (guard : d16873 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16872 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15607 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16802 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15609 (p : Pattern) (guard : d16874 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16873 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15608 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15610 (p : Pattern) (guard : d16875 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16874 p = 1 := by simpa only [d16875, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15609 p hg
    simpa only [d16875, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16875, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16875, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15611 (p : Pattern) (guard : d16876 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16876, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16876, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16875 p = 1 := by simpa only [d16876, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15610 p hg
    simpa only [d16876, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15612 (p : Pattern) (guard : d16877 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16801 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15477 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15613 (p : Pattern) (guard : d16878 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16877 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15612 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15614 (p : Pattern) (guard : d16879 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16878 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15613 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15615 (p : Pattern) (guard : d16880 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16879 p = 1 := by simpa only [d16880, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15614 p hg
    simpa only [d16880, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16880, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16880, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15616 (p : Pattern) (guard : d16881 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16881, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16881, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16880 p = 1 := by simpa only [d16881, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15615 p hg
    simpa only [d16881, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15617 (p : Pattern) (guard : d16882 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16876 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15611 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16881 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15616 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15618 (p : Pattern) (guard : d16883 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16882 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15617 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15619 (p : Pattern) (guard : d16884 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16883 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15618 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15620 (p : Pattern) (guard : d16885 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16884 p = 1 := by simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15619 p hg
    simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15621 (p : Pattern) (guard : d16886 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16881 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15616 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15488 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15622 (p : Pattern) (guard : d16887 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16886 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15621 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15623 (p : Pattern) (guard : d16888 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16887 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15622 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15624 (p : Pattern) (guard : d16889 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16888 p = 1 := by simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15623 p hg
    simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15625 (p : Pattern) (guard : d16890 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16885 p = 1 := by simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15620 p hg
    simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16889 p = 1 := by simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15624 p hg
    simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15626 (p : Pattern) (guard : d128353 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16890 p = 1 := by simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15625 p hg
    simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15627 (p : Pattern) (guard : d16931 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16931, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16931, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16930 p = 1 := by simpa only [d16931, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15571 p hg
    simpa only [d16931, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15628 (p : Pattern) (guard : d16932 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16931 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15627 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15629 (p : Pattern) (guard : d16933 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16932 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15628 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15630 (p : Pattern) (guard : d16934 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16933 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15629 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15631 (p : Pattern) (guard : d16935 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16934 p = 1 := by simpa only [d16935, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15630 p hg
    simpa only [d16935, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16935, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16935, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15632 (p : Pattern) (guard : d16936 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16936, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16936, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16935 p = 1 := by simpa only [d16936, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15631 p hg
    simpa only [d16936, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15633 (p : Pattern) (guard : d16937 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16936 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15632 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15634 (p : Pattern) (guard : d16938 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16937 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15633 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15635 (p : Pattern) (guard : d16939 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16938 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15634 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15636 (p : Pattern) (guard : d16940 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16939 p = 1 := by simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15635 p hg
    simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15637 (p : Pattern) (guard : d16941 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16940 p = 1 := by simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15636 p hg
    simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15638 (p : Pattern) (guard : d16942 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16941 p = 1 := by simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15637 p hg
    simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15639 (p : Pattern) (guard : d128354 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128353 p = 1 := by simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15626 p hg
    simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16942 p = 1 := by simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15638 p hg
    simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15640 (p : Pattern) (guard : d128355 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16858 p = 1 := by simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15604 p hg
    simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128354 p = 1 := by simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15639 p hg
    simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15641 (p : Pattern) (guard : d128356 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16849 p = 1 := by simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15595 p hg
    simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128355 p = 1 := by simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15640 p hg
    simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15642 (p : Pattern) (guard : d16947 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16842 p = 1 := by simpa only [d16947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15513 p hg
    simpa only [d16947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15643 (p : Pattern) (guard : d16948 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16844 p = 1 := by simpa only [d16948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15515 p hg
    simpa only [d16948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15644 (p : Pattern) (guard : d16949 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16947 p = 1 := by simpa only [d16949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15642 p hg
    simpa only [d16949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16948 p = 1 := by simpa only [d16949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15643 p hg
    simpa only [d16949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15645 (p : Pattern) (guard : d16950 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16949 p = 1 := by simpa only [d16950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15644 p hg
    simpa only [d16950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15646 (p : Pattern) (guard : d16951 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16950 p = 1 := by simpa only [d16951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15645 p hg
    simpa only [d16951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15647 (p : Pattern) (guard : d16952 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16951 p = 1 := by simpa only [d16952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15646 p hg
    simpa only [d16952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15648 (p : Pattern) (guard : d16953 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16851 p = 1 := by simpa only [d16953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15522 p hg
    simpa only [d16953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15649 (p : Pattern) (guard : d16954 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16854 p = 1 := by simpa only [d16954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15525 p hg
    simpa only [d16954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15650 (p : Pattern) (guard : d16955 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16953 p = 1 := by simpa only [d16955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15648 p hg
    simpa only [d16955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16954 p = 1 := by simpa only [d16955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15649 p hg
    simpa only [d16955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15651 (p : Pattern) (guard : d16956 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16955 p = 1 := by simpa only [d16956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15650 p hg
    simpa only [d16956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15652 (p : Pattern) (guard : d16957 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16956 p = 1 := by simpa only [d16957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15651 p hg
    simpa only [d16957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15653 (p : Pattern) (guard : d16958 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16884 p = 1 := by simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15561 p hg
    simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15654 (p : Pattern) (guard : d16959 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16888 p = 1 := by simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15565 p hg
    simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15655 (p : Pattern) (guard : d16960 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16958 p = 1 := by simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15653 p hg
    simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16959 p = 1 := by simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15654 p hg
    simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15656 (p : Pattern) (guard : d128358 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16960 p = 1 := by simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15655 p hg
    simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15657 (p : Pattern) (guard : d16965 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16939 p = 1 := by simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15580 p hg
    simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15658 (p : Pattern) (guard : d16966 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16965 p = 1 := by simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15657 p hg
    simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15659 (p : Pattern) (guard : d16967 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16966 p = 1 := by simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15658 p hg
    simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15660 (p : Pattern) (guard : d128359 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128358 p = 1 := by simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15656 p hg
    simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16967 p = 1 := by simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15659 p hg
    simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15661 (p : Pattern) (guard : d128360 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16957 p = 1 := by simpa only [d128360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15652 p hg
    simpa only [d128360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128359 p = 1 := by simpa only [d128360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15660 p hg
    simpa only [d128360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15662 (p : Pattern) (guard : d128361 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16952 p = 1 := by simpa only [d128361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15647 p hg
    simpa only [d128361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128360 p = 1 := by simpa only [d128361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15661 p hg
    simpa only [d128361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15663 (p : Pattern) (guard : d128362 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128356 p = 1 := by simpa only [d128362, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15641 p hg
    simpa only [d128362, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128361 p = 1 := by simpa only [d128362, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15662 p hg
    simpa only [d128362, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15664 (p : Pattern) (guard : d128363 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128357 p = 1 := by simpa only [d128363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15587 p hg
    simpa only [d128363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128362 p = 1 := by simpa only [d128363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15663 p hg
    simpa only [d128363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15665 (p : Pattern) (guard : d16973 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16889 p = 1 := by simpa only [d16973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15624 p hg
    simpa only [d16973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15496 p hg
    simpa only [d16973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15666 (p : Pattern) (guard : d16974 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16973 p = 1 := by simpa only [d16974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15665 p hg
    simpa only [d16974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15667 (p : Pattern) (guard : d16975 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16974 p = 1 := by simpa only [d16975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15666 p hg
    simpa only [d16975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15668 (p : Pattern) (guard : d16976 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16975 p = 1 := by simpa only [d16976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15667 p hg
    simpa only [d16976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15669 (p : Pattern) (guard : d16977 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16976 p = 1 := by simpa only [d16977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15668 p hg
    simpa only [d16977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15670 (p : Pattern) (guard : d16978 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16822 p = 1 := by simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15671 (p : Pattern) (guard : d16979 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16978 p = 1 := by simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15670 p hg
    simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15672 (p : Pattern) (guard : d16980 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16979 p = 1 := by simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15671 p hg
    simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15673 (p : Pattern) (guard : d16981 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16980 p = 1 := by simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15672 p hg
    simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15674 (p : Pattern) (guard : d16982 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16981 p = 1 := by simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15673 p hg
    simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15675 (p : Pattern) (guard : d16983 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16977 p = 1 := by simpa only [d16983, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d16983, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16982 p = 1 := by simpa only [d16983, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15674 p hg
    simpa only [d16983, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15676 (p : Pattern) (guard : d16978 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16822 p = 1 := by simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15496 p hg
    simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15677 (p : Pattern) (guard : d16979 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16978 p = 1 := by simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15676 p hg
    simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15678 (p : Pattern) (guard : d16980 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16979 p = 1 := by simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15677 p hg
    simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15679 (p : Pattern) (guard : d16981 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16980 p = 1 := by simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15678 p hg
    simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15680 (p : Pattern) (guard : d16982 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16981 p = 1 := by simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15679 p hg
    simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15681 (p : Pattern) (guard : d16984 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16832 p = 1 := by simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15503 p hg
    simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15682 (p : Pattern) (guard : d16985 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16984 p = 1 := by simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15681 p hg
    simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15683 (p : Pattern) (guard : d16986 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16985 p = 1 := by simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15682 p hg
    simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15684 (p : Pattern) (guard : d16987 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16986 p = 1 := by simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15685 (p : Pattern) (guard : d16988 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16987 p = 1 := by simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15684 p hg
    simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15686 (p : Pattern) (guard : d16989 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16982 p = 1 := by simpa only [d16989, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15680 p hg
    simpa only [d16989, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16988 p = 1 := by simpa only [d16989, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15685 p hg
    simpa only [d16989, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15687 (p : Pattern) (guard : d16990 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16983 p = 1 := by simpa only [d16990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15675 p hg
    simpa only [d16990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16989 p = 1 := by simpa only [d16990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15686 p hg
    simpa only [d16990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15688 (p : Pattern) (guard : d128364 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128363 p = 1 := by simpa only [d128364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15664 p hg
    simpa only [d128364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16990 p = 1 := by simpa only [d128364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15687 p hg
    simpa only [d128364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15689 (p : Pattern) (guard : d128365 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128364 p = 1 := by simpa only [d128365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15688 p hg
    simpa only [d128365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d128365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15690 (p : Pattern) (guard : d128366 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d16841 p = 1 := by simpa only [d128366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15512 p hg
    simpa only [d128366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128365 p = 1 := by simpa only [d128366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15689 p hg
    simpa only [d128366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15691 (p : Pattern) (guard : d1667 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15692 (p : Pattern) (guard : d1668 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1667 p = 1 := by simpa only [d1668, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15691 p hg
    simpa only [d1668, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1668, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d1668, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15693 (p : Pattern) (guard : d16859 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15694 (p : Pattern) (guard : d16860 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16859 p = 1 := by simpa only [d16860, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15693 p hg
    simpa only [d16860, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16860, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d16860, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15695 (p : Pattern) (guard : d16861 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1668 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15692 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16860 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15696 (p : Pattern) (guard : d15229 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15697 (p : Pattern) (guard : d15230 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15229 p = 1 := by simpa only [d15230, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15696 p hg
    simpa only [d15230, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15230, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d15230, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15698 (p : Pattern) (guard : d15151 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15699 (p : Pattern) (guard : d15152 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15698 p hg
    simpa only [d15152, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d15152, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15700 (p : Pattern) (guard : d16862 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15230 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15697 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15152 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15699 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15701 (p : Pattern) (guard : d16863 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16861 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15695 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16862 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15700 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15702 (p : Pattern) (guard : d1557 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15703 (p : Pattern) (guard : d1558 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1558, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d1558, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15704 (p : Pattern) (guard : d16787 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15705 (p : Pattern) (guard : d16788 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15704 p hg
    simpa only [d16788, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d16788, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15706 (p : Pattern) (guard : d16789 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15703 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15705 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15707 (p : Pattern) (guard : d15156 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15708 (p : Pattern) (guard : d15157 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15707 p hg
    simpa only [d15157, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d15157, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15709 (p : Pattern) (guard : d16790 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15699 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15708 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15710 (p : Pattern) (guard : d16791 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15706 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15709 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15711 (p : Pattern) (guard : d16864 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16863 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15701 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16791 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15710 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15712 (p : Pattern) (guard : d16865 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16865, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16865, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16864 p = 1 := by simpa only [d16865, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d16865, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15713 (p : Pattern) (guard : d16866 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16866, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16866, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16865 p = 1 := by simpa only [d16866, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15712 p hg
    simpa only [d16866, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15714 (p : Pattern) (guard : d13348 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15715 (p : Pattern) (guard : d13349 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13348 p = 1 := by simpa only [d13349, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15714 p hg
    simpa only [d13349, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13349, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d13349, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15716 (p : Pattern) (guard : d16867 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13349 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15715 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15708 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15717 (p : Pattern) (guard : d15158 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15708 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15718 (p : Pattern) (guard : d16868 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16867 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15716 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15717 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15719 (p : Pattern) (guard : d16869 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15710 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16868 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15718 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15720 (p : Pattern) (guard : d16870 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16870, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16870, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16869 p = 1 := by simpa only [d16870, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15719 p hg
    simpa only [d16870, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15721 (p : Pattern) (guard : d16871 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16871, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16871, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16870 p = 1 := by simpa only [d16871, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15720 p hg
    simpa only [d16871, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15722 (p : Pattern) (guard : d16872 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16866 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15713 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16871 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15721 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15723 (p : Pattern) (guard : d1572 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15724 (p : Pattern) (guard : d1573 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15723 p hg
    simpa only [d1573, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d1573, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15725 (p : Pattern) (guard : d16792 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15726 (p : Pattern) (guard : d16793 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15725 p hg
    simpa only [d16793, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d16793, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15727 (p : Pattern) (guard : d16794 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15724 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15726 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15728 (p : Pattern) (guard : d16795 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15727 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15717 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15729 (p : Pattern) (guard : d16796 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15710 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15728 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15730 (p : Pattern) (guard : d16797 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16797, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15729 p hg
    simpa only [d16797, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15731 (p : Pattern) (guard : d16798 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16798, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15730 p hg
    simpa only [d16798, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15732 (p : Pattern) (guard : d5136 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15733 (p : Pattern) (guard : d5137 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15732 p hg
    simpa only [d5137, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d5137, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15734 (p : Pattern) (guard : d5138 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15733 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15735 (p : Pattern) (guard : d15163 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15736 (p : Pattern) (guard : d15164 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15735 p hg
    simpa only [d15164, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d15164, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15737 (p : Pattern) (guard : d15165 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15736 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15738 (p : Pattern) (guard : d15166 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15734 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15737 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15739 (p : Pattern) (guard : d16799 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15728 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15738 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15740 (p : Pattern) (guard : d16800 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16800, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15739 p hg
    simpa only [d16800, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15741 (p : Pattern) (guard : d16801 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16801, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15740 p hg
    simpa only [d16801, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15742 (p : Pattern) (guard : d16802 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15731 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15741 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15743 (p : Pattern) (guard : d16873 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16872 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15722 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16802 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15742 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15744 (p : Pattern) (guard : d16874 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16873 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15743 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15745 (p : Pattern) (guard : d16875 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16874 p = 1 := by simpa only [d16875, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15744 p hg
    simpa only [d16875, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16875, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16875, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15746 (p : Pattern) (guard : d16876 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16876, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16876, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16875 p = 1 := by simpa only [d16876, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15745 p hg
    simpa only [d16876, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15747 (p : Pattern) (guard : d16877 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16801 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15741 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15748 (p : Pattern) (guard : d16878 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15742 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16877 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15747 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15749 (p : Pattern) (guard : d16879 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16878 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15748 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
