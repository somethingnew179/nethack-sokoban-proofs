import NetHack.Soko22Hazard87.Compare077
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19500 (p : Pattern) (guard : d16819 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19495 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19501 (p : Pattern) (guard : d16820 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19500 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19502 (p : Pattern) (guard : d16821 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19501 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19503 (p : Pattern) (guard : d16822 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16821 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19502 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19504 (p : Pattern) (guard : d16823 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16818 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19499 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19503 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19505 (p : Pattern) (guard : d16824 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16823 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19504 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19506 (p : Pattern) (guard : d16825 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16824 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19505 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19507 (p : Pattern) (guard : d16826 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16825 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19506 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19508 (p : Pattern) (guard : d16827 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16826 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19507 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19509 (p : Pattern) (guard : d16831 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16817 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19469 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19510 (p : Pattern) (guard : d16832 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16821 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19473 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19511 (p : Pattern) (guard : d16833 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16831 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19509 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16832 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19510 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19512 (p : Pattern) (guard : d16834 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16833 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19511 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19513 (p : Pattern) (guard : d16835 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16834 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19512 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19514 (p : Pattern) (guard : d16836 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16835 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19513 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19515 (p : Pattern) (guard : d16837 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16836 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19514 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19516 (p : Pattern) (guard : d16838 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16827 p = 1 := by simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19508 p hg
    simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16837 p = 1 := by simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19515 p hg
    simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19517 (p : Pattern) (guard : d16839 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16828 p = 1 := by simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19480 p hg
    simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16838 p = 1 := by simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19516 p hg
    simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19518 (p : Pattern) (guard : d16840 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16839 p = 1 := by simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19517 p hg
    simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19519 (p : Pattern) (guard : d16841 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16830 p = 1 := by simpa only [d16841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19482 p hg
    simpa only [d16841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16840 p = 1 := by simpa only [d16841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19518 p hg
    simpa only [d16841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19520 (p : Pattern) (guard : d16842 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16816 p = 1 := by simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19468 p hg
    simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19521 (p : Pattern) (guard : d16843 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16842 p = 1 := by simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19520 p hg
    simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19522 (p : Pattern) (guard : d16844 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16820 p = 1 := by simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19472 p hg
    simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19523 (p : Pattern) (guard : d16845 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16844 p = 1 := by simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19522 p hg
    simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19524 (p : Pattern) (guard : d16846 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16843 p = 1 := by simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19521 p hg
    simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16845 p = 1 := by simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19523 p hg
    simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19525 (p : Pattern) (guard : d16847 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16846 p = 1 := by simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19524 p hg
    simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19526 (p : Pattern) (guard : d16848 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16847 p = 1 := by simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19525 p hg
    simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19527 (p : Pattern) (guard : d16849 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16848 p = 1 := by simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19526 p hg
    simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19528 (p : Pattern) (guard : d16850 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16815 p = 1 := by simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19467 p hg
    simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19529 (p : Pattern) (guard : d16851 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16850 p = 1 := by simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19528 p hg
    simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19530 (p : Pattern) (guard : d16852 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16851 p = 1 := by simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19529 p hg
    simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19531 (p : Pattern) (guard : d16853 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16819 p = 1 := by simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19471 p hg
    simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19532 (p : Pattern) (guard : d16854 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16853 p = 1 := by simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19531 p hg
    simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19533 (p : Pattern) (guard : d16855 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16854 p = 1 := by simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19532 p hg
    simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19534 (p : Pattern) (guard : d16856 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16852 p = 1 := by simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19530 p hg
    simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16855 p = 1 := by simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19533 p hg
    simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19535 (p : Pattern) (guard : d16857 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16856 p = 1 := by simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19534 p hg
    simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19536 (p : Pattern) (guard : d16858 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16857 p = 1 := by simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19535 p hg
    simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19537 (p : Pattern) (guard : d1664 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19538 (p : Pattern) (guard : d1665 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1664 p = 1 := by simpa only [d1665, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19537 p hg
    simpa only [d1665, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1665, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d1665, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19539 (p : Pattern) (guard : d1666 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1665 p = 1 := by simpa only [d1666, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19538 p hg
    simpa only [d1666, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1666, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d1666, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19540 (p : Pattern) (guard : d1667 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1667, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d1667, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1666 p = 1 := by simpa only [d1667, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19539 p hg
    simpa only [d1667, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19541 (p : Pattern) (guard : d1668 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1667 p = 1 := by simpa only [d1668, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19540 p hg
    simpa only [d1668, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1668, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d1668, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19542 (p : Pattern) (guard : d10035 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19543 (p : Pattern) (guard : d10036 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10035 p = 1 := by simpa only [d10036, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19542 p hg
    simpa only [d10036, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10036, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10036, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19544 (p : Pattern) (guard : d10038 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10036 p = 1 := by simpa only [d10038, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19543 p hg
    simpa only [d10038, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10038, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10038, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19545 (p : Pattern) (guard : d16859 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16859, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d16859, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10038 p = 1 := by simpa only [d16859, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19544 p hg
    simpa only [d16859, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19546 (p : Pattern) (guard : d16860 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16859 p = 1 := by simpa only [d16860, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19545 p hg
    simpa only [d16860, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16860, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d16860, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19547 (p : Pattern) (guard : d16861 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1668 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19541 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16860 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19546 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19548 (p : Pattern) (guard : d10045 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19549 (p : Pattern) (guard : d10046 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10045 p = 1 := by simpa only [d10046, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19548 p hg
    simpa only [d10046, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10046, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10046, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19550 (p : Pattern) (guard : d10048 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10046 p = 1 := by simpa only [d10048, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19549 p hg
    simpa only [d10048, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10048, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10048, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19551 (p : Pattern) (guard : d15229 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15229, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d15229, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10048 p = 1 := by simpa only [d15229, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19550 p hg
    simpa only [d15229, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19552 (p : Pattern) (guard : d15230 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15229 p = 1 := by simpa only [d15230, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19551 p hg
    simpa only [d15230, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15230, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d15230, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19553 (p : Pattern) (guard : d16862 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15230 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19552 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15152 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19407 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19554 (p : Pattern) (guard : d16863 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16861 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19547 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16862 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19553 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19555 (p : Pattern) (guard : d16864 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16863 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19554 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16791 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19414 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19556 (p : Pattern) (guard : d16865 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16865, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16865, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16864 p = 1 := by simpa only [d16865, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19555 p hg
    simpa only [d16865, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19557 (p : Pattern) (guard : d16866 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16866, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16866, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16865 p = 1 := by simpa only [d16866, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19556 p hg
    simpa only [d16866, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19558 (p : Pattern) (guard : d10098 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19559 (p : Pattern) (guard : d10099 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10098 p = 1 := by simpa only [d10099, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19558 p hg
    simpa only [d10099, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10099, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10099, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19560 (p : Pattern) (guard : d10101 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10099 p = 1 := by simpa only [d10101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19559 p hg
    simpa only [d10101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19561 (p : Pattern) (guard : d13348 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13348, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d13348, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10101 p = 1 := by simpa only [d13348, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19560 p hg
    simpa only [d13348, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19562 (p : Pattern) (guard : d13349 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13348 p = 1 := by simpa only [d13349, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19561 p hg
    simpa only [d13349, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13349, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d13349, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19563 (p : Pattern) (guard : d16867 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13349 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19562 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19412 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19564 (p : Pattern) (guard : d16868 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16867 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19563 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19426 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19565 (p : Pattern) (guard : d16869 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19414 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16868 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19564 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19566 (p : Pattern) (guard : d16870 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16870, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16870, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16869 p = 1 := by simpa only [d16870, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19565 p hg
    simpa only [d16870, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19567 (p : Pattern) (guard : d16871 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16871, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16871, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16870 p = 1 := by simpa only [d16871, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19566 p hg
    simpa only [d16871, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19568 (p : Pattern) (guard : d16872 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16866 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19557 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16871 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19567 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19569 (p : Pattern) (guard : d16873 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16872 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19568 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16802 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19447 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19570 (p : Pattern) (guard : d16874 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16873 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19569 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19571 (p : Pattern) (guard : d16875 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16874 p = 1 := by simpa only [d16875, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19570 p hg
    simpa only [d16875, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16875, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16875, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19572 (p : Pattern) (guard : d16876 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16876, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16876, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16875 p = 1 := by simpa only [d16876, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19571 p hg
    simpa only [d16876, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19573 (p : Pattern) (guard : d16877 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16801 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19446 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19574 (p : Pattern) (guard : d16878 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19447 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16877 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19573 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19575 (p : Pattern) (guard : d16879 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16878 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19574 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19576 (p : Pattern) (guard : d16880 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16879 p = 1 := by simpa only [d16880, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19575 p hg
    simpa only [d16880, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16880, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16880, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19577 (p : Pattern) (guard : d16881 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16881, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16881, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16880 p = 1 := by simpa only [d16881, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19576 p hg
    simpa only [d16881, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19578 (p : Pattern) (guard : d16882 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16876 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19572 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16881 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19577 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19579 (p : Pattern) (guard : d16883 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16882 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19578 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19580 (p : Pattern) (guard : d16884 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16883 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19579 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19581 (p : Pattern) (guard : d16885 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16884 p = 1 := by simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19580 p hg
    simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19582 (p : Pattern) (guard : d16886 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16881 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19577 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19466 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19583 (p : Pattern) (guard : d16887 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16886 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19582 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19584 (p : Pattern) (guard : d16888 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16887 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19583 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19585 (p : Pattern) (guard : d16889 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16888 p = 1 := by simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19584 p hg
    simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19586 (p : Pattern) (guard : d16890 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16885 p = 1 := by simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19581 p hg
    simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16889 p = 1 := by simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19585 p hg
    simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19587 (p : Pattern) (guard : d128353 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16890 p = 1 := by simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19586 p hg
    simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19588 (p : Pattern) (guard : d13287 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19453 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19589 (p : Pattern) (guard : d16929 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19427 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13287 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19588 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19590 (p : Pattern) (guard : d16930 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16930, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16930, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16929 p = 1 := by simpa only [d16930, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19589 p hg
    simpa only [d16930, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19591 (p : Pattern) (guard : d16931 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16931, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16931, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16930 p = 1 := by simpa only [d16931, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19590 p hg
    simpa only [d16931, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19592 (p : Pattern) (guard : d16932 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16931 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19591 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19593 (p : Pattern) (guard : d16933 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19447 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16932 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19592 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19594 (p : Pattern) (guard : d16934 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16933 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19593 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19595 (p : Pattern) (guard : d16935 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16934 p = 1 := by simpa only [d16935, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19594 p hg
    simpa only [d16935, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16935, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16935, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19596 (p : Pattern) (guard : d16936 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16936, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16936, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16935 p = 1 := by simpa only [d16936, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19595 p hg
    simpa only [d16936, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19597 (p : Pattern) (guard : d16937 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16936 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19596 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19598 (p : Pattern) (guard : d16938 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16937 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19597 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19599 (p : Pattern) (guard : d16939 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16938 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19598 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19600 (p : Pattern) (guard : d16940 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16939 p = 1 := by simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19599 p hg
    simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19601 (p : Pattern) (guard : d16941 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16940 p = 1 := by simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19600 p hg
    simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19602 (p : Pattern) (guard : d16942 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16941 p = 1 := by simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19601 p hg
    simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19603 (p : Pattern) (guard : d128354 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128353 p = 1 := by simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19587 p hg
    simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16942 p = 1 := by simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19602 p hg
    simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19604 (p : Pattern) (guard : d128355 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16858 p = 1 := by simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19536 p hg
    simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128354 p = 1 := by simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19603 p hg
    simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19605 (p : Pattern) (guard : d128356 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16849 p = 1 := by simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19527 p hg
    simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128355 p = 1 := by simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19604 p hg
    simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19606 (p : Pattern) (guard : d128357 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128357, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128357, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128356 p = 1 := by simpa only [d128357, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19605 p hg
    simpa only [d128357, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19607 (p : Pattern) (guard : d16842 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16816 p = 1 := by simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19497 p hg
    simpa only [d16842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19608 (p : Pattern) (guard : d16843 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16842 p = 1 := by simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19607 p hg
    simpa only [d16843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19609 (p : Pattern) (guard : d16844 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16820 p = 1 := by simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19501 p hg
    simpa only [d16844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19610 (p : Pattern) (guard : d16845 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16844 p = 1 := by simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19609 p hg
    simpa only [d16845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19611 (p : Pattern) (guard : d16846 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16843 p = 1 := by simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19608 p hg
    simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16845 p = 1 := by simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19610 p hg
    simpa only [d16846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19612 (p : Pattern) (guard : d16847 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16846 p = 1 := by simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19611 p hg
    simpa only [d16847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19613 (p : Pattern) (guard : d16848 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16847 p = 1 := by simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19612 p hg
    simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19614 (p : Pattern) (guard : d16849 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16848 p = 1 := by simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19613 p hg
    simpa only [d16849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19615 (p : Pattern) (guard : d16850 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16815 p = 1 := by simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19496 p hg
    simpa only [d16850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19616 (p : Pattern) (guard : d16851 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16850 p = 1 := by simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19615 p hg
    simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19617 (p : Pattern) (guard : d16852 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16851 p = 1 := by simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19616 p hg
    simpa only [d16852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19618 (p : Pattern) (guard : d16853 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16819 p = 1 := by simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19500 p hg
    simpa only [d16853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19619 (p : Pattern) (guard : d16854 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16853 p = 1 := by simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19618 p hg
    simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19620 (p : Pattern) (guard : d16855 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16854 p = 1 := by simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19619 p hg
    simpa only [d16855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19621 (p : Pattern) (guard : d16856 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16852 p = 1 := by simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19617 p hg
    simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16855 p = 1 := by simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19620 p hg
    simpa only [d16856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19622 (p : Pattern) (guard : d16857 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16856 p = 1 := by simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19621 p hg
    simpa only [d16857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19623 (p : Pattern) (guard : d16858 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16857 p = 1 := by simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19622 p hg
    simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19624 (p : Pattern) (guard : d16866 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16866, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16866, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16865 p = 1 := by simpa only [d16866, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19556 p hg
    simpa only [d16866, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19625 (p : Pattern) (guard : d16871 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16871, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16871, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16870 p = 1 := by simpa only [d16871, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19566 p hg
    simpa only [d16871, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19626 (p : Pattern) (guard : d16872 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16866 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19624 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16871 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19625 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19627 (p : Pattern) (guard : d16873 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16872 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19626 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16802 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19628 (p : Pattern) (guard : d16874 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16873 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19627 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19629 (p : Pattern) (guard : d16875 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16874 p = 1 := by simpa only [d16875, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19628 p hg
    simpa only [d16875, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16875, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16875, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19630 (p : Pattern) (guard : d16876 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16876, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16876, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16875 p = 1 := by simpa only [d16876, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19629 p hg
    simpa only [d16876, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19631 (p : Pattern) (guard : d16877 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16801 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19484 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19632 (p : Pattern) (guard : d16878 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16877 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19631 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19633 (p : Pattern) (guard : d16879 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16878 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19632 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19634 (p : Pattern) (guard : d16880 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16879 p = 1 := by simpa only [d16880, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19633 p hg
    simpa only [d16880, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16880, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16880, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19635 (p : Pattern) (guard : d16881 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16881, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16881, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16880 p = 1 := by simpa only [d16881, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19634 p hg
    simpa only [d16881, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19636 (p : Pattern) (guard : d16882 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16876 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19630 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16881 p = 1 := by simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19635 p hg
    simpa only [d16882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19637 (p : Pattern) (guard : d16883 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16882 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19636 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19638 (p : Pattern) (guard : d16884 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16883 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19637 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19639 (p : Pattern) (guard : d16885 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16884 p = 1 := by simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19638 p hg
    simpa only [d16885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19640 (p : Pattern) (guard : d16886 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16881 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19635 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19495 p hg
    simpa only [d16886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19641 (p : Pattern) (guard : d16887 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16886 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19640 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19642 (p : Pattern) (guard : d16888 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16887 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19641 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19643 (p : Pattern) (guard : d16889 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16888 p = 1 := by simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19642 p hg
    simpa only [d16889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19644 (p : Pattern) (guard : d16890 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16885 p = 1 := by simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19639 p hg
    simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16889 p = 1 := by simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19643 p hg
    simpa only [d16890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19645 (p : Pattern) (guard : d128353 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16890 p = 1 := by simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19644 p hg
    simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19646 (p : Pattern) (guard : d16931 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16931, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16931, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16930 p = 1 := by simpa only [d16931, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19590 p hg
    simpa only [d16931, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19647 (p : Pattern) (guard : d16932 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16931 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19646 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19648 (p : Pattern) (guard : d16933 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16932 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19647 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19649 (p : Pattern) (guard : d16934 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16933 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19648 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19650 (p : Pattern) (guard : d16935 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16934 p = 1 := by simpa only [d16935, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19649 p hg
    simpa only [d16935, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16935, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16935, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19651 (p : Pattern) (guard : d16936 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16936, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16936, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16935 p = 1 := by simpa only [d16936, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19650 p hg
    simpa only [d16936, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19652 (p : Pattern) (guard : d16937 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16936 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19651 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19653 (p : Pattern) (guard : d16938 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16937 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19652 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19654 (p : Pattern) (guard : d16939 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16938 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19653 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19655 (p : Pattern) (guard : d16940 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16939 p = 1 := by simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19654 p hg
    simpa only [d16940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19656 (p : Pattern) (guard : d16941 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16940 p = 1 := by simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19655 p hg
    simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19657 (p : Pattern) (guard : d16942 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16941 p = 1 := by simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19656 p hg
    simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19658 (p : Pattern) (guard : d128354 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128353 p = 1 := by simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19645 p hg
    simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16942 p = 1 := by simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19657 p hg
    simpa only [d128354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19659 (p : Pattern) (guard : d128355 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16858 p = 1 := by simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19623 p hg
    simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128354 p = 1 := by simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19658 p hg
    simpa only [d128355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19660 (p : Pattern) (guard : d128356 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16849 p = 1 := by simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19614 p hg
    simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128355 p = 1 := by simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19659 p hg
    simpa only [d128356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19661 (p : Pattern) (guard : d16947 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16842 p = 1 := by simpa only [d16947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19520 p hg
    simpa only [d16947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19662 (p : Pattern) (guard : d16948 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16844 p = 1 := by simpa only [d16948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19522 p hg
    simpa only [d16948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19663 (p : Pattern) (guard : d16949 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16947 p = 1 := by simpa only [d16949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19661 p hg
    simpa only [d16949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16948 p = 1 := by simpa only [d16949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19662 p hg
    simpa only [d16949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19664 (p : Pattern) (guard : d16950 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16949 p = 1 := by simpa only [d16950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19663 p hg
    simpa only [d16950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19665 (p : Pattern) (guard : d16951 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16950 p = 1 := by simpa only [d16951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19664 p hg
    simpa only [d16951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19666 (p : Pattern) (guard : d16952 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16951 p = 1 := by simpa only [d16952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19665 p hg
    simpa only [d16952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19667 (p : Pattern) (guard : d16953 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16851 p = 1 := by simpa only [d16953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19529 p hg
    simpa only [d16953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19668 (p : Pattern) (guard : d16954 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16854 p = 1 := by simpa only [d16954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19532 p hg
    simpa only [d16954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19669 (p : Pattern) (guard : d16955 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16953 p = 1 := by simpa only [d16955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19667 p hg
    simpa only [d16955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16954 p = 1 := by simpa only [d16955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19668 p hg
    simpa only [d16955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19670 (p : Pattern) (guard : d16956 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16955 p = 1 := by simpa only [d16956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19669 p hg
    simpa only [d16956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19671 (p : Pattern) (guard : d16957 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16956 p = 1 := by simpa only [d16957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19670 p hg
    simpa only [d16957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19672 (p : Pattern) (guard : d16958 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16884 p = 1 := by simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19580 p hg
    simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19673 (p : Pattern) (guard : d16959 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16888 p = 1 := by simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19584 p hg
    simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19674 (p : Pattern) (guard : d16960 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16958 p = 1 := by simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19672 p hg
    simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16959 p = 1 := by simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19673 p hg
    simpa only [d16960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19675 (p : Pattern) (guard : d128358 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16960 p = 1 := by simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19674 p hg
    simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19676 (p : Pattern) (guard : d16965 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16939 p = 1 := by simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19599 p hg
    simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19677 (p : Pattern) (guard : d16966 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16965 p = 1 := by simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19676 p hg
    simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19678 (p : Pattern) (guard : d16967 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16966 p = 1 := by simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19677 p hg
    simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19679 (p : Pattern) (guard : d128359 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128358 p = 1 := by simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19675 p hg
    simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16967 p = 1 := by simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19678 p hg
    simpa only [d128359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19680 (p : Pattern) (guard : d128360 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16957 p = 1 := by simpa only [d128360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19671 p hg
    simpa only [d128360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128359 p = 1 := by simpa only [d128360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19679 p hg
    simpa only [d128360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19681 (p : Pattern) (guard : d128361 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16952 p = 1 := by simpa only [d128361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19666 p hg
    simpa only [d128361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128360 p = 1 := by simpa only [d128361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19680 p hg
    simpa only [d128361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19682 (p : Pattern) (guard : d128362 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128356 p = 1 := by simpa only [d128362, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19660 p hg
    simpa only [d128362, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128361 p = 1 := by simpa only [d128362, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19681 p hg
    simpa only [d128362, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19683 (p : Pattern) (guard : d128363 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128357 p = 1 := by simpa only [d128363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19606 p hg
    simpa only [d128363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128362 p = 1 := by simpa only [d128363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19682 p hg
    simpa only [d128363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19684 (p : Pattern) (guard : d16973 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16889 p = 1 := by simpa only [d16973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19643 p hg
    simpa only [d16973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19503 p hg
    simpa only [d16973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19685 (p : Pattern) (guard : d16974 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16973 p = 1 := by simpa only [d16974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19684 p hg
    simpa only [d16974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19686 (p : Pattern) (guard : d16975 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16974 p = 1 := by simpa only [d16975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19685 p hg
    simpa only [d16975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19687 (p : Pattern) (guard : d16976 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16975 p = 1 := by simpa only [d16976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19686 p hg
    simpa only [d16976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19688 (p : Pattern) (guard : d16977 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16976 p = 1 := by simpa only [d16977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19687 p hg
    simpa only [d16977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19689 (p : Pattern) (guard : d16978 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16822 p = 1 := by simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19474 p hg
    simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19690 (p : Pattern) (guard : d16979 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16978 p = 1 := by simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19689 p hg
    simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19691 (p : Pattern) (guard : d16980 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16979 p = 1 := by simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19690 p hg
    simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19692 (p : Pattern) (guard : d16981 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16980 p = 1 := by simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19691 p hg
    simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19693 (p : Pattern) (guard : d16982 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16981 p = 1 := by simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19692 p hg
    simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19694 (p : Pattern) (guard : d16983 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16977 p = 1 := by simpa only [d16983, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19688 p hg
    simpa only [d16983, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16982 p = 1 := by simpa only [d16983, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19693 p hg
    simpa only [d16983, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19695 (p : Pattern) (guard : d16978 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16822 p = 1 := by simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19503 p hg
    simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19696 (p : Pattern) (guard : d16979 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16978 p = 1 := by simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19695 p hg
    simpa only [d16979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19697 (p : Pattern) (guard : d16980 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16979 p = 1 := by simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19696 p hg
    simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19698 (p : Pattern) (guard : d16981 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16980 p = 1 := by simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19697 p hg
    simpa only [d16981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19699 (p : Pattern) (guard : d16982 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16981 p = 1 := by simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19698 p hg
    simpa only [d16982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19700 (p : Pattern) (guard : d16984 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16832 p = 1 := by simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19510 p hg
    simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19701 (p : Pattern) (guard : d16985 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16984 p = 1 := by simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19700 p hg
    simpa only [d16985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19702 (p : Pattern) (guard : d16986 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16985 p = 1 := by simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19701 p hg
    simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19703 (p : Pattern) (guard : d16987 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16986 p = 1 := by simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19702 p hg
    simpa only [d16987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19704 (p : Pattern) (guard : d16988 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16987 p = 1 := by simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19703 p hg
    simpa only [d16988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19705 (p : Pattern) (guard : d16989 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16982 p = 1 := by simpa only [d16989, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19699 p hg
    simpa only [d16989, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16988 p = 1 := by simpa only [d16989, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19704 p hg
    simpa only [d16989, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19706 (p : Pattern) (guard : d16990 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16983 p = 1 := by simpa only [d16990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19694 p hg
    simpa only [d16990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16989 p = 1 := by simpa only [d16990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19705 p hg
    simpa only [d16990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19707 (p : Pattern) (guard : d128364 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128363 p = 1 := by simpa only [d128364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19683 p hg
    simpa only [d128364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16990 p = 1 := by simpa only [d128364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19706 p hg
    simpa only [d128364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19708 (p : Pattern) (guard : d128365 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128364 p = 1 := by simpa only [d128365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19707 p hg
    simpa only [d128365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d128365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19709 (p : Pattern) (guard : d128366 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d16841 p = 1 := by simpa only [d128366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19519 p hg
    simpa only [d128366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128365 p = 1 := by simpa only [d128366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19708 p hg
    simpa only [d128366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19710 (p : Pattern) (guard : d1664 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19711 (p : Pattern) (guard : d1665 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1664 p = 1 := by simpa only [d1665, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19710 p hg
    simpa only [d1665, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1665, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d1665, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19712 (p : Pattern) (guard : d1666 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1665 p = 1 := by simpa only [d1666, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19711 p hg
    simpa only [d1666, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1666, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d1666, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19713 (p : Pattern) (guard : d1667 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1667, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d1667, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1666 p = 1 := by simpa only [d1667, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19712 p hg
    simpa only [d1667, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19714 (p : Pattern) (guard : d1668 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1667 p = 1 := by simpa only [d1668, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19713 p hg
    simpa only [d1668, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1668, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d1668, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19715 (p : Pattern) (guard : d10035 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19716 (p : Pattern) (guard : d10036 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10035 p = 1 := by simpa only [d10036, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19715 p hg
    simpa only [d10036, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10036, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10036, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19717 (p : Pattern) (guard : d10038 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10036 p = 1 := by simpa only [d10038, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19716 p hg
    simpa only [d10038, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10038, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10038, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19718 (p : Pattern) (guard : d16859 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16859, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d16859, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10038 p = 1 := by simpa only [d16859, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19717 p hg
    simpa only [d16859, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19719 (p : Pattern) (guard : d16860 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16859 p = 1 := by simpa only [d16860, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19718 p hg
    simpa only [d16860, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16860, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d16860, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19720 (p : Pattern) (guard : d16861 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1668 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19714 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16860 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19719 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19721 (p : Pattern) (guard : d10045 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19722 (p : Pattern) (guard : d10046 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10045 p = 1 := by simpa only [d10046, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19721 p hg
    simpa only [d10046, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10046, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10046, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19723 (p : Pattern) (guard : d10048 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10046 p = 1 := by simpa only [d10048, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19722 p hg
    simpa only [d10048, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10048, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10048, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19724 (p : Pattern) (guard : d15229 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15229, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d15229, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10048 p = 1 := by simpa only [d15229, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19723 p hg
    simpa only [d15229, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19725 (p : Pattern) (guard : d15230 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15229 p = 1 := by simpa only [d15230, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19724 p hg
    simpa only [d15230, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15230, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d15230, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19726 (p : Pattern) (guard : d10062 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19727 (p : Pattern) (guard : d10063 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10062 p = 1 := by simpa only [d10063, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19726 p hg
    simpa only [d10063, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10063, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10063, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19728 (p : Pattern) (guard : d10065 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10063 p = 1 := by simpa only [d10065, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19727 p hg
    simpa only [d10065, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10065, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10065, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19729 (p : Pattern) (guard : d15151 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15151, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d15151, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10065 p = 1 := by simpa only [d15151, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19728 p hg
    simpa only [d15151, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19730 (p : Pattern) (guard : d15152 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19729 p hg
    simpa only [d15152, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d15152, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19731 (p : Pattern) (guard : d16862 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15230 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19725 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15152 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19730 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19732 (p : Pattern) (guard : d16863 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16861 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19720 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16862 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19731 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19733 (p : Pattern) (guard : d1554 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19734 (p : Pattern) (guard : d1555 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19733 p hg
    simpa only [d1555, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d1555, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19735 (p : Pattern) (guard : d1556 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19734 p hg
    simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19736 (p : Pattern) (guard : d1557 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19735 p hg
    simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19737 (p : Pattern) (guard : d1558 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19736 p hg
    simpa only [d1558, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d1558, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19738 (p : Pattern) (guard : d10073 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19739 (p : Pattern) (guard : d10074 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10073 p = 1 := by simpa only [d10074, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19738 p hg
    simpa only [d10074, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10074, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10074, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19740 (p : Pattern) (guard : d10076 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10074 p = 1 := by simpa only [d10076, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19739 p hg
    simpa only [d10076, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10076, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10076, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19741 (p : Pattern) (guard : d16787 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16787, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d16787, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10076 p = 1 := by simpa only [d16787, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19740 p hg
    simpa only [d16787, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19742 (p : Pattern) (guard : d16788 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19741 p hg
    simpa only [d16788, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d16788, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19743 (p : Pattern) (guard : d16789 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19737 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19742 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19744 (p : Pattern) (guard : d10084 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19745 (p : Pattern) (guard : d10085 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10084 p = 1 := by simpa only [d10085, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19744 p hg
    simpa only [d10085, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10085, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10085, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19746 (p : Pattern) (guard : d10087 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10085 p = 1 := by simpa only [d10087, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19745 p hg
    simpa only [d10087, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10087, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10087, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19747 (p : Pattern) (guard : d15156 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15156, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d15156, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10087 p = 1 := by simpa only [d15156, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19746 p hg
    simpa only [d15156, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19748 (p : Pattern) (guard : d15157 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19747 p hg
    simpa only [d15157, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d15157, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19749 (p : Pattern) (guard : d16790 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19730 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19748 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
