import NetHack.Soko22Hazard87.Compare049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12500 (p : Pattern) (guard : d160851 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160850 p = 1 := by simpa only [d160851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12499 p hg
    simpa only [d160851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12501 (p : Pattern) (guard : d160852 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160851 p = 1 := by simpa only [d160852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12500 p hg
    simpa only [d160852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12502 (p : Pattern) (guard : d160853 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160852 p = 1 := by simpa only [d160853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12501 p hg
    simpa only [d160853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12503 (p : Pattern) (guard : d160854 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160853 p = 1 := by simpa only [d160854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12502 p hg
    simpa only [d160854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12504 (p : Pattern) (guard : d160855 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160848 p = 1 := by simpa only [d160855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12497 p hg
    simpa only [d160855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160854 p = 1 := by simpa only [d160855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12503 p hg
    simpa only [d160855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12505 (p : Pattern) (guard : d160856 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d160827 p = 1 := by simpa only [d160856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12466 p hg
    simpa only [d160856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160855 p = 1 := by simpa only [d160856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12504 p hg
    simpa only [d160856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12506 (p : Pattern) (guard : d160857 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d160818 p = 1 := by simpa only [d160857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12457 p hg
    simpa only [d160857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160856 p = 1 := by simpa only [d160857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12505 p hg
    simpa only [d160857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12507 (p : Pattern) (guard : d160858 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160857 p = 1 := by simpa only [d160858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12506 p hg
    simpa only [d160858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12508 (p : Pattern) (guard : d160859 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160811 p = 1 := by simpa only [d160859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12450 p hg
    simpa only [d160859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12509 (p : Pattern) (guard : d160860 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160813 p = 1 := by simpa only [d160860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12452 p hg
    simpa only [d160860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12510 (p : Pattern) (guard : d160861 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160859 p = 1 := by simpa only [d160861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12508 p hg
    simpa only [d160861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160860 p = 1 := by simpa only [d160861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12509 p hg
    simpa only [d160861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12511 (p : Pattern) (guard : d160862 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160861 p = 1 := by simpa only [d160862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12510 p hg
    simpa only [d160862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12512 (p : Pattern) (guard : d160863 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160862 p = 1 := by simpa only [d160863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12511 p hg
    simpa only [d160863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12513 (p : Pattern) (guard : d160864 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160863 p = 1 := by simpa only [d160864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12512 p hg
    simpa only [d160864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12514 (p : Pattern) (guard : d160865 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160820 p = 1 := by simpa only [d160865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12459 p hg
    simpa only [d160865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12515 (p : Pattern) (guard : d160866 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160823 p = 1 := by simpa only [d160866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12462 p hg
    simpa only [d160866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12516 (p : Pattern) (guard : d160867 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160865 p = 1 := by simpa only [d160867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12514 p hg
    simpa only [d160867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160866 p = 1 := by simpa only [d160867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12515 p hg
    simpa only [d160867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12517 (p : Pattern) (guard : d160868 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160867 p = 1 := by simpa only [d160868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12516 p hg
    simpa only [d160868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12518 (p : Pattern) (guard : d160869 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160868 p = 1 := by simpa only [d160869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12517 p hg
    simpa only [d160869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12519 (p : Pattern) (guard : d160870 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160845 p = 1 := by simpa only [d160870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12494 p hg
    simpa only [d160870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12520 (p : Pattern) (guard : d160871 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160870 p = 1 := by simpa only [d160871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12519 p hg
    simpa only [d160871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160800 p = 1 := by simpa only [d160871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12439 p hg
    simpa only [d160871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12521 (p : Pattern) (guard : d160872 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160871 p = 1 := by simpa only [d160872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12520 p hg
    simpa only [d160872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12522 (p : Pattern) (guard : d160873 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160851 p = 1 := by simpa only [d160873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12500 p hg
    simpa only [d160873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12523 (p : Pattern) (guard : d160874 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160873 p = 1 := by simpa only [d160874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12522 p hg
    simpa only [d160874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12524 (p : Pattern) (guard : d160875 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160874 p = 1 := by simpa only [d160875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12523 p hg
    simpa only [d160875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12525 (p : Pattern) (guard : d160876 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160872 p = 1 := by simpa only [d160876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12521 p hg
    simpa only [d160876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160875 p = 1 := by simpa only [d160876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12524 p hg
    simpa only [d160876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12526 (p : Pattern) (guard : d160877 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d160869 p = 1 := by simpa only [d160877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12518 p hg
    simpa only [d160877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160876 p = 1 := by simpa only [d160877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12525 p hg
    simpa only [d160877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12527 (p : Pattern) (guard : d160878 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d160864 p = 1 := by simpa only [d160878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12513 p hg
    simpa only [d160878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160877 p = 1 := by simpa only [d160878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12526 p hg
    simpa only [d160878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12528 (p : Pattern) (guard : d160879 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160857 p = 1 := by simpa only [d160879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12506 p hg
    simpa only [d160879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160878 p = 1 := by simpa only [d160879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12527 p hg
    simpa only [d160879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12529 (p : Pattern) (guard : d160880 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160858 p = 1 := by simpa only [d160880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12507 p hg
    simpa only [d160880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160879 p = 1 := by simpa only [d160880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12528 p hg
    simpa only [d160880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12530 (p : Pattern) (guard : d160881 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160791 p = 1 := by simpa only [d160881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12430 p hg
    simpa only [d160881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12531 (p : Pattern) (guard : d160882 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160881 p = 1 := by simpa only [d160882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12530 p hg
    simpa only [d160882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12532 (p : Pattern) (guard : d160883 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160882 p = 1 := by simpa only [d160883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12531 p hg
    simpa only [d160883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12533 (p : Pattern) (guard : d160884 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160883 p = 1 := by simpa only [d160884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12532 p hg
    simpa only [d160884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12534 (p : Pattern) (guard : d160885 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160884 p = 1 := by simpa only [d160885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12533 p hg
    simpa only [d160885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12535 (p : Pattern) (guard : d160886 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160796 p = 1 := by simpa only [d160886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12435 p hg
    simpa only [d160886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160885 p = 1 := by simpa only [d160886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12534 p hg
    simpa only [d160886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12536 (p : Pattern) (guard : d160887 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160801 p = 1 := by simpa only [d160887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12440 p hg
    simpa only [d160887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12537 (p : Pattern) (guard : d160888 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160887 p = 1 := by simpa only [d160888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12536 p hg
    simpa only [d160888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12538 (p : Pattern) (guard : d160889 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160888 p = 1 := by simpa only [d160889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12537 p hg
    simpa only [d160889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12539 (p : Pattern) (guard : d160890 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160889 p = 1 := by simpa only [d160890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12538 p hg
    simpa only [d160890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12540 (p : Pattern) (guard : d160891 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160890 p = 1 := by simpa only [d160891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12539 p hg
    simpa only [d160891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12541 (p : Pattern) (guard : d160892 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160885 p = 1 := by simpa only [d160892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12534 p hg
    simpa only [d160892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160891 p = 1 := by simpa only [d160892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12540 p hg
    simpa only [d160892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12542 (p : Pattern) (guard : d160893 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160886 p = 1 := by simpa only [d160893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12535 p hg
    simpa only [d160893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160892 p = 1 := by simpa only [d160893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12541 p hg
    simpa only [d160893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12543 (p : Pattern) (guard : d160894 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160880 p = 1 := by simpa only [d160894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12529 p hg
    simpa only [d160894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160893 p = 1 := by simpa only [d160894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12542 p hg
    simpa only [d160894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12544 (p : Pattern) (guard : d160895 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160894 p = 1 := by simpa only [d160895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12543 p hg
    simpa only [d160895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12545 (p : Pattern) (guard : d160896 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160810 p = 1 := by simpa only [d160896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12449 p hg
    simpa only [d160896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160895 p = 1 := by simpa only [d160896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12544 p hg
    simpa only [d160896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12546 (p : Pattern) (guard : d2037 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d2037, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7467 p hg
    simpa only [d2037, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12547 (p : Pattern) (guard : d2038 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12546 p hg
    simpa only [d2038, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d2038, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12548 (p : Pattern) (guard : d160828 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2038 p = 1 := by simpa only [d160828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12547 p hg
    simpa only [d160828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12549 (p : Pattern) (guard : d160829 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160828 p = 1 := by simpa only [d160829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12548 p hg
    simpa only [d160829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12550 (p : Pattern) (guard : d2055 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d2055, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7486 p hg
    simpa only [d2055, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12551 (p : Pattern) (guard : d2056 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12550 p hg
    simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12552 (p : Pattern) (guard : d160764 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2056 p = 1 := by simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12551 p hg
    simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12553 (p : Pattern) (guard : d160765 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160764 p = 1 := by simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12552 p hg
    simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12554 (p : Pattern) (guard : d160830 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160829 p = 1 := by simpa only [d160830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12549 p hg
    simpa only [d160830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160765 p = 1 := by simpa only [d160830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12553 p hg
    simpa only [d160830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12555 (p : Pattern) (guard : d160831 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160831, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160831, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160830 p = 1 := by simpa only [d160831, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12554 p hg
    simpa only [d160831, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12556 (p : Pattern) (guard : d160832 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160832, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160832, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160831 p = 1 := by simpa only [d160832, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12555 p hg
    simpa only [d160832, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12557 (p : Pattern) (guard : d5715 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7456 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12558 (p : Pattern) (guard : d5716 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5715 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12557 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12559 (p : Pattern) (guard : d5717 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5716 p = 1 := by simpa only [d5717, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12558 p hg
    simpa only [d5717, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5717, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d5717, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12560 (p : Pattern) (guard : d13677 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5717 p = 1 := by simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12559 p hg
    simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12561 (p : Pattern) (guard : d13678 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13677 p = 1 := by simpa only [d13678, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12560 p hg
    simpa only [d13678, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13678, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d13678, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12562 (p : Pattern) (guard : d13679 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13678 p = 1 := by simpa only [d13679, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12561 p hg
    simpa only [d13679, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13679, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d13679, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12563 (p : Pattern) (guard : d13680 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13680, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d13680, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13679 p = 1 := by simpa only [d13680, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12562 p hg
    simpa only [d13680, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12564 (p : Pattern) (guard : d13681 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13680 p = 1 := by simpa only [d13681, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12563 p hg
    simpa only [d13681, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13681, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d13681, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12565 (p : Pattern) (guard : d160833 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13681 p = 1 := by simpa only [d160833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12564 p hg
    simpa only [d160833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12566 (p : Pattern) (guard : d160834 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160833 p = 1 := by simpa only [d160834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12565 p hg
    simpa only [d160834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12567 (p : Pattern) (guard : d160835 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160765 p = 1 := by simpa only [d160835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12553 p hg
    simpa only [d160835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160834 p = 1 := by simpa only [d160835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12566 p hg
    simpa only [d160835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12568 (p : Pattern) (guard : d160836 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160836, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160836, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160835 p = 1 := by simpa only [d160836, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12567 p hg
    simpa only [d160836, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12569 (p : Pattern) (guard : d160837 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160837, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160837, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160836 p = 1 := by simpa only [d160837, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12568 p hg
    simpa only [d160837, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12570 (p : Pattern) (guard : d160838 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160832 p = 1 := by simpa only [d160838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12556 p hg
    simpa only [d160838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160837 p = 1 := by simpa only [d160838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12569 p hg
    simpa only [d160838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12571 (p : Pattern) (guard : d2067 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d2067, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7499 p hg
    simpa only [d2067, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12572 (p : Pattern) (guard : d2068 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12571 p hg
    simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12573 (p : Pattern) (guard : d160766 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2068 p = 1 := by simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12572 p hg
    simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12574 (p : Pattern) (guard : d160767 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160766 p = 1 := by simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12573 p hg
    simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12575 (p : Pattern) (guard : d160768 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160765 p = 1 := by simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12553 p hg
    simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160767 p = 1 := by simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12574 p hg
    simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12576 (p : Pattern) (guard : d160769 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160769, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160769, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160768 p = 1 := by simpa only [d160769, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12575 p hg
    simpa only [d160769, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12577 (p : Pattern) (guard : d160770 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160770, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160770, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160769 p = 1 := by simpa only [d160770, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12576 p hg
    simpa only [d160770, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12578 (p : Pattern) (guard : d160771 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160767 p = 1 := by simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12574 p hg
    simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12579 (p : Pattern) (guard : d160772 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160772, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160772, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160771 p = 1 := by simpa only [d160772, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12578 p hg
    simpa only [d160772, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12580 (p : Pattern) (guard : d160773 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160773, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160773, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160772 p = 1 := by simpa only [d160773, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12579 p hg
    simpa only [d160773, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12581 (p : Pattern) (guard : d160774 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160770 p = 1 := by simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12577 p hg
    simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160773 p = 1 := by simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12580 p hg
    simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12582 (p : Pattern) (guard : d160839 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160838 p = 1 := by simpa only [d160839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12570 p hg
    simpa only [d160839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160774 p = 1 := by simpa only [d160839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12581 p hg
    simpa only [d160839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12583 (p : Pattern) (guard : d160840 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160839 p = 1 := by simpa only [d160840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12582 p hg
    simpa only [d160840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12584 (p : Pattern) (guard : d160841 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160840 p = 1 := by simpa only [d160841, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12583 p hg
    simpa only [d160841, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160841, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160841, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12585 (p : Pattern) (guard : d160842 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160842, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160842, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160841 p = 1 := by simpa only [d160842, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12584 p hg
    simpa only [d160842, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12586 (p : Pattern) (guard : d160775 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160773 p = 1 := by simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12580 p hg
    simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12587 (p : Pattern) (guard : d160776 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160774 p = 1 := by simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12581 p hg
    simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160775 p = 1 := by simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12586 p hg
    simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12588 (p : Pattern) (guard : d160777 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160776 p = 1 := by simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12587 p hg
    simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12589 (p : Pattern) (guard : d160778 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160777 p = 1 := by simpa only [d160778, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12588 p hg
    simpa only [d160778, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160778, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160778, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12590 (p : Pattern) (guard : d160779 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160779, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160779, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160778 p = 1 := by simpa only [d160779, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12589 p hg
    simpa only [d160779, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12591 (p : Pattern) (guard : d160843 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160842 p = 1 := by simpa only [d160843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12585 p hg
    simpa only [d160843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160779 p = 1 := by simpa only [d160843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12590 p hg
    simpa only [d160843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12592 (p : Pattern) (guard : d160844 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160843 p = 1 := by simpa only [d160844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12591 p hg
    simpa only [d160844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12593 (p : Pattern) (guard : d160845 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160844 p = 1 := by simpa only [d160845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12592 p hg
    simpa only [d160845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12594 (p : Pattern) (guard : d160870 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160845 p = 1 := by simpa only [d160870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12593 p hg
    simpa only [d160870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12595 (p : Pattern) (guard : d160780 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160775 p = 1 := by simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12586 p hg
    simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12596 (p : Pattern) (guard : d160781 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160780 p = 1 := by simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12595 p hg
    simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12597 (p : Pattern) (guard : d160782 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160781 p = 1 := by simpa only [d160782, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12596 p hg
    simpa only [d160782, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160782, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160782, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12598 (p : Pattern) (guard : d160783 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160783, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160783, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160782 p = 1 := by simpa only [d160783, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12597 p hg
    simpa only [d160783, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12599 (p : Pattern) (guard : d160784 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160779 p = 1 := by simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12590 p hg
    simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160783 p = 1 := by simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12598 p hg
    simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12600 (p : Pattern) (guard : d160785 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160784 p = 1 := by simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12599 p hg
    simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12601 (p : Pattern) (guard : d160786 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160785 p = 1 := by simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12600 p hg
    simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12602 (p : Pattern) (guard : d160800 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160786 p = 1 := by simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12601 p hg
    simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12603 (p : Pattern) (guard : d160871 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160870 p = 1 := by simpa only [d160871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12594 p hg
    simpa only [d160871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160800 p = 1 := by simpa only [d160871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12602 p hg
    simpa only [d160871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12604 (p : Pattern) (guard : d160872 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160871 p = 1 := by simpa only [d160872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12603 p hg
    simpa only [d160872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12605 (p : Pattern) (guard : d160849 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160779 p = 1 := by simpa only [d160849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12590 p hg
    simpa only [d160849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12606 (p : Pattern) (guard : d160850 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160849 p = 1 := by simpa only [d160850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12605 p hg
    simpa only [d160850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12607 (p : Pattern) (guard : d160851 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160850 p = 1 := by simpa only [d160851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12606 p hg
    simpa only [d160851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12608 (p : Pattern) (guard : d160873 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160851 p = 1 := by simpa only [d160873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12607 p hg
    simpa only [d160873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12609 (p : Pattern) (guard : d160874 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160873 p = 1 := by simpa only [d160874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12608 p hg
    simpa only [d160874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12610 (p : Pattern) (guard : d160875 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160874 p = 1 := by simpa only [d160875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12609 p hg
    simpa only [d160875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12611 (p : Pattern) (guard : d160876 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160872 p = 1 := by simpa only [d160876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12604 p hg
    simpa only [d160876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160875 p = 1 := by simpa only [d160876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12610 p hg
    simpa only [d160876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12612 (p : Pattern) (guard : d160897 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160876 p = 1 := by simpa only [d160897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12611 p hg
    simpa only [d160897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12613 (p : Pattern) (guard : d160898 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160897 p = 1 := by simpa only [d160898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12612 p hg
    simpa only [d160898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12614 (p : Pattern) (guard : d160899 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160899, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160899, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160898 p = 1 := by simpa only [d160899, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12613 p hg
    simpa only [d160899, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12615 (p : Pattern) (guard : d160900 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160899 p = 1 := by simpa only [d160900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12614 p hg
    simpa only [d160900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12616 (p : Pattern) (guard : d160788 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160783 p = 1 := by simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12598 p hg
    simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12617 (p : Pattern) (guard : d160789 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160788 p = 1 := by simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12616 p hg
    simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12618 (p : Pattern) (guard : d160790 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160789 p = 1 := by simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12617 p hg
    simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12619 (p : Pattern) (guard : d160801 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160790 p = 1 := by simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12618 p hg
    simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12620 (p : Pattern) (guard : d160887 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160801 p = 1 := by simpa only [d160887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12619 p hg
    simpa only [d160887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12621 (p : Pattern) (guard : d160888 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160887 p = 1 := by simpa only [d160888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12620 p hg
    simpa only [d160888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12622 (p : Pattern) (guard : d160889 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160888 p = 1 := by simpa only [d160889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12621 p hg
    simpa only [d160889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12623 (p : Pattern) (guard : d160890 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160889 p = 1 := by simpa only [d160890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12622 p hg
    simpa only [d160890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12624 (p : Pattern) (guard : d160891 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160890 p = 1 := by simpa only [d160891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12623 p hg
    simpa only [d160891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12625 (p : Pattern) (guard : d160901 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160901, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160901, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160891 p = 1 := by simpa only [d160901, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12624 p hg
    simpa only [d160901, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12626 (p : Pattern) (guard : d160902 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160901 p = 1 := by simpa only [d160902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12625 p hg
    simpa only [d160902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12627 (p : Pattern) (guard : d160903 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160900 p = 1 := by simpa only [d160903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12615 p hg
    simpa only [d160903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160902 p = 1 := by simpa only [d160903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12626 p hg
    simpa only [d160903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12628 (p : Pattern) (guard : d160904 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160903 p = 1 := by simpa only [d160904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12627 p hg
    simpa only [d160904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12629 (p : Pattern) (guard : d160905 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160904 p = 1 := by simpa only [d160905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12628 p hg
    simpa only [d160905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12630 (p : Pattern) (guard : d160906 p = 1) : d47768 p ≤ (-1 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160896 p = 1 := by simpa only [d160906, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12545 p hg
    simpa only [d160906, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160905 p = 1 := by simpa only [d160906, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12629 p hg
    simpa only [d160906, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12631 (p : Pattern) (guard : d2335 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2335, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d2335, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2034 p = 1 := by simpa only [d2335, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7667 p hg
    simpa only [d2335, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12632 (p : Pattern) (guard : d2336 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2335 p = 1 := by simpa only [d2336, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12631 p hg
    simpa only [d2336, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2035 p = 1 := by simpa only [d2336, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7669 p hg
    simpa only [d2336, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12633 (p : Pattern) (guard : d2337 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2336 p = 1 := by simpa only [d2337, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12632 p hg
    simpa only [d2337, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2337, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7694 p hg
    simpa only [d2337, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12634 (p : Pattern) (guard : d2338 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2337 p = 1 := by simpa only [d2338, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12633 p hg
    simpa only [d2338, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2338, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d2338, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12635 (p : Pattern) (guard : d160907 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2338 p = 1 := by simpa only [d160907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12634 p hg
    simpa only [d160907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12636 (p : Pattern) (guard : d160908 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160907 p = 1 := by simpa only [d160908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12635 p hg
    simpa only [d160908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12637 (p : Pattern) (guard : d2340 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2340, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d2340, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2052 p = 1 := by simpa only [d2340, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d2340, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12638 (p : Pattern) (guard : d2341 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2340 p = 1 := by simpa only [d2341, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12637 p hg
    simpa only [d2341, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2053 p = 1 := by simpa only [d2341, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7713 p hg
    simpa only [d2341, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12639 (p : Pattern) (guard : d2342 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2341 p = 1 := by simpa only [d2342, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12638 p hg
    simpa only [d2342, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2342, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7730 p hg
    simpa only [d2342, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12640 (p : Pattern) (guard : d2343 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2342 p = 1 := by simpa only [d2343, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12639 p hg
    simpa only [d2343, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2343, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d2343, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12641 (p : Pattern) (guard : d160909 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2343 p = 1 := by simpa only [d160909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12640 p hg
    simpa only [d160909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12642 (p : Pattern) (guard : d160910 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160909 p = 1 := by simpa only [d160910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12641 p hg
    simpa only [d160910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12643 (p : Pattern) (guard : d160911 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160908 p = 1 := by simpa only [d160911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12636 p hg
    simpa only [d160911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160910 p = 1 := by simpa only [d160911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12642 p hg
    simpa only [d160911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12644 (p : Pattern) (guard : d160912 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160912, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160912, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160911 p = 1 := by simpa only [d160912, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12643 p hg
    simpa only [d160912, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12645 (p : Pattern) (guard : d160913 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160913, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160913, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160912 p = 1 := by simpa only [d160913, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12644 p hg
    simpa only [d160913, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12646 (p : Pattern) (guard : d5715 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7658 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12647 (p : Pattern) (guard : d5716 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5715 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12646 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12648 (p : Pattern) (guard : d5717 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5716 p = 1 := by simpa only [d5717, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12647 p hg
    simpa only [d5717, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5717, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d5717, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12649 (p : Pattern) (guard : d13677 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5717 p = 1 := by simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12648 p hg
    simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12650 (p : Pattern) (guard : d13817 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13817, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d13817, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13677 p = 1 := by simpa only [d13817, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12649 p hg
    simpa only [d13817, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12651 (p : Pattern) (guard : d13678 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13677 p = 1 := by simpa only [d13678, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12477 p hg
    simpa only [d13678, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13678, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d13678, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12652 (p : Pattern) (guard : d13818 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13817 p = 1 := by simpa only [d13818, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12650 p hg
    simpa only [d13818, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13678 p = 1 := by simpa only [d13818, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12651 p hg
    simpa only [d13818, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12653 (p : Pattern) (guard : d5715 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7683 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12654 (p : Pattern) (guard : d5716 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5715 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12653 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12655 (p : Pattern) (guard : d5717 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5716 p = 1 := by simpa only [d5717, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12654 p hg
    simpa only [d5717, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5717, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d5717, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12656 (p : Pattern) (guard : d13677 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5717 p = 1 := by simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12655 p hg
    simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12657 (p : Pattern) (guard : d13678 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13677 p = 1 := by simpa only [d13678, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12656 p hg
    simpa only [d13678, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13678, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d13678, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12658 (p : Pattern) (guard : d13679 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13678 p = 1 := by simpa only [d13679, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12657 p hg
    simpa only [d13679, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13679, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d13679, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12659 (p : Pattern) (guard : d13819 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d13818 p = 1 := by simpa only [d13819, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12652 p hg
    simpa only [d13819, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13679 p = 1 := by simpa only [d13819, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12658 p hg
    simpa only [d13819, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12660 (p : Pattern) (guard : d13820 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13819 p = 1 := by simpa only [d13820, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12659 p hg
    simpa only [d13820, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13820, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d13820, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12661 (p : Pattern) (guard : d160914 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13820 p = 1 := by simpa only [d160914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12660 p hg
    simpa only [d160914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12662 (p : Pattern) (guard : d160915 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160914 p = 1 := by simpa only [d160915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12661 p hg
    simpa only [d160915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12663 (p : Pattern) (guard : d160916 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160910 p = 1 := by simpa only [d160916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12642 p hg
    simpa only [d160916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160915 p = 1 := by simpa only [d160916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12662 p hg
    simpa only [d160916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12664 (p : Pattern) (guard : d160917 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160917, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160917, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160916 p = 1 := by simpa only [d160917, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12663 p hg
    simpa only [d160917, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12665 (p : Pattern) (guard : d160918 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160918, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160918, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160917 p = 1 := by simpa only [d160918, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12664 p hg
    simpa only [d160918, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12666 (p : Pattern) (guard : d160919 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160913 p = 1 := by simpa only [d160919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12645 p hg
    simpa only [d160919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160918 p = 1 := by simpa only [d160919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12665 p hg
    simpa only [d160919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12667 (p : Pattern) (guard : d2346 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2346, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d2346, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2064 p = 1 := by simpa only [d2346, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7741 p hg
    simpa only [d2346, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12668 (p : Pattern) (guard : d2347 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2346 p = 1 := by simpa only [d2347, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12667 p hg
    simpa only [d2347, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2065 p = 1 := by simpa only [d2347, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7743 p hg
    simpa only [d2347, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12669 (p : Pattern) (guard : d2348 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2347 p = 1 := by simpa only [d2348, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12668 p hg
    simpa only [d2348, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2348, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7753 p hg
    simpa only [d2348, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12670 (p : Pattern) (guard : d2349 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2348 p = 1 := by simpa only [d2349, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12669 p hg
    simpa only [d2349, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2349, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d2349, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12671 (p : Pattern) (guard : d160920 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2349 p = 1 := by simpa only [d160920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12670 p hg
    simpa only [d160920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12672 (p : Pattern) (guard : d160921 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160920 p = 1 := by simpa only [d160921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12671 p hg
    simpa only [d160921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12673 (p : Pattern) (guard : d160922 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160910 p = 1 := by simpa only [d160922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12642 p hg
    simpa only [d160922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160921 p = 1 := by simpa only [d160922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12672 p hg
    simpa only [d160922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12674 (p : Pattern) (guard : d160923 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160923, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160923, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160922 p = 1 := by simpa only [d160923, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12673 p hg
    simpa only [d160923, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12675 (p : Pattern) (guard : d160924 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160924, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160924, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160923 p = 1 := by simpa only [d160924, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12674 p hg
    simpa only [d160924, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12676 (p : Pattern) (guard : d160925 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160921 p = 1 := by simpa only [d160925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12672 p hg
    simpa only [d160925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12677 (p : Pattern) (guard : d160926 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160926, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160926, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160925 p = 1 := by simpa only [d160926, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12676 p hg
    simpa only [d160926, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12678 (p : Pattern) (guard : d160927 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160927, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160927, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160926 p = 1 := by simpa only [d160927, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12677 p hg
    simpa only [d160927, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12679 (p : Pattern) (guard : d160928 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160924 p = 1 := by simpa only [d160928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12675 p hg
    simpa only [d160928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160927 p = 1 := by simpa only [d160928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12678 p hg
    simpa only [d160928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12680 (p : Pattern) (guard : d160929 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160919 p = 1 := by simpa only [d160929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12666 p hg
    simpa only [d160929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160928 p = 1 := by simpa only [d160929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12679 p hg
    simpa only [d160929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12681 (p : Pattern) (guard : d160930 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160929 p = 1 := by simpa only [d160930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12680 p hg
    simpa only [d160930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12682 (p : Pattern) (guard : d160931 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160930 p = 1 := by simpa only [d160931, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12681 p hg
    simpa only [d160931, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160931, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160931, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12683 (p : Pattern) (guard : d160932 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160932, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160932, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160931 p = 1 := by simpa only [d160932, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12682 p hg
    simpa only [d160932, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12684 (p : Pattern) (guard : d160933 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160927 p = 1 := by simpa only [d160933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12678 p hg
    simpa only [d160933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12685 (p : Pattern) (guard : d160934 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160928 p = 1 := by simpa only [d160934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12679 p hg
    simpa only [d160934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160933 p = 1 := by simpa only [d160934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12684 p hg
    simpa only [d160934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12686 (p : Pattern) (guard : d160935 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160934 p = 1 := by simpa only [d160935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12685 p hg
    simpa only [d160935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12687 (p : Pattern) (guard : d160936 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160935 p = 1 := by simpa only [d160936, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12686 p hg
    simpa only [d160936, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160936, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160936, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12688 (p : Pattern) (guard : d160937 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160937, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160937, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160936 p = 1 := by simpa only [d160937, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12687 p hg
    simpa only [d160937, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12689 (p : Pattern) (guard : d160938 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160932 p = 1 := by simpa only [d160938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12683 p hg
    simpa only [d160938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160937 p = 1 := by simpa only [d160938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12688 p hg
    simpa only [d160938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12690 (p : Pattern) (guard : d160939 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160938 p = 1 := by simpa only [d160939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12689 p hg
    simpa only [d160939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12691 (p : Pattern) (guard : d160940 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160939 p = 1 := by simpa only [d160940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12690 p hg
    simpa only [d160940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12692 (p : Pattern) (guard : d160941 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160940 p = 1 := by simpa only [d160941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12691 p hg
    simpa only [d160941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12693 (p : Pattern) (guard : d160942 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160933 p = 1 := by simpa only [d160942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12684 p hg
    simpa only [d160942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12694 (p : Pattern) (guard : d160943 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160942 p = 1 := by simpa only [d160943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12693 p hg
    simpa only [d160943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12695 (p : Pattern) (guard : d160944 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160943 p = 1 := by simpa only [d160944, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12694 p hg
    simpa only [d160944, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160944, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160944, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12696 (p : Pattern) (guard : d160945 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160945, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160945, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160944 p = 1 := by simpa only [d160945, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12695 p hg
    simpa only [d160945, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12697 (p : Pattern) (guard : d160946 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160937 p = 1 := by simpa only [d160946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12688 p hg
    simpa only [d160946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160945 p = 1 := by simpa only [d160946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12696 p hg
    simpa only [d160946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12698 (p : Pattern) (guard : d160947 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160946 p = 1 := by simpa only [d160947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12697 p hg
    simpa only [d160947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12699 (p : Pattern) (guard : d160948 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160947 p = 1 := by simpa only [d160948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12698 p hg
    simpa only [d160948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12700 (p : Pattern) (guard : d160949 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160948 p = 1 := by simpa only [d160949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12699 p hg
    simpa only [d160949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12701 (p : Pattern) (guard : d160950 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160941 p = 1 := by simpa only [d160950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12692 p hg
    simpa only [d160950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160949 p = 1 := by simpa only [d160950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12700 p hg
    simpa only [d160950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12702 (p : Pattern) (guard : d160951 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160950 p = 1 := by simpa only [d160951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12701 p hg
    simpa only [d160951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12703 (p : Pattern) (guard : d160952 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160937 p = 1 := by simpa only [d160952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12688 p hg
    simpa only [d160952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12704 (p : Pattern) (guard : d160953 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160952 p = 1 := by simpa only [d160953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12703 p hg
    simpa only [d160953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12705 (p : Pattern) (guard : d160954 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160953 p = 1 := by simpa only [d160954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12704 p hg
    simpa only [d160954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12706 (p : Pattern) (guard : d160955 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160954 p = 1 := by simpa only [d160955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12705 p hg
    simpa only [d160955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12707 (p : Pattern) (guard : d160956 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160955 p = 1 := by simpa only [d160956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12706 p hg
    simpa only [d160956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12708 (p : Pattern) (guard : d160957 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160956 p = 1 := by simpa only [d160957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12707 p hg
    simpa only [d160957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12709 (p : Pattern) (guard : d160958 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160951 p = 1 := by simpa only [d160958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12702 p hg
    simpa only [d160958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160957 p = 1 := by simpa only [d160958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12708 p hg
    simpa only [d160958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12710 (p : Pattern) (guard : d160959 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160958 p = 1 := by simpa only [d160959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d160959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12711 (p : Pattern) (guard : d160960 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160959 p = 1 := by simpa only [d160960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12710 p hg
    simpa only [d160960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12712 (p : Pattern) (guard : d160961 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160961, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160961, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160960 p = 1 := by simpa only [d160961, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12711 p hg
    simpa only [d160961, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12713 (p : Pattern) (guard : d160962 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160961 p = 1 := by simpa only [d160962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12712 p hg
    simpa only [d160962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12714 (p : Pattern) (guard : d160963 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160945 p = 1 := by simpa only [d160963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12696 p hg
    simpa only [d160963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12715 (p : Pattern) (guard : d160964 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160963 p = 1 := by simpa only [d160964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12714 p hg
    simpa only [d160964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12716 (p : Pattern) (guard : d160965 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160964 p = 1 := by simpa only [d160965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12715 p hg
    simpa only [d160965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12717 (p : Pattern) (guard : d160966 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160965 p = 1 := by simpa only [d160966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12716 p hg
    simpa only [d160966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12718 (p : Pattern) (guard : d160967 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160966 p = 1 := by simpa only [d160967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12717 p hg
    simpa only [d160967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12719 (p : Pattern) (guard : d160968 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160967 p = 1 := by simpa only [d160968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12718 p hg
    simpa only [d160968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12720 (p : Pattern) (guard : d160969 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160968 p = 1 := by simpa only [d160969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12719 p hg
    simpa only [d160969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12721 (p : Pattern) (guard : d160970 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160969 p = 1 := by simpa only [d160970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12720 p hg
    simpa only [d160970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12722 (p : Pattern) (guard : d160971 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160970 p = 1 := by simpa only [d160971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12721 p hg
    simpa only [d160971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12723 (p : Pattern) (guard : d160972 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160972, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160972, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160971 p = 1 := by simpa only [d160972, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12722 p hg
    simpa only [d160972, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12724 (p : Pattern) (guard : d160973 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160972 p = 1 := by simpa only [d160973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12723 p hg
    simpa only [d160973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12725 (p : Pattern) (guard : d160974 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160962 p = 1 := by simpa only [d160974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12713 p hg
    simpa only [d160974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160973 p = 1 := by simpa only [d160974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12724 p hg
    simpa only [d160974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12726 (p : Pattern) (guard : d160975 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160974 p = 1 := by simpa only [d160975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12725 p hg
    simpa only [d160975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12727 (p : Pattern) (guard : d160976 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160975 p = 1 := by simpa only [d160976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12726 p hg
    simpa only [d160976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12728 (p : Pattern) (guard : d160977 p = 1) : d47865 p ≤ (-1 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160976 p = 1 := by simpa only [d160977, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12727 p hg
    simpa only [d160977, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160977, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11105 p hg
    simpa only [d160977, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12729 (p : Pattern) (guard : d160978 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d160906 p = 1 := by simpa only [d160978, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12630 p hg
    simpa only [d160978, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160977 p = 1 := by simpa only [d160978, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d160978, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12730 (p : Pattern) (guard : d160979 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160978 p = 1 := by simpa only [d160979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12729 p hg
    simpa only [d160979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12731 (p : Pattern) (guard : d160980 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160979 p = 1 := by simpa only [d160980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12730 p hg
    simpa only [d160980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12732 (p : Pattern) (guard : d160981 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160980 p = 1 := by simpa only [d160981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12731 p hg
    simpa only [d160981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12733 (p : Pattern) (guard : d160982 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160981 p = 1 := by simpa only [d160982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12732 p hg
    simpa only [d160982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12734 (p : Pattern) (guard : d160983 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160982 p = 1 := by simpa only [d160983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12733 p hg
    simpa only [d160983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12735 (p : Pattern) (guard : d160984 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160983 p = 1 := by simpa only [d160984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12734 p hg
    simpa only [d160984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12736 (p : Pattern) (guard : d160985 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160984 p = 1 := by simpa only [d160985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12735 p hg
    simpa only [d160985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12737 (p : Pattern) (guard : d160986 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160985 p = 1 := by simpa only [d160986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12736 p hg
    simpa only [d160986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12738 (p : Pattern) (guard : d160987 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160986 p = 1 := by simpa only [d160987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12737 p hg
    simpa only [d160987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12739 (p : Pattern) (guard : d160988 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160987 p = 1 := by simpa only [d160988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12738 p hg
    simpa only [d160988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12740 (p : Pattern) (guard : d160989 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d160763 p = 1 := by simpa only [d160989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12398 p hg
    simpa only [d160989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160988 p = 1 := by simpa only [d160989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12739 p hg
    simpa only [d160989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12741 (p : Pattern) (guard : d160990 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 260 with
  | false =>
    have hg : d160989 p = 1 := by simpa only [d160990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12740 p hg
    simpa only [d160990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12742 (p : Pattern) (guard : d160991 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 259 with
  | false =>
    have hg : d160990 p = 1 := by simpa only [d160991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12741 p hg
    simpa only [d160991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12743 (p : Pattern) (guard : d160992 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 258 with
  | false =>
    have hg : d160991 p = 1 := by simpa only [d160992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12742 p hg
    simpa only [d160992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12744 (p : Pattern) (guard : d160993 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 257 with
  | false =>
    have hg : d160992 p = 1 := by simpa only [d160993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12743 p hg
    simpa only [d160993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12745 (p : Pattern) (guard : d160994 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 256 with
  | false =>
    have hg : d160993 p = 1 := by simpa only [d160994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12744 p hg
    simpa only [d160994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12746 (p : Pattern) (guard : d160995 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 255 with
  | false =>
    have hg : d160994 p = 1 := by simpa only [d160995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12745 p hg
    simpa only [d160995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12747 (p : Pattern) (guard : d160996 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 254 with
  | false =>
    have hg : d160995 p = 1 := by simpa only [d160996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12746 p hg
    simpa only [d160996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12748 (p : Pattern) (guard : d160997 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 253 with
  | false =>
    have hg : d160996 p = 1 := by simpa only [d160997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12747 p hg
    simpa only [d160997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12749 (p : Pattern) (guard : d160998 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 252 with
  | false =>
    have hg : d160997 p = 1 := by simpa only [d160998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12748 p hg
    simpa only [d160998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160998, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
