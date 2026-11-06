/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons018
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c2660 (pattern : Twelve) (guard : d1864 pattern = 1) : d342 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2652 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2659 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2661 (pattern : Twelve) (guard : d1864 pattern = 1) : d344 pattern ≤ (0 : Int) + d424 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d344, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2644 pattern childGuard
    simpa only [d344, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d344, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2660 pattern childGuard
    simpa only [d344, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2662 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d163 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2663 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d367 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2662 pattern childGuard
    simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2664 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d373 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1272 pattern childGuard
    simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2663 pattern childGuard
    simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2665 (pattern : Twelve) (guard : d0 pattern = 1) : d816 pattern ≤ (0 : Int) + d818 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2666 (pattern : Twelve) (guard : d1849 pattern = 1) : d824 pattern ≤ (0 : Int) + d1030 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d824, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1397 pattern childGuard
    simpa only [d1849, d824, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d824, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2665 pattern childGuard
    simpa only [d1849, d824, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2667 (pattern : Twelve) (guard : d1863 pattern = 1) : d838 pattern ≤ (0 : Int) + d1038 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d838, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d1863, d838, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d838, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2666 pattern childGuard
    simpa only [d1863, d838, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2668 (pattern : Twelve) (guard : d0 pattern = 1) : d909 pattern ≤ (0 : Int) + d1039 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2669 (pattern : Twelve) (guard : d1864 pattern = 1) : d980 pattern ≤ (0 : Int) + d1048 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d980, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2667 pattern childGuard
    simpa only [d1864, d980, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d980, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2668 pattern childGuard
    simpa only [d1864, d980, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2670 (pattern : Twelve) (guard : d1848 pattern = 1) : d56 pattern ≤ (0 : Int) + d377 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1285 pattern childGuard
    simpa only [d56, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2566 pattern childGuard
    simpa only [d56, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2671 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (0 : Int) + d818 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2672 (pattern : Twelve) (guard : d1849 pattern = 1) : d826 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d826, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1849, d826, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d826, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2671 pattern childGuard
    simpa only [d1849, d826, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2673 (pattern : Twelve) (guard : d1863 pattern = 1) : d840 pattern ≤ (0 : Int) + d1040 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d840, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2670 pattern childGuard
    simpa only [d1863, d840, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d840, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2672 pattern childGuard
    simpa only [d1863, d840, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2674 (pattern : Twelve) (guard : d0 pattern = 1) : d910 pattern ≤ (0 : Int) + d1041 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2675 (pattern : Twelve) (guard : d1864 pattern = 1) : d981 pattern ≤ (0 : Int) + d1049 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d981, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2673 pattern childGuard
    simpa only [d1864, d981, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d981, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2674 pattern childGuard
    simpa only [d1864, d981, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2676 (pattern : Twelve) (guard : d1864 pattern = 1) : d991 pattern ≤ (0 : Int) + d1054 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d991, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2669 pattern childGuard
    simpa only [d991, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d991, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2675 pattern childGuard
    simpa only [d991, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2677 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d377 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1304 pattern childGuard
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2678 (pattern : Twelve) (guard : d1849 pattern = 1) : d824 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d824, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1415 pattern childGuard
    simpa only [d1849, d824, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d824, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2665 pattern childGuard
    simpa only [d1849, d824, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2679 (pattern : Twelve) (guard : d1863 pattern = 1) : d838 pattern ≤ (0 : Int) + d1040 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d838, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2677 pattern childGuard
    simpa only [d1863, d838, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d838, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2678 pattern childGuard
    simpa only [d1863, d838, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2680 (pattern : Twelve) (guard : d1864 pattern = 1) : d982 pattern ≤ (0 : Int) + d1049 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d982, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2679 pattern childGuard
    simpa only [d1864, d982, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d982, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2674 pattern childGuard
    simpa only [d1864, d982, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2681 (pattern : Twelve) (guard : d1863 pattern = 1) : d840 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d840, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d1863, d840, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d840, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2672 pattern childGuard
    simpa only [d1863, d840, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2682 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1041 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2683 (pattern : Twelve) (guard : d1864 pattern = 1) : d983 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d983, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2681 pattern childGuard
    simpa only [d1864, d983, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d983, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2682 pattern childGuard
    simpa only [d1864, d983, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2684 (pattern : Twelve) (guard : d1864 pattern = 1) : d992 pattern ≤ (0 : Int) + d1055 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d992, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2680 pattern childGuard
    simpa only [d992, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d992, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2683 pattern childGuard
    simpa only [d992, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2685 (pattern : Twelve) (guard : d1864 pattern = 1) : d1000 pattern ≤ (0 : Int) + d1060 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1000, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2676 pattern childGuard
    simpa only [d1000, d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1000, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2684 pattern childGuard
    simpa only [d1000, d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2686 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d383 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1325 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2687 (pattern : Twelve) (guard : d0 pattern = 1) : d819 pattern ≤ (0 : Int) + d818 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2688 (pattern : Twelve) (guard : d1849 pattern = 1) : d828 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d828, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1849, d828, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d828, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2687 pattern childGuard
    simpa only [d1849, d828, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2689 (pattern : Twelve) (guard : d1863 pattern = 1) : d842 pattern ≤ (0 : Int) + d1043 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d842, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2686 pattern childGuard
    simpa only [d1863, d842, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d842, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2688 pattern childGuard
    simpa only [d1863, d842, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2690 (pattern : Twelve) (guard : d0 pattern = 1) : d911 pattern ≤ (0 : Int) + d1041 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2691 (pattern : Twelve) (guard : d1864 pattern = 1) : d984 pattern ≤ (0 : Int) + d1051 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d984, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2689 pattern childGuard
    simpa only [d1864, d984, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d984, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2690 pattern childGuard
    simpa only [d1864, d984, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2692 (pattern : Twelve) (guard : d0 pattern = 1) : d820 pattern ≤ (0 : Int) + d820 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2693 (pattern : Twelve) (guard : d1849 pattern = 1) : d829 pattern ≤ (0 : Int) + d1034 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d829, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d829, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d829, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2692 pattern childGuard
    simpa only [d1849, d829, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2694 (pattern : Twelve) (guard : d1863 pattern = 1) : d844 pattern ≤ (0 : Int) + d1044 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d844, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1863, d844, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d844, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2693 pattern childGuard
    simpa only [d1863, d844, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2695 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1045 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2696 (pattern : Twelve) (guard : d1864 pattern = 1) : d985 pattern ≤ (0 : Int) + d1052 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d985, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2694 pattern childGuard
    simpa only [d1864, d985, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d985, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2695 pattern childGuard
    simpa only [d1864, d985, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2697 (pattern : Twelve) (guard : d1864 pattern = 1) : d993 pattern ≤ (0 : Int) + d1056 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d993, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2691 pattern childGuard
    simpa only [d993, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d993, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2696 pattern childGuard
    simpa only [d993, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2698 (pattern : Twelve) (guard : d1864 pattern = 1) : d994 pattern ≤ (0 : Int) + d1057 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d994, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2683 pattern childGuard
    simpa only [d994, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d994, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d994, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2699 (pattern : Twelve) (guard : d1864 pattern = 1) : d1001 pattern ≤ (0 : Int) + d1061 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1001, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2697 pattern childGuard
    simpa only [d1001, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1001, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2698 pattern childGuard
    simpa only [d1001, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2700 (pattern : Twelve) (guard : d1864 pattern = 1) : d1004 pattern ≤ (0 : Int) + d1064 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1004, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2685 pattern childGuard
    simpa only [d1004, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1004, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2699 pattern childGuard
    simpa only [d1004, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2701 (pattern : Twelve) (guard : d1863 pattern = 1) : d838 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d838, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d1863, d838, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d838, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2678 pattern childGuard
    simpa only [d1863, d838, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2702 (pattern : Twelve) (guard : d1864 pattern = 1) : d986 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d986, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2701 pattern childGuard
    simpa only [d1864, d986, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d986, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2682 pattern childGuard
    simpa only [d1864, d986, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2703 (pattern : Twelve) (guard : d0 pattern = 1) : d45 pattern ≤ (0 : Int) + d818 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2704 (pattern : Twelve) (guard : d1849 pattern = 1) : d832 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d832, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1849, d832, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d832, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2703 pattern childGuard
    simpa only [d1849, d832, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2705 (pattern : Twelve) (guard : d1863 pattern = 1) : d847 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d847, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d1863, d847, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d847, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2704 pattern childGuard
    simpa only [d1863, d847, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2706 (pattern : Twelve) (guard : d1864 pattern = 1) : d987 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d987, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2705 pattern childGuard
    simpa only [d1864, d987, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d987, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2682 pattern childGuard
    simpa only [d1864, d987, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2707 (pattern : Twelve) (guard : d1864 pattern = 1) : d995 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2702 pattern childGuard
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2706 pattern childGuard
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2708 (pattern : Twelve) (guard : d0 pattern = 1) : d46 pattern ≤ (0 : Int) + d818 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2709 (pattern : Twelve) (guard : d1849 pattern = 1) : d834 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d834, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1849, d834, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d834, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2708 pattern childGuard
    simpa only [d1849, d834, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2710 (pattern : Twelve) (guard : d1863 pattern = 1) : d849 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d849, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1863, d849, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d849, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2709 pattern childGuard
    simpa only [d1863, d849, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2711 (pattern : Twelve) (guard : d1864 pattern = 1) : d988 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d988, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2710 pattern childGuard
    simpa only [d1864, d988, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d988, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2682 pattern childGuard
    simpa only [d1864, d988, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2712 (pattern : Twelve) (guard : d0 pattern = 1) : d47 pattern ≤ (0 : Int) + d820 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2713 (pattern : Twelve) (guard : d1849 pattern = 1) : d836 pattern ≤ (0 : Int) + d1034 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d836, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d836, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d836, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2712 pattern childGuard
    simpa only [d1849, d836, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2714 (pattern : Twelve) (guard : d1863 pattern = 1) : d851 pattern ≤ (0 : Int) + d1044 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d851, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1863, d851, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d851, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2713 pattern childGuard
    simpa only [d1863, d851, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2715 (pattern : Twelve) (guard : d1864 pattern = 1) : d989 pattern ≤ (0 : Int) + d1052 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d989, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2714 pattern childGuard
    simpa only [d1864, d989, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d989, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2695 pattern childGuard
    simpa only [d1864, d989, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2716 (pattern : Twelve) (guard : d1864 pattern = 1) : d996 pattern ≤ (0 : Int) + d1058 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d996, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2711 pattern childGuard
    simpa only [d996, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d996, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2715 pattern childGuard
    simpa only [d996, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2717 (pattern : Twelve) (guard : d1864 pattern = 1) : d997 pattern ≤ (0 : Int) + d1057 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d997, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2706 pattern childGuard
    simpa only [d997, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d997, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d997, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2718 (pattern : Twelve) (guard : d1864 pattern = 1) : d1002 pattern ≤ (0 : Int) + d1062 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1002, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2716 pattern childGuard
    simpa only [d1002, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1002, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2717 pattern childGuard
    simpa only [d1002, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2719 (pattern : Twelve) (guard : d1864 pattern = 1) : d1005 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1005, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2707 pattern childGuard
    simpa only [d1005, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1005, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2718 pattern childGuard
    simpa only [d1005, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2720 (pattern : Twelve) (guard : d1864 pattern = 1) : d1007 pattern ≤ (0 : Int) + d1067 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1007, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2700 pattern childGuard
    simpa only [d1007, d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1007, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2719 pattern childGuard
    simpa only [d1007, d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2721 (pattern : Twelve) (guard : d1864 pattern = 1) : d998 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2702 pattern childGuard
    simpa only [d998, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2683 pattern childGuard
    simpa only [d998, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2722 (pattern : Twelve) (guard : d1863 pattern = 1) : d842 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d842, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1863, d842, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d842, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2688 pattern childGuard
    simpa only [d1863, d842, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2723 (pattern : Twelve) (guard : d1864 pattern = 1) : d990 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d990, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2722 pattern childGuard
    simpa only [d1864, d990, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d990, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2682 pattern childGuard
    simpa only [d1864, d990, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2724 (pattern : Twelve) (guard : d1864 pattern = 1) : d999 pattern ≤ (0 : Int) + d1058 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d999, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2723 pattern childGuard
    simpa only [d999, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d999, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2696 pattern childGuard
    simpa only [d999, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2725 (pattern : Twelve) (guard : d1864 pattern = 1) : d1003 pattern ≤ (0 : Int) + d1062 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1003, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2724 pattern childGuard
    simpa only [d1003, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1003, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2698 pattern childGuard
    simpa only [d1003, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2726 (pattern : Twelve) (guard : d1864 pattern = 1) : d1006 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1006, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2721 pattern childGuard
    simpa only [d1006, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1006, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2725 pattern childGuard
    simpa only [d1006, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2727 (pattern : Twelve) (guard : d1864 pattern = 1) : d1008 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2726 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2719 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2728 (pattern : Twelve) (guard : d1864 pattern = 1) : d1009 pattern ≤ (0 : Int) + d1068 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1009, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2720 pattern childGuard
    simpa only [d1009, d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1009, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2727 pattern childGuard
    simpa only [d1009, d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2729 (pattern : Twelve) (guard : d0 pattern = 1) : d820 pattern ≤ (0 : Int) + d880 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2730 (pattern : Twelve) (guard : d1849 pattern = 1) : d829 pattern ≤ (0 : Int) + d1036 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d829, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d829, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d829, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2729 pattern childGuard
    simpa only [d1849, d829, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2731 (pattern : Twelve) (guard : d1863 pattern = 1) : d844 pattern ≤ (0 : Int) + d1046 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d844, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1863, d844, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d844, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2730 pattern childGuard
    simpa only [d1863, d844, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2732 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1047 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2733 (pattern : Twelve) (guard : d1864 pattern = 1) : d985 pattern ≤ (0 : Int) + d1053 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d985, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2731 pattern childGuard
    simpa only [d1864, d985, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d985, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2732 pattern childGuard
    simpa only [d1864, d985, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2734 (pattern : Twelve) (guard : d1864 pattern = 1) : d999 pattern ≤ (0 : Int) + d1059 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d999, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2723 pattern childGuard
    simpa only [d999, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d999, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2733 pattern childGuard
    simpa only [d999, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2735 (pattern : Twelve) (guard : d1864 pattern = 1) : d1003 pattern ≤ (0 : Int) + d1063 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1003, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2734 pattern childGuard
    simpa only [d1003, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1003, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2698 pattern childGuard
    simpa only [d1003, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2736 (pattern : Twelve) (guard : d1864 pattern = 1) : d1006 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1006, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2721 pattern childGuard
    simpa only [d1006, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1006, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2735 pattern childGuard
    simpa only [d1006, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2737 (pattern : Twelve) (guard : d0 pattern = 1) : d47 pattern ≤ (0 : Int) + d880 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2738 (pattern : Twelve) (guard : d1849 pattern = 1) : d836 pattern ≤ (0 : Int) + d1036 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d836, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d836, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d836, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2737 pattern childGuard
    simpa only [d1849, d836, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2739 (pattern : Twelve) (guard : d1863 pattern = 1) : d851 pattern ≤ (0 : Int) + d1046 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d851, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1863, d851, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d851, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2738 pattern childGuard
    simpa only [d1863, d851, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2740 (pattern : Twelve) (guard : d1864 pattern = 1) : d989 pattern ≤ (0 : Int) + d1053 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d989, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2739 pattern childGuard
    simpa only [d1864, d989, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d989, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2732 pattern childGuard
    simpa only [d1864, d989, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2741 (pattern : Twelve) (guard : d1864 pattern = 1) : d996 pattern ≤ (0 : Int) + d1059 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d996, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2711 pattern childGuard
    simpa only [d996, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d996, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2740 pattern childGuard
    simpa only [d996, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2742 (pattern : Twelve) (guard : d1864 pattern = 1) : d1002 pattern ≤ (0 : Int) + d1063 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1002, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2741 pattern childGuard
    simpa only [d1002, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1002, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2717 pattern childGuard
    simpa only [d1002, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2743 (pattern : Twelve) (guard : d1864 pattern = 1) : d1005 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1005, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2707 pattern childGuard
    simpa only [d1005, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1005, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2742 pattern childGuard
    simpa only [d1005, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2744 (pattern : Twelve) (guard : d1864 pattern = 1) : d1008 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2736 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2743 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2745 (pattern : Twelve) (guard : d1864 pattern = 1) : d1010 pattern ≤ (0 : Int) + d1069 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1010, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2728 pattern childGuard
    simpa only [d1010, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1010, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2744 pattern childGuard
    simpa only [d1010, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2746 (pattern : Twelve) (guard : d1848 pattern = 1) : d17 pattern ≤ (0 : Int) + d1031 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1402 pattern childGuard
    simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2747 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (0 : Int) + d1280 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2748 (pattern : Twelve) (guard : d1849 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1284, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1470 pattern childGuard
    simpa only [d1849, d1284, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1284, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2747 pattern childGuard
    simpa only [d1849, d1284, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2749 (pattern : Twelve) (guard : d1863 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1448 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1293, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2746 pattern childGuard
    simpa only [d1863, d1293, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1293, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2748 pattern childGuard
    simpa only [d1863, d1293, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2750 (pattern : Twelve) (guard : d0 pattern = 1) : d1355 pattern ≤ (0 : Int) + d1449 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2751 (pattern : Twelve) (guard : d1864 pattern = 1) : d1412 pattern ≤ (0 : Int) + d1455 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1412, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2749 pattern childGuard
    simpa only [d1864, d1412, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1412, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2750 pattern childGuard
    simpa only [d1864, d1412, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2752 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d36 pattern := by
  omega
theorem c2753 (pattern : Twelve) (guard : d1848 pattern = 1) : d827 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2752 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2754 (pattern : Twelve) (guard : d0 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1280 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2755 (pattern : Twelve) (guard : d1849 pattern = 1) : d1285 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1285, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1478 pattern childGuard
    simpa only [d1849, d1285, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1285, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2754 pattern childGuard
    simpa only [d1849, d1285, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2756 (pattern : Twelve) (guard : d1863 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1295, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2753 pattern childGuard
    simpa only [d1863, d1295, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1295, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2755 pattern childGuard
    simpa only [d1863, d1295, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2757 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1449 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2758 (pattern : Twelve) (guard : d1864 pattern = 1) : d1413 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1413, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2756 pattern childGuard
    simpa only [d1864, d1413, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1413, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2757 pattern childGuard
    simpa only [d1864, d1413, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2759 (pattern : Twelve) (guard : d1864 pattern = 1) : d1417 pattern ≤ (0 : Int) + d1459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1417, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2751 pattern childGuard
    simpa only [d1417, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1417, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2758 pattern childGuard
    simpa only [d1417, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2760 (pattern : Twelve) (guard : d1863 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1293, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d1863, d1293, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1293, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2748 pattern childGuard
    simpa only [d1863, d1293, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2761 (pattern : Twelve) (guard : d1864 pattern = 1) : d1414 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1414, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2760 pattern childGuard
    simpa only [d1864, d1414, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1414, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2757 pattern childGuard
    simpa only [d1864, d1414, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2762 (pattern : Twelve) (guard : d1864 pattern = 1) : d1418 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2761 pattern childGuard
    simpa only [d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2758 pattern childGuard
    simpa only [d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2763 (pattern : Twelve) (guard : d1864 pattern = 1) : d1421 pattern ≤ (0 : Int) + d1463 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1421, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2759 pattern childGuard
    simpa only [d1421, d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1421, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2762 pattern childGuard
    simpa only [d1421, d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2764 (pattern : Twelve) (guard : d0 pattern = 1) : d1281 pattern ≤ (0 : Int) + d1280 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2765 (pattern : Twelve) (guard : d1849 pattern = 1) : d1287 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1287, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1478 pattern childGuard
    simpa only [d1849, d1287, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1287, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2764 pattern childGuard
    simpa only [d1849, d1287, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2766 (pattern : Twelve) (guard : d1863 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1297, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1863, d1297, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1297, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2765 pattern childGuard
    simpa only [d1863, d1297, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2767 (pattern : Twelve) (guard : d1864 pattern = 1) : d1415 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1415, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2766 pattern childGuard
    simpa only [d1864, d1415, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1415, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2757 pattern childGuard
    simpa only [d1864, d1415, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2768 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d40 pattern := by
  omega
theorem c2769 (pattern : Twelve) (guard : d1848 pattern = 1) : d830 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2768 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2770 (pattern : Twelve) (guard : d0 pattern = 1) : d125 pattern ≤ (0 : Int) + d125 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2771 (pattern : Twelve) (guard : d1849 pattern = 1) : d1288 pattern ≤ (0 : Int) + d1446 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1288, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1491 pattern childGuard
    simpa only [d1849, d1288, d1446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1288, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2770 pattern childGuard
    simpa only [d1849, d1288, d1446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2772 (pattern : Twelve) (guard : d1863 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1451 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d1863, d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2771 pattern childGuard
    simpa only [d1863, d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2773 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1452 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2774 (pattern : Twelve) (guard : d1864 pattern = 1) : d1416 pattern ≤ (0 : Int) + d1457 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1416, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2772 pattern childGuard
    simpa only [d1864, d1416, d1457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1416, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2773 pattern childGuard
    simpa only [d1864, d1416, d1457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2775 (pattern : Twelve) (guard : d1864 pattern = 1) : d1419 pattern ≤ (0 : Int) + d1460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1419, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2767 pattern childGuard
    simpa only [d1419, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1419, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2774 pattern childGuard
    simpa only [d1419, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2776 (pattern : Twelve) (guard : d1864 pattern = 1) : d1420 pattern ≤ (0 : Int) + d1461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1420, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2758 pattern childGuard
    simpa only [d1420, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1420, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d1420, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2777 (pattern : Twelve) (guard : d1864 pattern = 1) : d1422 pattern ≤ (0 : Int) + d1464 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1422, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2775 pattern childGuard
    simpa only [d1422, d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1422, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2776 pattern childGuard
    simpa only [d1422, d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2778 (pattern : Twelve) (guard : d1864 pattern = 1) : d1423 pattern ≤ (0 : Int) + d1466 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1423, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2763 pattern childGuard
    simpa only [d1423, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1423, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2777 pattern childGuard
    simpa only [d1423, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2779 (pattern : Twelve) (guard : d1864 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1467 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1424, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2762 pattern childGuard
    simpa only [d1424, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1424, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2777 pattern childGuard
    simpa only [d1424, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2780 (pattern : Twelve) (guard : d1864 pattern = 1) : d1425 pattern ≤ (0 : Int) + d1469 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1425, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2778 pattern childGuard
    simpa only [d1425, d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1425, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2779 pattern childGuard
    simpa only [d1425, d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2781 (pattern : Twelve) (guard : d1864 pattern = 1) : d1426 pattern ≤ (0 : Int) + d1470 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1426, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2780 pattern childGuard
    simpa only [d1426, d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1426, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2779 pattern childGuard
    simpa only [d1426, d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2782 (pattern : Twelve) (guard : d0 pattern = 1) : d125 pattern ≤ (0 : Int) + d1331 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2783 (pattern : Twelve) (guard : d1849 pattern = 1) : d1288 pattern ≤ (0 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1491 pattern childGuard
    simpa only [d1849, d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2782 pattern childGuard
    simpa only [d1849, d1288, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2784 (pattern : Twelve) (guard : d1863 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1453 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1299, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d1863, d1299, d1453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1299, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2783 pattern childGuard
    simpa only [d1863, d1299, d1453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2785 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1454 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2786 (pattern : Twelve) (guard : d1864 pattern = 1) : d1416 pattern ≤ (0 : Int) + d1458 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1416, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d1864, d1416, d1458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1416, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2785 pattern childGuard
    simpa only [d1864, d1416, d1458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2787 (pattern : Twelve) (guard : d1864 pattern = 1) : d1419 pattern ≤ (0 : Int) + d1462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1419, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2767 pattern childGuard
    simpa only [d1419, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1419, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2786 pattern childGuard
    simpa only [d1419, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2788 (pattern : Twelve) (guard : d1864 pattern = 1) : d1422 pattern ≤ (0 : Int) + d1465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1422, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2787 pattern childGuard
    simpa only [d1422, d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1422, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2776 pattern childGuard
    simpa only [d1422, d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2789 (pattern : Twelve) (guard : d1864 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1468 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1424, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2762 pattern childGuard
    simpa only [d1424, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1424, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2788 pattern childGuard
    simpa only [d1424, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2790 (pattern : Twelve) (guard : d1864 pattern = 1) : d1427 pattern ≤ (0 : Int) + d1471 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1427, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2781 pattern childGuard
    simpa only [d1427, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1427, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2789 pattern childGuard
    simpa only [d1427, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2791 (pattern : Twelve) (guard : d0 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1645 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2792 (pattern : Twelve) (guard : d1849 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1523 pattern childGuard
    simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2791 pattern childGuard
    simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2793 (pattern : Twelve) (guard : d1863 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1649, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1473 pattern childGuard
    simpa only [d1863, d1649, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1649, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2792 pattern childGuard
    simpa only [d1863, d1649, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2794 (pattern : Twelve) (guard : d1864 pattern = 1) : d1705 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1705, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2793 pattern childGuard
    simpa only [d1864, d1705, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1705, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2773 pattern childGuard
    simpa only [d1864, d1705, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2795 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d29 pattern := by
  omega
theorem c2796 (pattern : Twelve) (guard : d1848 pattern = 1) : d1286 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2797 (pattern : Twelve) (guard : d0 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1645 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2798 (pattern : Twelve) (guard : d1849 pattern = 1) : d1647 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1531 pattern childGuard
    simpa only [d1849, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2797 pattern childGuard
    simpa only [d1849, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2799 (pattern : Twelve) (guard : d1863 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1651, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2796 pattern childGuard
    simpa only [d1863, d1651, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1651, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2798 pattern childGuard
    simpa only [d1863, d1651, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
