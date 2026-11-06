/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons161
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22680 (p : Pattern) (guard : d5537 p = 1) : d2647 p ≤ (0 : Int) + d1844 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2647, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22679 p hg
    simpa only [d2647, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2647, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22624 p hg
    simpa only [d2647, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22681 (p : Pattern) (guard : d5537 p = 1) : d2648 p ≤ (0 : Int) + d1845 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2648, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22676 p hg
    simpa only [d2648, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2648, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22680 p hg
    simpa only [d2648, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22682 (p : Pattern) (guard : d5537 p = 1) : d2649 p ≤ (0 : Int) + d1846 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2649, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22681 p hg
    simpa only [d2649, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2649, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22661 p hg
    simpa only [d2649, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22683 (p : Pattern) (guard : d5537 p = 1) : d2650 p ≤ (0 : Int) + d1847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2650, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22661 p hg
    simpa only [d2650, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2650, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2650, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22684 (p : Pattern) (guard : d5537 p = 1) : d2651 p ≤ (0 : Int) + d1848 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2651, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22682 p hg
    simpa only [d2651, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2651, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22683 p hg
    simpa only [d2651, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22685 (p : Pattern) (guard : d5537 p = 1) : d2652 p ≤ (0 : Int) + d1849 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2652, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22672 p hg
    simpa only [d2652, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2652, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22684 p hg
    simpa only [d2652, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22686 (p : Pattern) (guard : d0 p = 1) : d2507 p ≤ (0 : Int) + d358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22687 (p : Pattern) (guard : d5537 p = 1) : d2655 p ≤ (0 : Int) + d1850 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2655, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21288 p hg
    simpa only [d5537, d2655, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2655, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22686 p hg
    simpa only [d5537, d2655, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22688 (p : Pattern) (guard : d5537 p = 1) : d2656 p ≤ (0 : Int) + d1851 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2656, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22687 p hg
    simpa only [d2656, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2656, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22555 p hg
    simpa only [d2656, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22689 (p : Pattern) (guard : d5537 p = 1) : d2657 p ≤ (0 : Int) + d1852 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2657, d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22688 p hg
    simpa only [d2657, d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2657, d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22563 p hg
    simpa only [d2657, d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22690 (p : Pattern) (guard : d5537 p = 1) : d2658 p ≤ (0 : Int) + d1853 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2658, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22689 p hg
    simpa only [d2658, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2658, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22568 p hg
    simpa only [d2658, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22691 (p : Pattern) (guard : d5537 p = 1) : d2659 p ≤ (0 : Int) + d1854 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2659, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22690 p hg
    simpa only [d2659, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2659, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22575 p hg
    simpa only [d2659, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22692 (p : Pattern) (guard : d5537 p = 1) : d2660 p ≤ (0 : Int) + d1855 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2660, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22691 p hg
    simpa only [d2660, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2660, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22592 p hg
    simpa only [d2660, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22693 (p : Pattern) (guard : d5537 p = 1) : d2661 p ≤ (0 : Int) + d1856 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2661, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22559 p hg
    simpa only [d2661, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2661, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22600 p hg
    simpa only [d2661, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22694 (p : Pattern) (guard : d5537 p = 1) : d2662 p ≤ (0 : Int) + d1857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2662, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22693 p hg
    simpa only [d2662, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2662, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22602 p hg
    simpa only [d2662, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22695 (p : Pattern) (guard : d5537 p = 1) : d2663 p ≤ (0 : Int) + d1858 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2663, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22694 p hg
    simpa only [d2663, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2663, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22613 p hg
    simpa only [d2663, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22696 (p : Pattern) (guard : d5537 p = 1) : d2664 p ≤ (0 : Int) + d1859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2664, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22695 p hg
    simpa only [d2664, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2664, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22624 p hg
    simpa only [d2664, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22697 (p : Pattern) (guard : d5537 p = 1) : d2665 p ≤ (0 : Int) + d1860 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2665, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22692 p hg
    simpa only [d2665, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2665, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22696 p hg
    simpa only [d2665, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22698 (p : Pattern) (guard : d5537 p = 1) : d2666 p ≤ (0 : Int) + d1861 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2666, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22697 p hg
    simpa only [d2666, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2666, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22661 p hg
    simpa only [d2666, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22699 (p : Pattern) (guard : d5537 p = 1) : d2667 p ≤ (0 : Int) + d1862 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2667, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22698 p hg
    simpa only [d2667, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2667, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22671 p hg
    simpa only [d2667, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22700 (p : Pattern) (guard : d5537 p = 1) : d2668 p ≤ (0 : Int) + d1863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2668, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22563 p hg
    simpa only [d2668, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2668, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22568 p hg
    simpa only [d2668, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22701 (p : Pattern) (guard : d5537 p = 1) : d2669 p ≤ (0 : Int) + d1864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2669, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22700 p hg
    simpa only [d2669, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2669, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22575 p hg
    simpa only [d2669, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22702 (p : Pattern) (guard : d5537 p = 1) : d2670 p ≤ (0 : Int) + d1865 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2670, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22701 p hg
    simpa only [d2670, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2670, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22592 p hg
    simpa only [d2670, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22703 (p : Pattern) (guard : d5537 p = 1) : d2671 p ≤ (0 : Int) + d1866 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2671, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22702 p hg
    simpa only [d2671, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2671, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22680 p hg
    simpa only [d2671, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22704 (p : Pattern) (guard : d5537 p = 1) : d2672 p ≤ (0 : Int) + d1867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2672, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22703 p hg
    simpa only [d2672, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2672, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22661 p hg
    simpa only [d2672, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22705 (p : Pattern) (guard : d5537 p = 1) : d2673 p ≤ (0 : Int) + d1868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2673, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22704 p hg
    simpa only [d2673, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2673, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22683 p hg
    simpa only [d2673, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22706 (p : Pattern) (guard : d5537 p = 1) : d2674 p ≤ (0 : Int) + d1869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2674, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22699 p hg
    simpa only [d2674, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2674, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22705 p hg
    simpa only [d2674, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22707 (p : Pattern) (guard : d5537 p = 1) : d2675 p ≤ (0 : Int) + d1870 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2675, d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22685 p hg
    simpa only [d2675, d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2675, d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22706 p hg
    simpa only [d2675, d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22708 (p : Pattern) (guard : d0 p = 1) : d2680 p ≤ (0 : Int) + d358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22709 (p : Pattern) (guard : d5537 p = 1) : d2681 p ≤ (0 : Int) + d1871 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2681, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21313 p hg
    simpa only [d5537, d2681, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2681, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22708 p hg
    simpa only [d5537, d2681, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22710 (p : Pattern) (guard : d5537 p = 1) : d2684 p ≤ (0 : Int) + d1876 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2684, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21320 p hg
    simpa only [d5537, d2684, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2684, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2684, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22711 (p : Pattern) (guard : d5537 p = 1) : d2685 p ≤ (0 : Int) + d1877 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2685, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22709 p hg
    simpa only [d2685, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2685, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22710 p hg
    simpa only [d2685, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22712 (p : Pattern) (guard : d0 p = 1) : d2680 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22713 (p : Pattern) (guard : d5537 p = 1) : d2686 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2686, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d5537, d2686, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2686, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22712 p hg
    simpa only [d5537, d2686, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22714 (p : Pattern) (guard : d5537 p = 1) : d2687 p ≤ (0 : Int) + d1878 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2687, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22713 p hg
    simpa only [d2687, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2687, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22710 p hg
    simpa only [d2687, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22715 (p : Pattern) (guard : d5537 p = 1) : d2688 p ≤ (0 : Int) + d1879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2688, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22711 p hg
    simpa only [d2688, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2688, d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22714 p hg
    simpa only [d2688, d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22716 (p : Pattern) (guard : d0 p = 1) : d2691 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22717 (p : Pattern) (guard : d5537 p = 1) : d2692 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2692, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d5537, d2692, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2692, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22716 p hg
    simpa only [d5537, d2692, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22718 (p : Pattern) (guard : d5537 p = 1) : d2695 p ≤ (0 : Int) + d1884 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2695, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21333 p hg
    simpa only [d5537, d2695, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2695, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2695, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22719 (p : Pattern) (guard : d5537 p = 1) : d2696 p ≤ (0 : Int) + d1885 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2696, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22717 p hg
    simpa only [d2696, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2696, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22718 p hg
    simpa only [d2696, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22720 (p : Pattern) (guard : d5537 p = 1) : d2697 p ≤ (0 : Int) + d1886 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2697, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22714 p hg
    simpa only [d2697, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2697, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22719 p hg
    simpa only [d2697, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22721 (p : Pattern) (guard : d5537 p = 1) : d2698 p ≤ (0 : Int) + d1887 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2698, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22715 p hg
    simpa only [d2698, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2698, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22720 p hg
    simpa only [d2698, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22722 (p : Pattern) (guard : d5537 p = 1) : d2699 p ≤ (0 : Int) + d1888 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2699, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22607 p hg
    simpa only [d2699, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2699, d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2699, d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22723 (p : Pattern) (guard : d5537 p = 1) : d2700 p ≤ (0 : Int) + d1889 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2700, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22720 p hg
    simpa only [d2700, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2700, d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22722 p hg
    simpa only [d2700, d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22724 (p : Pattern) (guard : d5537 p = 1) : d2701 p ≤ (0 : Int) + d1890 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2701, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22721 p hg
    simpa only [d2701, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2701, d1890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22723 p hg
    simpa only [d2701, d1890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22725 (p : Pattern) (guard : d5537 p = 1) : d2705 p ≤ (0 : Int) + d1899 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2705, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21349 p hg
    simpa only [d5537, d2705, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2705, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2705, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22726 (p : Pattern) (guard : d5537 p = 1) : d2706 p ≤ (0 : Int) + d1900 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2706, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22713 p hg
    simpa only [d2706, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2706, d1900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22725 p hg
    simpa only [d2706, d1900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22727 (p : Pattern) (guard : d5537 p = 1) : d2710 p ≤ (0 : Int) + d1906 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2710, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21354 p hg
    simpa only [d5537, d2710, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2710, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2710, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22728 (p : Pattern) (guard : d5537 p = 1) : d2711 p ≤ (0 : Int) + d1907 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2711, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22713 p hg
    simpa only [d2711, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2711, d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22727 p hg
    simpa only [d2711, d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22729 (p : Pattern) (guard : d5537 p = 1) : d2712 p ≤ (0 : Int) + d1908 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2712, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22726 p hg
    simpa only [d2712, d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2712, d1908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22728 p hg
    simpa only [d2712, d1908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22730 (p : Pattern) (guard : d5537 p = 1) : d2713 p ≤ (0 : Int) + d1909 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2713, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22713 p hg
    simpa only [d2713, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2713, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2713, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22731 (p : Pattern) (guard : d5537 p = 1) : d2714 p ≤ (0 : Int) + d1910 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2714, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22717 p hg
    simpa only [d2714, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2714, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2714, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22732 (p : Pattern) (guard : d5537 p = 1) : d2715 p ≤ (0 : Int) + d1911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2715, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22730 p hg
    simpa only [d2715, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2715, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22731 p hg
    simpa only [d2715, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22733 (p : Pattern) (guard : d5537 p = 1) : d2716 p ≤ (0 : Int) + d1912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2716, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22729 p hg
    simpa only [d2716, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2716, d1912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22732 p hg
    simpa only [d2716, d1912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22734 (p : Pattern) (guard : d5537 p = 1) : d2717 p ≤ (0 : Int) + d278 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2717, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22619 p hg
    simpa only [d2717, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2717, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2717, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22735 (p : Pattern) (guard : d5537 p = 1) : d2718 p ≤ (0 : Int) + d1913 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2718, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22732 p hg
    simpa only [d2718, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2718, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22734 p hg
    simpa only [d2718, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22736 (p : Pattern) (guard : d5537 p = 1) : d2719 p ≤ (0 : Int) + d1914 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2719, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22733 p hg
    simpa only [d2719, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2719, d1914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22735 p hg
    simpa only [d2719, d1914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22737 (p : Pattern) (guard : d5537 p = 1) : d2720 p ≤ (0 : Int) + d1915 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2720, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22724 p hg
    simpa only [d2720, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2720, d1915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22736 p hg
    simpa only [d2720, d1915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22738 (p : Pattern) (guard : d0 p = 1) : d2680 p ≤ (0 : Int) + d333 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22739 (p : Pattern) (guard : d5537 p = 1) : d2723 p ≤ (0 : Int) + d1916 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2723, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21373 p hg
    simpa only [d5537, d2723, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2723, d1916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22738 p hg
    simpa only [d5537, d2723, d1916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22740 (p : Pattern) (guard : d5537 p = 1) : d2724 p ≤ (0 : Int) + d1917 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2724, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22739 p hg
    simpa only [d2724, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2724, d1917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22710 p hg
    simpa only [d2724, d1917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22741 (p : Pattern) (guard : d0 p = 1) : d2704 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22742 (p : Pattern) (guard : d5537 p = 1) : d2725 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2725, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d5537, d2725, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2725, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22741 p hg
    simpa only [d5537, d2725, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22743 (p : Pattern) (guard : d5537 p = 1) : d2728 p ≤ (0 : Int) + d1922 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2728, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21383 p hg
    simpa only [d5537, d2728, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2728, d1922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2728, d1922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22744 (p : Pattern) (guard : d5537 p = 1) : d2729 p ≤ (0 : Int) + d1923 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2729, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22742 p hg
    simpa only [d2729, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2729, d1923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22743 p hg
    simpa only [d2729, d1923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22745 (p : Pattern) (guard : d5537 p = 1) : d2730 p ≤ (0 : Int) + d1924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2730, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22740 p hg
    simpa only [d2730, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2730, d1924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22744 p hg
    simpa only [d2730, d1924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22746 (p : Pattern) (guard : d5537 p = 1) : d2731 p ≤ (0 : Int) + d1925 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2731, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22719 p hg
    simpa only [d2731, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2731, d1925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22607 p hg
    simpa only [d2731, d1925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22747 (p : Pattern) (guard : d5537 p = 1) : d2732 p ≤ (0 : Int) + d1926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2732, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22745 p hg
    simpa only [d2732, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2732, d1926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22746 p hg
    simpa only [d2732, d1926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22748 (p : Pattern) (guard : d5537 p = 1) : d2733 p ≤ (0 : Int) + d1927 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2733, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22719 p hg
    simpa only [d2733, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2733, d1927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22611 p hg
    simpa only [d2733, d1927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22749 (p : Pattern) (guard : d5537 p = 1) : d2734 p ≤ (0 : Int) + d1928 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2734, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22748 p hg
    simpa only [d2734, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2734, d1928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2734, d1928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22750 (p : Pattern) (guard : d5537 p = 1) : d2735 p ≤ (0 : Int) + d1929 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2735, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22747 p hg
    simpa only [d2735, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2735, d1929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22749 p hg
    simpa only [d2735, d1929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22751 (p : Pattern) (guard : d5537 p = 1) : d2736 p ≤ (0 : Int) + d1930 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2736, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22742 p hg
    simpa only [d2736, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2736, d1930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2736, d1930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22752 (p : Pattern) (guard : d5537 p = 1) : d2737 p ≤ (0 : Int) + d1931 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2737, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22728 p hg
    simpa only [d2737, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2737, d1931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22751 p hg
    simpa only [d2737, d1931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22753 (p : Pattern) (guard : d5537 p = 1) : d2738 p ≤ (0 : Int) + d1932 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2738, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22731 p hg
    simpa only [d2738, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2738, d1932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22619 p hg
    simpa only [d2738, d1932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22754 (p : Pattern) (guard : d5537 p = 1) : d2739 p ≤ (0 : Int) + d1933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2739, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22752 p hg
    simpa only [d2739, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2739, d1933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22753 p hg
    simpa only [d2739, d1933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22755 (p : Pattern) (guard : d5537 p = 1) : d2740 p ≤ (0 : Int) + d1934 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2740, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22731 p hg
    simpa only [d2740, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2740, d1934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22621 p hg
    simpa only [d2740, d1934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22756 (p : Pattern) (guard : d5537 p = 1) : d2741 p ≤ (0 : Int) + d1935 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2741, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22755 p hg
    simpa only [d2741, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2741, d1935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2741, d1935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22757 (p : Pattern) (guard : d5537 p = 1) : d2742 p ≤ (0 : Int) + d1936 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2742, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22754 p hg
    simpa only [d2742, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2742, d1936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22756 p hg
    simpa only [d2742, d1936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22758 (p : Pattern) (guard : d5537 p = 1) : d2743 p ≤ (0 : Int) + d1937 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2743, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22750 p hg
    simpa only [d2743, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2743, d1937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22757 p hg
    simpa only [d2743, d1937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22759 (p : Pattern) (guard : d5537 p = 1) : d2744 p ≤ (0 : Int) + d1938 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2744, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22737 p hg
    simpa only [d2744, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2744, d1938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22758 p hg
    simpa only [d2744, d1938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22760 (p : Pattern) (guard : d5537 p = 1) : d2745 p ≤ (0 : Int) + d1943 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2745, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21316 p hg
    simpa only [d5537, d2745, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2745, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2745, d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22761 (p : Pattern) (guard : d5537 p = 1) : d2746 p ≤ (0 : Int) + d1944 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2746, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22713 p hg
    simpa only [d2746, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2746, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22760 p hg
    simpa only [d2746, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22762 (p : Pattern) (guard : d5537 p = 1) : d2745 p ≤ (0 : Int) + d1952 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2745, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21413 p hg
    simpa only [d5537, d2745, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2745, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2745, d1952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22763 (p : Pattern) (guard : d5537 p = 1) : d2746 p ≤ (0 : Int) + d1953 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2746, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22713 p hg
    simpa only [d2746, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2746, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22762 p hg
    simpa only [d2746, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22764 (p : Pattern) (guard : d5537 p = 1) : d2746 p ≤ (0 : Int) + d1954 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22761 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22763 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22765 (p : Pattern) (guard : d5537 p = 1) : d2745 p ≤ (0 : Int) + d1958 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2745, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21344 p hg
    simpa only [d5537, d2745, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2745, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2745, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22766 (p : Pattern) (guard : d5537 p = 1) : d2746 p ≤ (0 : Int) + d1959 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2746, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22713 p hg
    simpa only [d2746, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2746, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22765 p hg
    simpa only [d2746, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22767 (p : Pattern) (guard : d5537 p = 1) : d2747 p ≤ (0 : Int) + d1967 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2747, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21362 p hg
    simpa only [d5537, d2747, d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2747, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2747, d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22768 (p : Pattern) (guard : d5537 p = 1) : d2748 p ≤ (0 : Int) + d1968 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2748, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22717 p hg
    simpa only [d2748, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2748, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22767 p hg
    simpa only [d2748, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22769 (p : Pattern) (guard : d5537 p = 1) : d2749 p ≤ (0 : Int) + d1969 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2749, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22766 p hg
    simpa only [d2749, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2749, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22768 p hg
    simpa only [d2749, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22770 (p : Pattern) (guard : d5537 p = 1) : d2750 p ≤ (0 : Int) + d1970 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2750, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22764 p hg
    simpa only [d2750, d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2750, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22769 p hg
    simpa only [d2750, d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22771 (p : Pattern) (guard : d5537 p = 1) : d2751 p ≤ (0 : Int) + d1971 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2751, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22769 p hg
    simpa only [d2751, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2751, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22722 p hg
    simpa only [d2751, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22772 (p : Pattern) (guard : d5537 p = 1) : d2752 p ≤ (0 : Int) + d1972 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2752, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22770 p hg
    simpa only [d2752, d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2752, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22771 p hg
    simpa only [d2752, d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22773 (p : Pattern) (guard : d5537 p = 1) : d2753 p ≤ (0 : Int) + d1973 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2753, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22742 p hg
    simpa only [d2753, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2753, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22725 p hg
    simpa only [d2753, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22774 (p : Pattern) (guard : d0 p = 1) : d2709 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22775 (p : Pattern) (guard : d5537 p = 1) : d2754 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2754, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21426 p hg
    simpa only [d5537, d2754, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2754, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22774 p hg
    simpa only [d5537, d2754, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22776 (p : Pattern) (guard : d5537 p = 1) : d2755 p ≤ (0 : Int) + d1974 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2755, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22775 p hg
    simpa only [d2755, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2755, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22727 p hg
    simpa only [d2755, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22777 (p : Pattern) (guard : d5537 p = 1) : d2756 p ≤ (0 : Int) + d1975 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2756, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22773 p hg
    simpa only [d2756, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2756, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22776 p hg
    simpa only [d2756, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22778 (p : Pattern) (guard : d5537 p = 1) : d2757 p ≤ (0 : Int) + d1976 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2757, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22777 p hg
    simpa only [d2757, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2757, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2757, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22779 (p : Pattern) (guard : d5537 p = 1) : d2758 p ≤ (0 : Int) + d1977 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2758, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22778 p hg
    simpa only [d2758, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2758, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2758, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22780 (p : Pattern) (guard : d5537 p = 1) : d2759 p ≤ (0 : Int) + d1978 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2759, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22772 p hg
    simpa only [d2759, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2759, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22779 p hg
    simpa only [d2759, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22781 (p : Pattern) (guard : d5537 p = 1) : d2760 p ≤ (0 : Int) + d1979 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2760, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22763 p hg
    simpa only [d2760, d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2760, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22773 p hg
    simpa only [d2760, d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22782 (p : Pattern) (guard : d5537 p = 1) : d2761 p ≤ (0 : Int) + d1980 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2761, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22768 p hg
    simpa only [d2761, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2761, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22607 p hg
    simpa only [d2761, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22783 (p : Pattern) (guard : d5537 p = 1) : d2762 p ≤ (0 : Int) + d1981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2762, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22781 p hg
    simpa only [d2762, d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2762, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22782 p hg
    simpa only [d2762, d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22784 (p : Pattern) (guard : d5537 p = 1) : d2763 p ≤ (0 : Int) + d1982 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2763, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22768 p hg
    simpa only [d2763, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2763, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22611 p hg
    simpa only [d2763, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22785 (p : Pattern) (guard : d5537 p = 1) : d2764 p ≤ (0 : Int) + d1983 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2764, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22784 p hg
    simpa only [d2764, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2764, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2764, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22786 (p : Pattern) (guard : d5537 p = 1) : d2765 p ≤ (0 : Int) + d1984 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2765, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22783 p hg
    simpa only [d2765, d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2765, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22785 p hg
    simpa only [d2765, d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22787 (p : Pattern) (guard : d5537 p = 1) : d2766 p ≤ (0 : Int) + d1985 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2766, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22776 p hg
    simpa only [d2766, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2766, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2766, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22788 (p : Pattern) (guard : d5537 p = 1) : d2767 p ≤ (0 : Int) + d1986 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2767, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22787 p hg
    simpa only [d2767, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2767, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2767, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22789 (p : Pattern) (guard : d5537 p = 1) : d2768 p ≤ (0 : Int) + d1987 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2768, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22788 p hg
    simpa only [d2768, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2768, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2768, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22790 (p : Pattern) (guard : d5537 p = 1) : d2769 p ≤ (0 : Int) + d1988 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2769, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22786 p hg
    simpa only [d2769, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2769, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22789 p hg
    simpa only [d2769, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22791 (p : Pattern) (guard : d5537 p = 1) : d2770 p ≤ (0 : Int) + d1989 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2770, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22780 p hg
    simpa only [d2770, d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2770, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22790 p hg
    simpa only [d2770, d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22792 (p : Pattern) (guard : d5537 p = 1) : d2771 p ≤ (0 : Int) + d1990 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2771, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22759 p hg
    simpa only [d2771, d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2771, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22791 p hg
    simpa only [d2771, d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22793 (p : Pattern) (guard : d5537 p = 1) : d2772 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22722 p hg
    simpa only [d2772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22794 (p : Pattern) (guard : d5537 p = 1) : d2773 p ≤ (0 : Int) + d1992 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2773, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22793 p hg
    simpa only [d2773, d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2773, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2773, d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22795 (p : Pattern) (guard : d5537 p = 1) : d2774 p ≤ (0 : Int) + d1993 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2774, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22794 p hg
    simpa only [d2774, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2774, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2774, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22796 (p : Pattern) (guard : d5537 p = 1) : d2775 p ≤ (0 : Int) + d1994 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2775, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22795 p hg
    simpa only [d2775, d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2775, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2775, d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22797 (p : Pattern) (guard : d5537 p = 1) : d2776 p ≤ (0 : Int) + d1995 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2776, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22791 p hg
    simpa only [d2776, d1995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2776, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22796 p hg
    simpa only [d2776, d1995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22798 (p : Pattern) (guard : d5537 p = 1) : d2777 p ≤ (0 : Int) + d1996 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2777, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22792 p hg
    simpa only [d2777, d1996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2777, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22797 p hg
    simpa only [d2777, d1996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22799 (p : Pattern) (guard : d5537 p = 1) : d2778 p ≤ (0 : Int) + d1997 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2778, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22714 p hg
    simpa only [d2778, d1997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2778, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22720 p hg
    simpa only [d2778, d1997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22800 (p : Pattern) (guard : d5537 p = 1) : d2779 p ≤ (0 : Int) + d1998 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2779, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22799 p hg
    simpa only [d2779, d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2779, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22723 p hg
    simpa only [d2779, d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22801 (p : Pattern) (guard : d5537 p = 1) : d2780 p ≤ (0 : Int) + d1999 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2780, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22800 p hg
    simpa only [d2780, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2780, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22736 p hg
    simpa only [d2780, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22802 (p : Pattern) (guard : d5537 p = 1) : d2781 p ≤ (0 : Int) + d2000 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2781, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22714 p hg
    simpa only [d2781, d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2781, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22744 p hg
    simpa only [d2781, d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22803 (p : Pattern) (guard : d5537 p = 1) : d2782 p ≤ (0 : Int) + d2001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2782, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22802 p hg
    simpa only [d2782, d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2782, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22746 p hg
    simpa only [d2782, d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22804 (p : Pattern) (guard : d5537 p = 1) : d2783 p ≤ (0 : Int) + d2002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2783, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22803 p hg
    simpa only [d2783, d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2783, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22749 p hg
    simpa only [d2783, d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22805 (p : Pattern) (guard : d5537 p = 1) : d2784 p ≤ (0 : Int) + d2003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2784, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22804 p hg
    simpa only [d2784, d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2784, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22757 p hg
    simpa only [d2784, d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22806 (p : Pattern) (guard : d5537 p = 1) : d2785 p ≤ (0 : Int) + d2004 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2785, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22801 p hg
    simpa only [d2785, d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2785, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22805 p hg
    simpa only [d2785, d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22807 (p : Pattern) (guard : d5537 p = 1) : d2786 p ≤ (0 : Int) + d2005 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2786, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22806 p hg
    simpa only [d2786, d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2786, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22791 p hg
    simpa only [d2786, d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22808 (p : Pattern) (guard : d5537 p = 1) : d2787 p ≤ (0 : Int) + d2006 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2787, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22791 p hg
    simpa only [d2787, d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2787, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d2787, d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22809 (p : Pattern) (guard : d5537 p = 1) : d2788 p ≤ (0 : Int) + d2007 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2788, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22807 p hg
    simpa only [d2788, d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2788, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22808 p hg
    simpa only [d2788, d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22810 (p : Pattern) (guard : d5537 p = 1) : d2789 p ≤ (0 : Int) + d2008 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2789, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22798 p hg
    simpa only [d2789, d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2789, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22809 p hg
    simpa only [d2789, d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22811 (p : Pattern) (guard : d5537 p = 1) : d2790 p ≤ (0 : Int) + d2009 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2790, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22685 p hg
    simpa only [d2790, d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2790, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22810 p hg
    simpa only [d2790, d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22812 (p : Pattern) (guard : d5537 p = 1) : d2791 p ≤ (0 : Int) + d2010 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2791, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22707 p hg
    simpa only [d2791, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2791, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22811 p hg
    simpa only [d2791, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22813 (p : Pattern) (guard : d5537 p = 1) : d2602 p ≤ (0 : Int) + d2013 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d2602, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21112 p hg
    simpa only [d5537, d2602, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d2602, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d2602, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22814 (p : Pattern) (guard : d5537 p = 1) : d2603 p ≤ (0 : Int) + d2014 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2603, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22565 p hg
    simpa only [d2603, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2603, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22813 p hg
    simpa only [d2603, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22815 (p : Pattern) (guard : d5537 p = 1) : d2604 p ≤ (0 : Int) + d2015 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2604, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22628 p hg
    simpa only [d2604, d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2604, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22814 p hg
    simpa only [d2604, d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22816 (p : Pattern) (guard : d5537 p = 1) : d2605 p ≤ (0 : Int) + d2016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2605, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22628 p hg
    simpa only [d2605, d2016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2605, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22815 p hg
    simpa only [d2605, d2016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22817 (p : Pattern) (guard : d5537 p = 1) : d2609 p ≤ (0 : Int) + d2017 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2609, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22815 p hg
    simpa only [d2609, d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2609, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22640 p hg
    simpa only [d2609, d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22818 (p : Pattern) (guard : d5537 p = 1) : d2610 p ≤ (0 : Int) + d2018 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2610, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22816 p hg
    simpa only [d2610, d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2610, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22817 p hg
    simpa only [d2610, d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22819 (p : Pattern) (guard : d5537 p = 1) : d2792 p ≤ (0 : Int) + d2019 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d2792, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22598 p hg
    simpa only [d2792, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d2792, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22579 p hg
    simpa only [d2792, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
