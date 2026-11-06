/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons305
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42840 (p : Pattern) (guard : d8107 p = 1) : d2746 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42839 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42820 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42841 (p : Pattern) (guard : d8112 p = 1) : d2749 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42793 p hg
    simpa only [d8112, d2749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42797 p hg
    simpa only [d8112, d2749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42842 (p : Pattern) (guard : d8113 p = 1) : d2750 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2750, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42840 p hg
    simpa only [d8113, d2750, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2750, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42841 p hg
    simpa only [d8113, d2750, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42843 (p : Pattern) (guard : d8118 p = 1) : d2751 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2751, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42798 p hg
    simpa only [d8118, d2751, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2751, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42802 p hg
    simpa only [d8118, d2751, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42844 (p : Pattern) (guard : d8119 p = 1) : d2752 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2752, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42842 p hg
    simpa only [d8119, d2752, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2752, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42843 p hg
    simpa only [d8119, d2752, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42845 (p : Pattern) (guard : d8089 p = 1) : d2702 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2702, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38206 p hg
    simpa only [d8089, d2702, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2702, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2702, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42846 (p : Pattern) (guard : d8094 p = 1) : d2702 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42845 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42749 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42847 (p : Pattern) (guard : d8100 p = 1) : d2725 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2725, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42846 p hg
    simpa only [d8100, d2725, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2725, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42751 p hg
    simpa only [d8100, d2725, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42848 (p : Pattern) (guard : d8106 p = 1) : d2753 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2753, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42847 p hg
    simpa only [d8106, d2753, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2753, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42807 p hg
    simpa only [d8106, d2753, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42849 (p : Pattern) (guard : d8112 p = 1) : d2756 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2756, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42848 p hg
    simpa only [d8112, d2756, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2756, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42812 p hg
    simpa only [d8112, d2756, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42850 (p : Pattern) (guard : d8118 p = 1) : d2757 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2757, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42849 p hg
    simpa only [d8118, d2757, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2757, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2757, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42851 (p : Pattern) (guard : d8124 p = 1) : d2758 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2758, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42850 p hg
    simpa only [d8124, d2758, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2758, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2758, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42852 (p : Pattern) (guard : d8125 p = 1) : d2759 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2759, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42844 p hg
    simpa only [d8125, d2759, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2759, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42851 p hg
    simpa only [d8125, d2759, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42853 (p : Pattern) (guard : d8089 p = 1) : d2677 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35298 p hg
    simpa only [d8089, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42854 (p : Pattern) (guard : d8094 p = 1) : d2677 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42853 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42855 (p : Pattern) (guard : d8100 p = 1) : d2686 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42854 p hg
    simpa only [d8100, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8100, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42856 (p : Pattern) (guard : d8106 p = 1) : d2746 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2746, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42855 p hg
    simpa only [d8106, d2746, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2746, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42792 p hg
    simpa only [d8106, d2746, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42857 (p : Pattern) (guard : d5854 p = 1) : d2702 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2702, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39300 p hg
    simpa only [d5854, d2702, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2702, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2702, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42858 (p : Pattern) (guard : d8099 p = 1) : d2702 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42857 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21884 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42859 (p : Pattern) (guard : d8105 p = 1) : d2725 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2725, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42858 p hg
    simpa only [d8105, d2725, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2725, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22741 p hg
    simpa only [d8105, d2725, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42860 (p : Pattern) (guard : d8111 p = 1) : d2753 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2753, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42859 p hg
    simpa only [d8111, d2753, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2753, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42824 p hg
    simpa only [d8111, d2753, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42861 (p : Pattern) (guard : d8112 p = 1) : d2760 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2760, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42856 p hg
    simpa only [d8112, d2760, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2760, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42860 p hg
    simpa only [d8112, d2760, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42862 (p : Pattern) (guard : d5854 p = 1) : d2689 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2689, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35305 p hg
    simpa only [d5854, d2689, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2689, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2689, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42863 (p : Pattern) (guard : d8099 p = 1) : d2689 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42862 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21849 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42864 (p : Pattern) (guard : d8105 p = 1) : d2692 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2692, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42863 p hg
    simpa only [d8105, d2692, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2692, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22716 p hg
    simpa only [d8105, d2692, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42865 (p : Pattern) (guard : d8111 p = 1) : d2748 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2748, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42864 p hg
    simpa only [d8111, d2748, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2748, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42796 p hg
    simpa only [d8111, d2748, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42866 (p : Pattern) (guard : d8117 p = 1) : d2761 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2761, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42865 p hg
    simpa only [d8117, d2761, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2761, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d8117, d2761, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42867 (p : Pattern) (guard : d8118 p = 1) : d2762 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2762, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42861 p hg
    simpa only [d8118, d2762, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2762, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42866 p hg
    simpa only [d8118, d2762, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42868 (p : Pattern) (guard : d8124 p = 1) : d2765 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2765, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42867 p hg
    simpa only [d8124, d2765, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2765, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42831 p hg
    simpa only [d8124, d2765, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42869 (p : Pattern) (guard : d8130 p = 1) : d2769 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2769, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42868 p hg
    simpa only [d8130, d2769, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2769, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42835 p hg
    simpa only [d8130, d2769, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42870 (p : Pattern) (guard : d8131 p = 1) : d2770 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2770, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42852 p hg
    simpa only [d8131, d2770, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2770, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42869 p hg
    simpa only [d8131, d2770, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42871 (p : Pattern) (guard : d8118 p = 1) : d2772 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2772, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42703 p hg
    simpa only [d8118, d2772, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2772, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2772, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42872 (p : Pattern) (guard : d8124 p = 1) : d2773 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2773, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42871 p hg
    simpa only [d8124, d2773, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2773, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2773, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42873 (p : Pattern) (guard : d8130 p = 1) : d2774 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2774, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42872 p hg
    simpa only [d8130, d2774, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2774, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d2774, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42874 (p : Pattern) (guard : d8136 p = 1) : d2775 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2775, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42873 p hg
    simpa only [d8136, d2775, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2775, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d8136, d2775, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42875 (p : Pattern) (guard : d8137 p = 1) : d2776 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2776, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42870 p hg
    simpa only [d8137, d2776, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2776, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42874 p hg
    simpa only [d8137, d2776, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42876 (p : Pattern) (guard : d8138 p = 1) : d2777 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2777, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42838 p hg
    simpa only [d8138, d2777, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2777, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42875 p hg
    simpa only [d8138, d2777, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42877 (p : Pattern) (guard : d8099 p = 1) : d2683 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8099, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21836 p hg
    simpa only [d8099, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42878 (p : Pattern) (guard : d8105 p = 1) : d2684 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42877 p hg
    simpa only [d8105, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42879 (p : Pattern) (guard : d8106 p = 1) : d2687 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2687, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42855 p hg
    simpa only [d8106, d2687, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2687, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42878 p hg
    simpa only [d8106, d2687, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42880 (p : Pattern) (guard : d8107 p = 1) : d2687 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42676 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42879 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42881 (p : Pattern) (guard : d8106 p = 1) : d2687 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2687, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42819 p hg
    simpa only [d8106, d2687, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2687, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42878 p hg
    simpa only [d8106, d2687, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42882 (p : Pattern) (guard : d0 p = 1) : d2695 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42883 (p : Pattern) (guard : d8111 p = 1) : d2696 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2696, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42864 p hg
    simpa only [d8111, d2696, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2696, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42882 p hg
    simpa only [d8111, d2696, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42884 (p : Pattern) (guard : d8112 p = 1) : d2697 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2697, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42881 p hg
    simpa only [d8112, d2697, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2697, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42883 p hg
    simpa only [d8112, d2697, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42885 (p : Pattern) (guard : d8113 p = 1) : d2778 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2778, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42880 p hg
    simpa only [d8113, d2778, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2778, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42884 p hg
    simpa only [d8113, d2778, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42886 (p : Pattern) (guard : d8106 p = 1) : d2687 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2687, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42776 p hg
    simpa only [d8106, d2687, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2687, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42878 p hg
    simpa only [d8106, d2687, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42887 (p : Pattern) (guard : d8111 p = 1) : d2696 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42728 p hg
    simpa only [d8111, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42882 p hg
    simpa only [d8111, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42888 (p : Pattern) (guard : d8112 p = 1) : d2697 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2697, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42886 p hg
    simpa only [d8112, d2697, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2697, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42887 p hg
    simpa only [d8112, d2697, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42889 (p : Pattern) (guard : d8118 p = 1) : d2700 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2700, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42888 p hg
    simpa only [d8118, d2700, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2700, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42802 p hg
    simpa only [d8118, d2700, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42890 (p : Pattern) (guard : d8119 p = 1) : d2779 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2779, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42885 p hg
    simpa only [d8119, d2779, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2779, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42889 p hg
    simpa only [d8119, d2779, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42891 (p : Pattern) (guard : d8106 p = 1) : d2706 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2706, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42718 p hg
    simpa only [d8106, d2706, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2706, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42807 p hg
    simpa only [d8106, d2706, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42892 (p : Pattern) (guard : d8099 p = 1) : d2677 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21845 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42893 (p : Pattern) (guard : d8105 p = 1) : d2686 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42892 p hg
    simpa only [d8105, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22712 p hg
    simpa only [d8105, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42894 (p : Pattern) (guard : d8111 p = 1) : d2711 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42893 p hg
    simpa only [d8111, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42811 p hg
    simpa only [d8111, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42895 (p : Pattern) (guard : d8112 p = 1) : d2712 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2712, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42891 p hg
    simpa only [d8112, d2712, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2712, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d8112, d2712, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42896 (p : Pattern) (guard : d8111 p = 1) : d2713 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42893 p hg
    simpa only [d8111, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42897 (p : Pattern) (guard : d0 p = 1) : d2714 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42898 (p : Pattern) (guard : d8117 p = 1) : d2715 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d8117, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d8117, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42899 (p : Pattern) (guard : d8118 p = 1) : d2716 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2716, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d8118, d2716, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2716, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d8118, d2716, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42900 (p : Pattern) (guard : d0 p = 1) : d2717 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42901 (p : Pattern) (guard : d8123 p = 1) : d2718 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d8123, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d8123, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42902 (p : Pattern) (guard : d8124 p = 1) : d2719 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2719, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d8124, d2719, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2719, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d8124, d2719, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42903 (p : Pattern) (guard : d8125 p = 1) : d2780 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2780, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42890 p hg
    simpa only [d8125, d2780, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2780, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42902 p hg
    simpa only [d8125, d2780, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42904 (p : Pattern) (guard : d8089 p = 1) : d2677 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35325 p hg
    simpa only [d8089, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42905 (p : Pattern) (guard : d8094 p = 1) : d2677 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42906 (p : Pattern) (guard : d8100 p = 1) : d2686 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42905 p hg
    simpa only [d8100, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8100, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42907 (p : Pattern) (guard : d8106 p = 1) : d2687 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2687, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d8106, d2687, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2687, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42878 p hg
    simpa only [d8106, d2687, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42908 (p : Pattern) (guard : d5854 p = 1) : d2702 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2702, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35331 p hg
    simpa only [d5854, d2702, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2702, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2702, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42909 (p : Pattern) (guard : d8099 p = 1) : d2702 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42908 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21884 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42910 (p : Pattern) (guard : d8105 p = 1) : d2725 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2725, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42909 p hg
    simpa only [d8105, d2725, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2725, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22741 p hg
    simpa only [d8105, d2725, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42911 (p : Pattern) (guard : d0 p = 1) : d2728 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42912 (p : Pattern) (guard : d8111 p = 1) : d2729 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2729, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42910 p hg
    simpa only [d8111, d2729, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2729, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42911 p hg
    simpa only [d8111, d2729, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42913 (p : Pattern) (guard : d8112 p = 1) : d2781 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2781, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42907 p hg
    simpa only [d8112, d2781, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2781, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d8112, d2781, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42914 (p : Pattern) (guard : d5854 p = 1) : d2689 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2689, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35338 p hg
    simpa only [d5854, d2689, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2689, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2689, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42915 (p : Pattern) (guard : d8099 p = 1) : d2689 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42914 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21849 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42916 (p : Pattern) (guard : d8105 p = 1) : d2692 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2692, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42915 p hg
    simpa only [d8105, d2692, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2692, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22716 p hg
    simpa only [d8105, d2692, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42917 (p : Pattern) (guard : d8111 p = 1) : d2696 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2696, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d8111, d2696, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2696, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42882 p hg
    simpa only [d8111, d2696, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42918 (p : Pattern) (guard : d8117 p = 1) : d2731 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2731, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42917 p hg
    simpa only [d8117, d2731, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2731, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d8117, d2731, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42919 (p : Pattern) (guard : d8118 p = 1) : d2782 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2782, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42913 p hg
    simpa only [d8118, d2782, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2782, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42918 p hg
    simpa only [d8118, d2782, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42920 (p : Pattern) (guard : d8117 p = 1) : d2733 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2733, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42883 p hg
    simpa only [d8117, d2733, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2733, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42829 p hg
    simpa only [d8117, d2733, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42921 (p : Pattern) (guard : d8123 p = 1) : d2734 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2734, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42920 p hg
    simpa only [d8123, d2734, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2734, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2734, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42922 (p : Pattern) (guard : d8124 p = 1) : d2783 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2783, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42919 p hg
    simpa only [d8124, d2783, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2783, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42921 p hg
    simpa only [d8124, d2783, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42923 (p : Pattern) (guard : d0 p = 1) : d2736 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42924 (p : Pattern) (guard : d8117 p = 1) : d2737 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d8117, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42923 p hg
    simpa only [d8117, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42925 (p : Pattern) (guard : d0 p = 1) : d2738 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42926 (p : Pattern) (guard : d8123 p = 1) : d2739 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42924 p hg
    simpa only [d8123, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42925 p hg
    simpa only [d8123, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42927 (p : Pattern) (guard : d0 p = 1) : d2741 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42928 (p : Pattern) (guard : d8129 p = 1) : d2742 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42926 p hg
    simpa only [d8129, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42927 p hg
    simpa only [d8129, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42929 (p : Pattern) (guard : d8130 p = 1) : d2784 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2784, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42922 p hg
    simpa only [d8130, d2784, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2784, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42928 p hg
    simpa only [d8130, d2784, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42930 (p : Pattern) (guard : d8131 p = 1) : d2785 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2785, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42903 p hg
    simpa only [d8131, d2785, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2785, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d8131, d2785, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42931 (p : Pattern) (guard : d0 p = 1) : d2745 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42932 (p : Pattern) (guard : d8111 p = 1) : d2746 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42893 p hg
    simpa only [d8111, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42931 p hg
    simpa only [d8111, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42933 (p : Pattern) (guard : d8112 p = 1) : d2746 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42793 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42932 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42934 (p : Pattern) (guard : d0 p = 1) : d2748 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42935 (p : Pattern) (guard : d8117 p = 1) : d2749 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42932 p hg
    simpa only [d8117, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42934 p hg
    simpa only [d8117, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42936 (p : Pattern) (guard : d8118 p = 1) : d2750 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2750, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42933 p hg
    simpa only [d8118, d2750, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2750, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42935 p hg
    simpa only [d8118, d2750, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42937 (p : Pattern) (guard : d0 p = 1) : d2699 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42938 (p : Pattern) (guard : d8123 p = 1) : d2751 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42935 p hg
    simpa only [d8123, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42937 p hg
    simpa only [d8123, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42939 (p : Pattern) (guard : d8124 p = 1) : d2752 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2752, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42936 p hg
    simpa only [d8124, d2752, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2752, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42938 p hg
    simpa only [d8124, d2752, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42940 (p : Pattern) (guard : d8111 p = 1) : d2753 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42779 p hg
    simpa only [d8111, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42824 p hg
    simpa only [d8111, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42941 (p : Pattern) (guard : d0 p = 1) : d2755 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42942 (p : Pattern) (guard : d8117 p = 1) : d2756 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42940 p hg
    simpa only [d8117, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42941 p hg
    simpa only [d8117, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42943 (p : Pattern) (guard : d8123 p = 1) : d2757 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42942 p hg
    simpa only [d8123, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42944 (p : Pattern) (guard : d8129 p = 1) : d2758 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42943 p hg
    simpa only [d8129, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42945 (p : Pattern) (guard : d8130 p = 1) : d2759 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2759, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42939 p hg
    simpa only [d8130, d2759, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2759, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42944 p hg
    simpa only [d8130, d2759, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42946 (p : Pattern) (guard : d5854 p = 1) : d2677 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2677, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35366 p hg
    simpa only [d5854, d2677, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2677, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2677, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42947 (p : Pattern) (guard : d8099 p = 1) : d2677 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42946 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21845 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42948 (p : Pattern) (guard : d8105 p = 1) : d2686 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2686, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42947 p hg
    simpa only [d8105, d2686, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2686, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22712 p hg
    simpa only [d8105, d2686, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42949 (p : Pattern) (guard : d8111 p = 1) : d2746 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2746, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42948 p hg
    simpa only [d8111, d2746, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2746, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42931 p hg
    simpa only [d8111, d2746, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42950 (p : Pattern) (guard : d0 p = 1) : d2753 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42951 (p : Pattern) (guard : d8117 p = 1) : d2760 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2760, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42949 p hg
    simpa only [d8117, d2760, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2760, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42950 p hg
    simpa only [d8117, d2760, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42952 (p : Pattern) (guard : d0 p = 1) : d2761 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42953 (p : Pattern) (guard : d8123 p = 1) : d2762 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2762, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d8123, d2762, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2762, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d8123, d2762, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42954 (p : Pattern) (guard : d0 p = 1) : d2764 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42955 (p : Pattern) (guard : d8129 p = 1) : d2765 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2765, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d8129, d2765, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2765, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d8129, d2765, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42956 (p : Pattern) (guard : d0 p = 1) : d2768 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42957 (p : Pattern) (guard : d8135 p = 1) : d2769 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2769, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d8135, d2769, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2769, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d8135, d2769, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42958 (p : Pattern) (guard : d8136 p = 1) : d2770 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2770, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42945 p hg
    simpa only [d8136, d2770, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2770, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42957 p hg
    simpa only [d8136, d2770, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42959 (p : Pattern) (guard : d8137 p = 1) : d2786 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2786, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42930 p hg
    simpa only [d8137, d2786, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2786, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42958 p hg
    simpa only [d8137, d2786, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42960 (p : Pattern) (guard : d8112 p = 1) : d2746 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42820 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42949 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42961 (p : Pattern) (guard : d8118 p = 1) : d2750 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2750, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42960 p hg
    simpa only [d8118, d2750, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2750, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42935 p hg
    simpa only [d8118, d2750, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42962 (p : Pattern) (guard : d8124 p = 1) : d2752 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2752, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d8124, d2752, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2752, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42938 p hg
    simpa only [d8124, d2752, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42963 (p : Pattern) (guard : d8130 p = 1) : d2759 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2759, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42962 p hg
    simpa only [d8130, d2759, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2759, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42944 p hg
    simpa only [d8130, d2759, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42964 (p : Pattern) (guard : d5854 p = 1) : d2677 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2677, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35733 p hg
    simpa only [d5854, d2677, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2677, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2677, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42965 (p : Pattern) (guard : d8099 p = 1) : d2677 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42964 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21845 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42966 (p : Pattern) (guard : d8105 p = 1) : d2686 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2686, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42965 p hg
    simpa only [d8105, d2686, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2686, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22712 p hg
    simpa only [d8105, d2686, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42967 (p : Pattern) (guard : d8111 p = 1) : d2746 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2746, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42966 p hg
    simpa only [d8111, d2746, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2746, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42931 p hg
    simpa only [d8111, d2746, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42968 (p : Pattern) (guard : d8117 p = 1) : d2760 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2760, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d8117, d2760, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2760, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42950 p hg
    simpa only [d8117, d2760, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42969 (p : Pattern) (guard : d8123 p = 1) : d2762 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2762, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42968 p hg
    simpa only [d8123, d2762, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2762, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d8123, d2762, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42970 (p : Pattern) (guard : d8129 p = 1) : d2765 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2765, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42969 p hg
    simpa only [d8129, d2765, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2765, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d8129, d2765, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42971 (p : Pattern) (guard : d8135 p = 1) : d2769 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2769, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42970 p hg
    simpa only [d8135, d2769, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2769, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d8135, d2769, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42972 (p : Pattern) (guard : d8136 p = 1) : d2770 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2770, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42963 p hg
    simpa only [d8136, d2770, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2770, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d8136, d2770, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42973 (p : Pattern) (guard : d8142 p = 1) : d2787 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2787, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42972 p hg
    simpa only [d8142, d2787, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2787, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d2787, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42974 (p : Pattern) (guard : d8143 p = 1) : d2788 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2788, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d8143, d2788, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2788, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42973 p hg
    simpa only [d8143, d2788, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42975 (p : Pattern) (guard : d8144 p = 1) : d2789 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d2789, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42876 p hg
    simpa only [d8144, d2789, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d2789, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42974 p hg
    simpa only [d8144, d2789, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42976 (p : Pattern) (guard : d8145 p = 1) : d2790 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d2790, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42652 p hg
    simpa only [d8145, d2790, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d2790, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42975 p hg
    simpa only [d8145, d2790, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42977 (p : Pattern) (guard : d8146 p = 1) : d2791 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d8146, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42976 p hg
    simpa only [d8146, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42978 (p : Pattern) (guard : d8086 p = 1) : d2654 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2654, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42249 p hg
    simpa only [d8086, d2654, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2654, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d8086, d2654, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42979 (p : Pattern) (guard : d8090 p = 1) : d2507 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2507, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42237 p hg
    simpa only [d8090, d2507, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2507, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41853 p hg
    simpa only [d8090, d2507, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
