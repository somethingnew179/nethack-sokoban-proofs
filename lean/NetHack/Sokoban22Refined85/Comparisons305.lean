/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons304
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42700 (p : Pattern) (guard : d8100 p = 1) : d2692 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2692, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42699 p hg
    simpa only [d8100, d2692, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2692, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42687 p hg
    simpa only [d8100, d2692, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42701 (p : Pattern) (guard : d8106 p = 1) : d2696 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2696, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42700 p hg
    simpa only [d8106, d2696, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2696, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42690 p hg
    simpa only [d8106, d2696, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42702 (p : Pattern) (guard : d8107 p = 1) : d2697 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2697, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42697 p hg
    simpa only [d8107, d2697, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2697, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42701 p hg
    simpa only [d8107, d2697, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42703 (p : Pattern) (guard : d8112 p = 1) : d2699 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2699, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42551 p hg
    simpa only [d8112, d2699, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2699, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2699, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42704 (p : Pattern) (guard : d8113 p = 1) : d2700 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2700, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42702 p hg
    simpa only [d8113, d2700, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2700, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42703 p hg
    simpa only [d8113, d2700, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42705 (p : Pattern) (guard : d8114 p = 1) : d2701 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2701, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42693 p hg
    simpa only [d8114, d2701, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2701, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42704 p hg
    simpa only [d8114, d2701, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42706 (p : Pattern) (guard : d8085 p = 1) : d2677 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35161 p hg
    simpa only [d8085, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2677, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42707 (p : Pattern) (guard : d8090 p = 1) : d2677 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42706 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42669 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42708 (p : Pattern) (guard : d8095 p = 1) : d2686 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42707 p hg
    simpa only [d8095, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42671 p hg
    simpa only [d8095, d2686, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42709 (p : Pattern) (guard : d8089 p = 1) : d2702 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35166 p hg
    simpa only [d8089, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42710 (p : Pattern) (guard : d5854 p = 1) : d2703 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39177 p hg
    simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42711 (p : Pattern) (guard : d8094 p = 1) : d2704 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42709 p hg
    simpa only [d8094, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42710 p hg
    simpa only [d8094, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42712 (p : Pattern) (guard : d8100 p = 1) : d2705 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42711 p hg
    simpa only [d8100, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42713 (p : Pattern) (guard : d8101 p = 1) : d2706 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2706, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42708 p hg
    simpa only [d8101, d2706, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2706, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42712 p hg
    simpa only [d8101, d2706, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42714 (p : Pattern) (guard : d8089 p = 1) : d2677 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2677, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35175 p hg
    simpa only [d8089, d2677, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2677, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2677, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42715 (p : Pattern) (guard : d5854 p = 1) : d2677 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42716 (p : Pattern) (guard : d8094 p = 1) : d2677 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42714 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42717 (p : Pattern) (guard : d8099 p = 1) : d2680 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8099, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21833 p hg
    simpa only [d8099, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42718 (p : Pattern) (guard : d8100 p = 1) : d2686 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2686, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42716 p hg
    simpa only [d8100, d2686, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2686, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8100, d2686, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42719 (p : Pattern) (guard : d5854 p = 1) : d2707 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35181 p hg
    simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42720 (p : Pattern) (guard : d8099 p = 1) : d2709 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42719 p hg
    simpa only [d8099, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21867 p hg
    simpa only [d8099, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42721 (p : Pattern) (guard : d8105 p = 1) : d2710 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42720 p hg
    simpa only [d8105, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42722 (p : Pattern) (guard : d8106 p = 1) : d2711 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2711, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42718 p hg
    simpa only [d8106, d2711, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2711, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42721 p hg
    simpa only [d8106, d2711, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42723 (p : Pattern) (guard : d8107 p = 1) : d2712 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2712, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42713 p hg
    simpa only [d8107, d2712, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2712, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42722 p hg
    simpa only [d8107, d2712, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42724 (p : Pattern) (guard : d8094 p = 1) : d2677 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42667 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42725 (p : Pattern) (guard : d8100 p = 1) : d2686 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2686, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42724 p hg
    simpa only [d8100, d2686, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2686, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8100, d2686, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42726 (p : Pattern) (guard : d8106 p = 1) : d2713 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2713, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42725 p hg
    simpa only [d8106, d2713, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2713, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2713, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42727 (p : Pattern) (guard : d8099 p = 1) : d2689 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42685 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21849 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42728 (p : Pattern) (guard : d8105 p = 1) : d2692 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42727 p hg
    simpa only [d8105, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22716 p hg
    simpa only [d8105, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42729 (p : Pattern) (guard : d8111 p = 1) : d2714 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42728 p hg
    simpa only [d8111, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42730 (p : Pattern) (guard : d8112 p = 1) : d2715 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2715, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42726 p hg
    simpa only [d8112, d2715, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2715, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42729 p hg
    simpa only [d8112, d2715, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42731 (p : Pattern) (guard : d8113 p = 1) : d2716 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2716, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42723 p hg
    simpa only [d8113, d2716, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2716, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42730 p hg
    simpa only [d8113, d2716, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42732 (p : Pattern) (guard : d8094 p = 1) : d2677 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42669 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42733 (p : Pattern) (guard : d8100 p = 1) : d2686 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42732 p hg
    simpa only [d8100, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8100, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42734 (p : Pattern) (guard : d8106 p = 1) : d2713 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42733 p hg
    simpa only [d8106, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42735 (p : Pattern) (guard : d8112 p = 1) : d2715 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42734 p hg
    simpa only [d8112, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42729 p hg
    simpa only [d8112, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42736 (p : Pattern) (guard : d8117 p = 1) : d2717 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42173 p hg
    simpa only [d8117, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42737 (p : Pattern) (guard : d8118 p = 1) : d2718 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42735 p hg
    simpa only [d8118, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42736 p hg
    simpa only [d8118, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42738 (p : Pattern) (guard : d8119 p = 1) : d2719 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2719, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42731 p hg
    simpa only [d8119, d2719, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2719, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42737 p hg
    simpa only [d8119, d2719, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42739 (p : Pattern) (guard : d8120 p = 1) : d2720 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2720, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42705 p hg
    simpa only [d8120, d2720, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2720, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42738 p hg
    simpa only [d8120, d2720, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42740 (p : Pattern) (guard : d8084 p = 1) : d327 p ≤ (0 : Int) + d327 p := by
  omega
theorem compare42741 (p : Pattern) (guard : d8085 p = 1) : d2721 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2721, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35201 p hg
    simpa only [d8085, d2721, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2721, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42740 p hg
    simpa only [d8085, d2721, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42742 (p : Pattern) (guard : d8090 p = 1) : d2722 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2722, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42741 p hg
    simpa only [d8090, d2722, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2722, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42714 p hg
    simpa only [d8090, d2722, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42743 (p : Pattern) (guard : d8094 p = 1) : d2680 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2680, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42667 p hg
    simpa only [d8094, d2680, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2680, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42670 p hg
    simpa only [d8094, d2680, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42744 (p : Pattern) (guard : d8095 p = 1) : d2723 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2723, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42742 p hg
    simpa only [d8095, d2723, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2723, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42743 p hg
    simpa only [d8095, d2723, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42745 (p : Pattern) (guard : d8094 p = 1) : d2683 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2683, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42714 p hg
    simpa only [d8094, d2683, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2683, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42673 p hg
    simpa only [d8094, d2683, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42746 (p : Pattern) (guard : d8100 p = 1) : d2684 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2684, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42745 p hg
    simpa only [d8100, d2684, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2684, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2684, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42747 (p : Pattern) (guard : d8101 p = 1) : d2724 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2724, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42744 p hg
    simpa only [d8101, d2724, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2724, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42746 p hg
    simpa only [d8101, d2724, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42748 (p : Pattern) (guard : d8089 p = 1) : d2702 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2702, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35209 p hg
    simpa only [d8089, d2702, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2702, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2702, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42749 (p : Pattern) (guard : d5854 p = 1) : d2702 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42750 (p : Pattern) (guard : d8094 p = 1) : d2702 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42748 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42749 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42751 (p : Pattern) (guard : d8099 p = 1) : d2704 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42749 p hg
    simpa only [d8099, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21863 p hg
    simpa only [d8099, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42752 (p : Pattern) (guard : d8100 p = 1) : d2725 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2725, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42750 p hg
    simpa only [d8100, d2725, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2725, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42751 p hg
    simpa only [d8100, d2725, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42753 (p : Pattern) (guard : d8099 p = 1) : d2727 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42749 p hg
    simpa only [d8099, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21887 p hg
    simpa only [d8099, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42754 (p : Pattern) (guard : d8105 p = 1) : d2728 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42753 p hg
    simpa only [d8105, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42755 (p : Pattern) (guard : d8106 p = 1) : d2729 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2729, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42752 p hg
    simpa only [d8106, d2729, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2729, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42754 p hg
    simpa only [d8106, d2729, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42756 (p : Pattern) (guard : d8107 p = 1) : d2730 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2730, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42747 p hg
    simpa only [d8107, d2730, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2730, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42755 p hg
    simpa only [d8107, d2730, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42757 (p : Pattern) (guard : d8089 p = 1) : d2689 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2689, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35218 p hg
    simpa only [d8089, d2689, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2689, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2689, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42758 (p : Pattern) (guard : d8094 p = 1) : d2689 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42757 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42685 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42759 (p : Pattern) (guard : d8100 p = 1) : d2692 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2692, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42758 p hg
    simpa only [d8100, d2692, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2692, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42687 p hg
    simpa only [d8100, d2692, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42760 (p : Pattern) (guard : d8106 p = 1) : d2696 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2696, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42759 p hg
    simpa only [d8106, d2696, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2696, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42690 p hg
    simpa only [d8106, d2696, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42761 (p : Pattern) (guard : d5854 p = 1) : d2577 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19998 p hg
    simpa only [d5854, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2577, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42762 (p : Pattern) (guard : d8099 p = 1) : d2577 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42761 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21718 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42763 (p : Pattern) (guard : d8105 p = 1) : d2579 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42762 p hg
    simpa only [d8105, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22604 p hg
    simpa only [d8105, d2579, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42764 (p : Pattern) (guard : d8111 p = 1) : d2581 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42763 p hg
    simpa only [d8111, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42218 p hg
    simpa only [d8111, d2581, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42765 (p : Pattern) (guard : d8112 p = 1) : d2731 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2731, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42760 p hg
    simpa only [d8112, d2731, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2731, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42764 p hg
    simpa only [d8112, d2731, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42766 (p : Pattern) (guard : d8113 p = 1) : d2732 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2732, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42756 p hg
    simpa only [d8113, d2732, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2732, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42765 p hg
    simpa only [d8113, d2732, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42767 (p : Pattern) (guard : d5854 p = 1) : d2551 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19941 p hg
    simpa only [d5854, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2551, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42768 (p : Pattern) (guard : d8099 p = 1) : d2551 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42767 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42769 (p : Pattern) (guard : d8105 p = 1) : d2583 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42768 p hg
    simpa only [d8105, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22609 p hg
    simpa only [d8105, d2583, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42770 (p : Pattern) (guard : d8111 p = 1) : d2584 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42769 p hg
    simpa only [d8111, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42221 p hg
    simpa only [d8111, d2584, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42771 (p : Pattern) (guard : d8112 p = 1) : d2733 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2733, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42691 p hg
    simpa only [d8112, d2733, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2733, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42770 p hg
    simpa only [d8112, d2733, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42772 (p : Pattern) (guard : d8118 p = 1) : d2734 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2734, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42771 p hg
    simpa only [d8118, d2734, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2734, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2734, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42773 (p : Pattern) (guard : d8119 p = 1) : d2735 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2735, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42766 p hg
    simpa only [d8119, d2735, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2735, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42772 p hg
    simpa only [d8119, d2735, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42774 (p : Pattern) (guard : d8089 p = 1) : d2677 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35236 p hg
    simpa only [d8089, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42775 (p : Pattern) (guard : d8094 p = 1) : d2677 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42774 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42776 (p : Pattern) (guard : d8100 p = 1) : d2686 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2686, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42775 p hg
    simpa only [d8100, d2686, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2686, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8100, d2686, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42777 (p : Pattern) (guard : d8106 p = 1) : d2711 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2711, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42776 p hg
    simpa only [d8106, d2711, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2711, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42721 p hg
    simpa only [d8106, d2711, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42778 (p : Pattern) (guard : d8099 p = 1) : d2702 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42749 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21884 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42779 (p : Pattern) (guard : d8105 p = 1) : d2725 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42778 p hg
    simpa only [d8105, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22741 p hg
    simpa only [d8105, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42780 (p : Pattern) (guard : d8111 p = 1) : d2736 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42779 p hg
    simpa only [d8111, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42781 (p : Pattern) (guard : d8112 p = 1) : d2737 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2737, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42777 p hg
    simpa only [d8112, d2737, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2737, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42780 p hg
    simpa only [d8112, d2737, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42782 (p : Pattern) (guard : d8117 p = 1) : d2738 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42729 p hg
    simpa only [d8117, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42443 p hg
    simpa only [d8117, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42783 (p : Pattern) (guard : d8118 p = 1) : d2739 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2739, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42781 p hg
    simpa only [d8118, d2739, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2739, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42782 p hg
    simpa only [d8118, d2739, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42784 (p : Pattern) (guard : d0 p = 1) : d2594 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42785 (p : Pattern) (guard : d8117 p = 1) : d2740 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42729 p hg
    simpa only [d8117, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42784 p hg
    simpa only [d8117, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42786 (p : Pattern) (guard : d8123 p = 1) : d2741 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42785 p hg
    simpa only [d8123, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42787 (p : Pattern) (guard : d8124 p = 1) : d2742 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2742, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42783 p hg
    simpa only [d8124, d2742, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2742, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42786 p hg
    simpa only [d8124, d2742, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42788 (p : Pattern) (guard : d8125 p = 1) : d2743 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2743, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42773 p hg
    simpa only [d8125, d2743, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2743, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42787 p hg
    simpa only [d8125, d2743, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42789 (p : Pattern) (guard : d8126 p = 1) : d2744 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2744, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42739 p hg
    simpa only [d8126, d2744, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2744, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42788 p hg
    simpa only [d8126, d2744, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42790 (p : Pattern) (guard : d8100 p = 1) : d2745 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42671 p hg
    simpa only [d8100, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42791 (p : Pattern) (guard : d8101 p = 1) : d2746 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42696 p hg
    simpa only [d8101, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42790 p hg
    simpa only [d8101, d2746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42792 (p : Pattern) (guard : d8105 p = 1) : d2745 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8105, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42793 (p : Pattern) (guard : d8106 p = 1) : d2746 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2746, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42776 p hg
    simpa only [d8106, d2746, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2746, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42792 p hg
    simpa only [d8106, d2746, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42794 (p : Pattern) (guard : d8107 p = 1) : d2746 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42791 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42793 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42795 (p : Pattern) (guard : d8106 p = 1) : d2746 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2746, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42718 p hg
    simpa only [d8106, d2746, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2746, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42792 p hg
    simpa only [d8106, d2746, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42796 (p : Pattern) (guard : d0 p = 1) : d2747 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42797 (p : Pattern) (guard : d8111 p = 1) : d2748 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42728 p hg
    simpa only [d8111, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42796 p hg
    simpa only [d8111, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42798 (p : Pattern) (guard : d8112 p = 1) : d2749 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2749, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42795 p hg
    simpa only [d8112, d2749, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2749, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42797 p hg
    simpa only [d8112, d2749, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42799 (p : Pattern) (guard : d8113 p = 1) : d2750 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2750, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42794 p hg
    simpa only [d8113, d2750, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2750, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42798 p hg
    simpa only [d8113, d2750, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42800 (p : Pattern) (guard : d8106 p = 1) : d2746 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2746, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42725 p hg
    simpa only [d8106, d2746, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2746, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42792 p hg
    simpa only [d8106, d2746, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42801 (p : Pattern) (guard : d8112 p = 1) : d2749 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2749, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42800 p hg
    simpa only [d8112, d2749, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2749, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42797 p hg
    simpa only [d8112, d2749, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42802 (p : Pattern) (guard : d8117 p = 1) : d2699 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42219 p hg
    simpa only [d8117, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42803 (p : Pattern) (guard : d8118 p = 1) : d2751 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2751, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42801 p hg
    simpa only [d8118, d2751, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2751, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42802 p hg
    simpa only [d8118, d2751, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42804 (p : Pattern) (guard : d8119 p = 1) : d2752 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2752, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42799 p hg
    simpa only [d8119, d2752, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2752, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42803 p hg
    simpa only [d8119, d2752, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42805 (p : Pattern) (guard : d8094 p = 1) : d2702 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42709 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42749 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42806 (p : Pattern) (guard : d8100 p = 1) : d2725 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42805 p hg
    simpa only [d8100, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42751 p hg
    simpa only [d8100, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42807 (p : Pattern) (guard : d8105 p = 1) : d2705 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42751 p hg
    simpa only [d8105, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42808 (p : Pattern) (guard : d8106 p = 1) : d2753 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42806 p hg
    simpa only [d8106, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42807 p hg
    simpa only [d8106, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42809 (p : Pattern) (guard : d8099 p = 1) : d2707 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42719 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21915 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42810 (p : Pattern) (guard : d8105 p = 1) : d2754 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42809 p hg
    simpa only [d8105, d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22774 p hg
    simpa only [d8105, d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42811 (p : Pattern) (guard : d0 p = 1) : d2710 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42812 (p : Pattern) (guard : d8111 p = 1) : d2755 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42810 p hg
    simpa only [d8111, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42811 p hg
    simpa only [d8111, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42813 (p : Pattern) (guard : d8112 p = 1) : d2756 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42808 p hg
    simpa only [d8112, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42812 p hg
    simpa only [d8112, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42814 (p : Pattern) (guard : d8118 p = 1) : d2757 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42813 p hg
    simpa only [d8118, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42815 (p : Pattern) (guard : d8124 p = 1) : d2758 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42814 p hg
    simpa only [d8124, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42816 (p : Pattern) (guard : d8125 p = 1) : d2759 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2759, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42804 p hg
    simpa only [d8125, d2759, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2759, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42815 p hg
    simpa only [d8125, d2759, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42817 (p : Pattern) (guard : d8089 p = 1) : d2677 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35272 p hg
    simpa only [d8089, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42818 (p : Pattern) (guard : d8094 p = 1) : d2677 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42817 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42819 (p : Pattern) (guard : d8100 p = 1) : d2686 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2686, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42818 p hg
    simpa only [d8100, d2686, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2686, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d8100, d2686, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42820 (p : Pattern) (guard : d8106 p = 1) : d2746 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2746, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42819 p hg
    simpa only [d8106, d2746, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2746, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42792 p hg
    simpa only [d8106, d2746, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42821 (p : Pattern) (guard : d5854 p = 1) : d2702 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2702, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35279 p hg
    simpa only [d5854, d2702, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2702, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2702, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42822 (p : Pattern) (guard : d8099 p = 1) : d2702 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42821 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21884 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42823 (p : Pattern) (guard : d8105 p = 1) : d2725 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2725, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42822 p hg
    simpa only [d8105, d2725, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2725, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22741 p hg
    simpa only [d8105, d2725, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42824 (p : Pattern) (guard : d0 p = 1) : d2705 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42825 (p : Pattern) (guard : d8111 p = 1) : d2753 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2753, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42823 p hg
    simpa only [d8111, d2753, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2753, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42824 p hg
    simpa only [d8111, d2753, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42826 (p : Pattern) (guard : d8112 p = 1) : d2760 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2760, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42820 p hg
    simpa only [d8112, d2760, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2760, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42825 p hg
    simpa only [d8112, d2760, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42827 (p : Pattern) (guard : d8117 p = 1) : d2761 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42797 p hg
    simpa only [d8117, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d8117, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42828 (p : Pattern) (guard : d8118 p = 1) : d2762 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2762, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42826 p hg
    simpa only [d8118, d2762, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2762, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42827 p hg
    simpa only [d8118, d2762, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42829 (p : Pattern) (guard : d0 p = 1) : d2584 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42830 (p : Pattern) (guard : d8117 p = 1) : d2763 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42797 p hg
    simpa only [d8117, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42829 p hg
    simpa only [d8117, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42831 (p : Pattern) (guard : d8123 p = 1) : d2764 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42830 p hg
    simpa only [d8123, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42832 (p : Pattern) (guard : d8124 p = 1) : d2765 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2765, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42828 p hg
    simpa only [d8124, d2765, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2765, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42831 p hg
    simpa only [d8124, d2765, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42833 (p : Pattern) (guard : d8117 p = 1) : d2766 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42812 p hg
    simpa only [d8117, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42834 (p : Pattern) (guard : d8123 p = 1) : d2767 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42833 p hg
    simpa only [d8123, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42835 (p : Pattern) (guard : d8129 p = 1) : d2768 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42834 p hg
    simpa only [d8129, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42836 (p : Pattern) (guard : d8130 p = 1) : d2769 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2769, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42832 p hg
    simpa only [d8130, d2769, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2769, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42835 p hg
    simpa only [d8130, d2769, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42837 (p : Pattern) (guard : d8131 p = 1) : d2770 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2770, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42816 p hg
    simpa only [d8131, d2770, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2770, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42836 p hg
    simpa only [d8131, d2770, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42838 (p : Pattern) (guard : d8132 p = 1) : d2771 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2771, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42789 p hg
    simpa only [d8132, d2771, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2771, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42837 p hg
    simpa only [d8132, d2771, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42839 (p : Pattern) (guard : d8101 p = 1) : d2746 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2746, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42680 p hg
    simpa only [d8101, d2746, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2746, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42790 p hg
    simpa only [d8101, d2746, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
