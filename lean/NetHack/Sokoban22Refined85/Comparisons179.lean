/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons178
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25060 (p : Pattern) (guard : d5502 p = 1) : d2993 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2993, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d2993, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2993, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17390 p hg
    simpa only [d2993, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25061 (p : Pattern) (guard : d5502 p = 1) : d2994 p ≤ (0 : Int) + d2687 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2994, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25060 p hg
    simpa only [d2994, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2994, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25058 p hg
    simpa only [d2994, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25062 (p : Pattern) (guard : d5502 p = 1) : d2994 p ≤ (0 : Int) + d2688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25059 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25061 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25063 (p : Pattern) (guard : d5502 p = 1) : d2995 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2995, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d2995, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2995, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17588 p hg
    simpa only [d2995, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25064 (p : Pattern) (guard : d5502 p = 1) : d1884 p ≤ (0 : Int) + d2695 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1884, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17326 p hg
    simpa only [d1884, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1884, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1884, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25065 (p : Pattern) (guard : d5502 p = 1) : d2996 p ≤ (0 : Int) + d2696 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2996, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25063 p hg
    simpa only [d2996, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2996, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25064 p hg
    simpa only [d2996, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25066 (p : Pattern) (guard : d5502 p = 1) : d2997 p ≤ (0 : Int) + d2697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2997, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25061 p hg
    simpa only [d2997, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2997, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25065 p hg
    simpa only [d2997, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25067 (p : Pattern) (guard : d5502 p = 1) : d2998 p ≤ (0 : Int) + d2698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2998, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25062 p hg
    simpa only [d2998, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2998, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25066 p hg
    simpa only [d2998, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25068 (p : Pattern) (guard : d5502 p = 1) : d2999 p ≤ (0 : Int) + d2699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2999, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24956 p hg
    simpa only [d2999, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2999, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2999, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25069 (p : Pattern) (guard : d5502 p = 1) : d3000 p ≤ (0 : Int) + d2700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3000, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25066 p hg
    simpa only [d3000, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3000, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25068 p hg
    simpa only [d3000, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25070 (p : Pattern) (guard : d5502 p = 1) : d3001 p ≤ (0 : Int) + d2701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3001, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25067 p hg
    simpa only [d3001, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3001, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25069 p hg
    simpa only [d3001, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25071 (p : Pattern) (guard : d5502 p = 1) : d3002 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3002, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d3002, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3002, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17403 p hg
    simpa only [d3002, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25072 (p : Pattern) (guard : d5502 p = 1) : d1899 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1899, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17339 p hg
    simpa only [d1899, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1899, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1899, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25073 (p : Pattern) (guard : d5502 p = 1) : d3003 p ≤ (0 : Int) + d2706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3003, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25071 p hg
    simpa only [d3003, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3003, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25072 p hg
    simpa only [d3003, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25074 (p : Pattern) (guard : d5502 p = 1) : d1906 p ≤ (0 : Int) + d2710 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1906, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17346 p hg
    simpa only [d1906, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1906, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1906, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25075 (p : Pattern) (guard : d5502 p = 1) : d3004 p ≤ (0 : Int) + d2711 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3004, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25071 p hg
    simpa only [d3004, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3004, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25074 p hg
    simpa only [d3004, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25076 (p : Pattern) (guard : d5502 p = 1) : d3005 p ≤ (0 : Int) + d2712 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3005, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25073 p hg
    simpa only [d3005, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3005, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25075 p hg
    simpa only [d3005, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25077 (p : Pattern) (guard : d5502 p = 1) : d3006 p ≤ (0 : Int) + d2713 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3006, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25071 p hg
    simpa only [d3006, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3006, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3006, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25078 (p : Pattern) (guard : d5502 p = 1) : d3007 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3007, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d3007, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3007, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17411 p hg
    simpa only [d3007, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25079 (p : Pattern) (guard : d5502 p = 1) : d3008 p ≤ (0 : Int) + d2714 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3008, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25078 p hg
    simpa only [d3008, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3008, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3008, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25080 (p : Pattern) (guard : d5502 p = 1) : d3009 p ≤ (0 : Int) + d2715 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3009, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25077 p hg
    simpa only [d3009, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3009, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25079 p hg
    simpa only [d3009, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25081 (p : Pattern) (guard : d5502 p = 1) : d3010 p ≤ (0 : Int) + d2716 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3010, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25076 p hg
    simpa only [d3010, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3010, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25080 p hg
    simpa only [d3010, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25082 (p : Pattern) (guard : d5502 p = 1) : d3011 p ≤ (0 : Int) + d2717 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3011, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24968 p hg
    simpa only [d3011, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3011, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3011, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25083 (p : Pattern) (guard : d5502 p = 1) : d3012 p ≤ (0 : Int) + d2718 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3012, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25080 p hg
    simpa only [d3012, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3012, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25082 p hg
    simpa only [d3012, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25084 (p : Pattern) (guard : d5502 p = 1) : d3013 p ≤ (0 : Int) + d2719 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3013, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25081 p hg
    simpa only [d3013, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3013, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25083 p hg
    simpa only [d3013, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25085 (p : Pattern) (guard : d5502 p = 1) : d3014 p ≤ (0 : Int) + d2720 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3014, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25070 p hg
    simpa only [d3014, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3014, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25084 p hg
    simpa only [d3014, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25086 (p : Pattern) (guard : d5502 p = 1) : d2993 p ≤ (0 : Int) + d2723 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2993, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17358 p hg
    simpa only [d2993, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2993, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17390 p hg
    simpa only [d2993, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25087 (p : Pattern) (guard : d5502 p = 1) : d2994 p ≤ (0 : Int) + d2724 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2994, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25086 p hg
    simpa only [d2994, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2994, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25058 p hg
    simpa only [d2994, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25088 (p : Pattern) (guard : d5502 p = 1) : d3015 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3015, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d3015, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3015, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17581 p hg
    simpa only [d3015, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25089 (p : Pattern) (guard : d5502 p = 1) : d1922 p ≤ (0 : Int) + d2728 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1922, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17368 p hg
    simpa only [d1922, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1922, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1922, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25090 (p : Pattern) (guard : d5502 p = 1) : d3016 p ≤ (0 : Int) + d2729 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3016, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25088 p hg
    simpa only [d3016, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3016, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25089 p hg
    simpa only [d3016, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25091 (p : Pattern) (guard : d5502 p = 1) : d3017 p ≤ (0 : Int) + d2730 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3017, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25087 p hg
    simpa only [d3017, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3017, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25090 p hg
    simpa only [d3017, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25092 (p : Pattern) (guard : d5502 p = 1) : d3018 p ≤ (0 : Int) + d2731 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3018, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25065 p hg
    simpa only [d3018, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3018, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24956 p hg
    simpa only [d3018, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25093 (p : Pattern) (guard : d5502 p = 1) : d3019 p ≤ (0 : Int) + d2732 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3019, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25091 p hg
    simpa only [d3019, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3019, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25092 p hg
    simpa only [d3019, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25094 (p : Pattern) (guard : d5502 p = 1) : d3020 p ≤ (0 : Int) + d2733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3020, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25065 p hg
    simpa only [d3020, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3020, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24959 p hg
    simpa only [d3020, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25095 (p : Pattern) (guard : d5502 p = 1) : d3021 p ≤ (0 : Int) + d2734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3021, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25094 p hg
    simpa only [d3021, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3021, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3021, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25096 (p : Pattern) (guard : d5502 p = 1) : d3022 p ≤ (0 : Int) + d2735 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3022, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25093 p hg
    simpa only [d3022, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3022, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25095 p hg
    simpa only [d3022, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25097 (p : Pattern) (guard : d5502 p = 1) : d3023 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3023, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d3023, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3023, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17339 p hg
    simpa only [d3023, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25098 (p : Pattern) (guard : d5502 p = 1) : d3024 p ≤ (0 : Int) + d2736 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3024, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25097 p hg
    simpa only [d3024, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3024, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3024, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25099 (p : Pattern) (guard : d5502 p = 1) : d3025 p ≤ (0 : Int) + d2737 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3025, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25075 p hg
    simpa only [d3025, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3025, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25098 p hg
    simpa only [d3025, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25100 (p : Pattern) (guard : d5502 p = 1) : d3026 p ≤ (0 : Int) + d2738 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3026, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25079 p hg
    simpa only [d3026, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3026, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24968 p hg
    simpa only [d3026, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25101 (p : Pattern) (guard : d5502 p = 1) : d3027 p ≤ (0 : Int) + d2739 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3027, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25099 p hg
    simpa only [d3027, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3027, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25100 p hg
    simpa only [d3027, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25102 (p : Pattern) (guard : d5502 p = 1) : d3028 p ≤ (0 : Int) + d2740 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3028, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25079 p hg
    simpa only [d3028, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3028, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24970 p hg
    simpa only [d3028, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25103 (p : Pattern) (guard : d5502 p = 1) : d3029 p ≤ (0 : Int) + d2741 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3029, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25102 p hg
    simpa only [d3029, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3029, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3029, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25104 (p : Pattern) (guard : d5502 p = 1) : d3030 p ≤ (0 : Int) + d2742 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3030, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25101 p hg
    simpa only [d3030, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3030, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25103 p hg
    simpa only [d3030, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25105 (p : Pattern) (guard : d5502 p = 1) : d3031 p ≤ (0 : Int) + d2743 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3031, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25096 p hg
    simpa only [d3031, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3031, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25104 p hg
    simpa only [d3031, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25106 (p : Pattern) (guard : d5502 p = 1) : d3032 p ≤ (0 : Int) + d2744 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3032, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25085 p hg
    simpa only [d3032, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3032, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25105 p hg
    simpa only [d3032, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25107 (p : Pattern) (guard : d5502 p = 1) : d3033 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3033, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d3033, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3033, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17562 p hg
    simpa only [d3033, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25108 (p : Pattern) (guard : d5502 p = 1) : d1943 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1943, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17390 p hg
    simpa only [d1943, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1943, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1943, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25109 (p : Pattern) (guard : d5502 p = 1) : d3034 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3034, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25107 p hg
    simpa only [d3034, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3034, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25108 p hg
    simpa only [d3034, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25110 (p : Pattern) (guard : d0 p = 1) : d3036 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25111 (p : Pattern) (guard : d5502 p = 1) : d3037 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d3037, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d5502, d3037, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d3037, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25110 p hg
    simpa only [d5502, d3037, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25112 (p : Pattern) (guard : d5502 p = 1) : d3038 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3038, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17394 p hg
    simpa only [d3038, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3038, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25111 p hg
    simpa only [d3038, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25113 (p : Pattern) (guard : d5502 p = 1) : d3039 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3039, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d3039, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3039, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25112 p hg
    simpa only [d3039, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25114 (p : Pattern) (guard : d5502 p = 1) : d1952 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1952, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17397 p hg
    simpa only [d1952, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1952, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1952, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25115 (p : Pattern) (guard : d5502 p = 1) : d3040 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3040, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25113 p hg
    simpa only [d3040, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3040, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25114 p hg
    simpa only [d3040, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25116 (p : Pattern) (guard : d5502 p = 1) : d3041 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25109 p hg
    simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25115 p hg
    simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25117 (p : Pattern) (guard : d5502 p = 1) : d1958 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1958, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17403 p hg
    simpa only [d1958, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1958, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1958, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25118 (p : Pattern) (guard : d5502 p = 1) : d3042 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3042, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25071 p hg
    simpa only [d3042, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3042, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25117 p hg
    simpa only [d3042, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25119 (p : Pattern) (guard : d5502 p = 1) : d1967 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1967, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17411 p hg
    simpa only [d1967, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1967, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1967, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25120 (p : Pattern) (guard : d5502 p = 1) : d3043 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3043, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25078 p hg
    simpa only [d3043, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3043, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25119 p hg
    simpa only [d3043, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25121 (p : Pattern) (guard : d5502 p = 1) : d3044 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3044, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25118 p hg
    simpa only [d3044, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3044, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25120 p hg
    simpa only [d3044, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25122 (p : Pattern) (guard : d5502 p = 1) : d3045 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3045, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25116 p hg
    simpa only [d3045, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3045, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25121 p hg
    simpa only [d3045, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25123 (p : Pattern) (guard : d5502 p = 1) : d3046 p ≤ (0 : Int) + d2751 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3046, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25121 p hg
    simpa only [d3046, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3046, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25068 p hg
    simpa only [d3046, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25124 (p : Pattern) (guard : d5502 p = 1) : d3047 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3047, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25122 p hg
    simpa only [d3047, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3047, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25123 p hg
    simpa only [d3047, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25125 (p : Pattern) (guard : d5502 p = 1) : d3048 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3048, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25097 p hg
    simpa only [d3048, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3048, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25072 p hg
    simpa only [d3048, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25126 (p : Pattern) (guard : d5502 p = 1) : d3049 p ≤ (0 : Int) + d2754 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3049, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15062 p hg
    simpa only [d3049, d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3049, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17346 p hg
    simpa only [d3049, d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25127 (p : Pattern) (guard : d5502 p = 1) : d3050 p ≤ (0 : Int) + d2755 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3050, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25126 p hg
    simpa only [d3050, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3050, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25074 p hg
    simpa only [d3050, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25128 (p : Pattern) (guard : d5502 p = 1) : d3051 p ≤ (0 : Int) + d2756 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3051, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25125 p hg
    simpa only [d3051, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3051, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25127 p hg
    simpa only [d3051, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25129 (p : Pattern) (guard : d5502 p = 1) : d3052 p ≤ (0 : Int) + d2757 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3052, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25128 p hg
    simpa only [d3052, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3052, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3052, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25130 (p : Pattern) (guard : d5502 p = 1) : d3053 p ≤ (0 : Int) + d2758 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3053, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25129 p hg
    simpa only [d3053, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3053, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3053, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25131 (p : Pattern) (guard : d5502 p = 1) : d3054 p ≤ (0 : Int) + d2759 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3054, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25124 p hg
    simpa only [d3054, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3054, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25130 p hg
    simpa only [d3054, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25132 (p : Pattern) (guard : d5502 p = 1) : d3055 p ≤ (0 : Int) + d2760 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3055, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25115 p hg
    simpa only [d3055, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3055, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25125 p hg
    simpa only [d3055, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25133 (p : Pattern) (guard : d5502 p = 1) : d3056 p ≤ (0 : Int) + d2761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3056, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25120 p hg
    simpa only [d3056, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3056, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24956 p hg
    simpa only [d3056, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25134 (p : Pattern) (guard : d5502 p = 1) : d3057 p ≤ (0 : Int) + d2762 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3057, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25132 p hg
    simpa only [d3057, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3057, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25133 p hg
    simpa only [d3057, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25135 (p : Pattern) (guard : d5502 p = 1) : d3058 p ≤ (0 : Int) + d2763 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3058, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25120 p hg
    simpa only [d3058, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3058, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24959 p hg
    simpa only [d3058, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25136 (p : Pattern) (guard : d5502 p = 1) : d3059 p ≤ (0 : Int) + d2764 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3059, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25135 p hg
    simpa only [d3059, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3059, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3059, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25137 (p : Pattern) (guard : d5502 p = 1) : d3060 p ≤ (0 : Int) + d2765 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3060, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25134 p hg
    simpa only [d3060, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3060, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25136 p hg
    simpa only [d3060, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25138 (p : Pattern) (guard : d5502 p = 1) : d3061 p ≤ (0 : Int) + d2766 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3061, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25127 p hg
    simpa only [d3061, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3061, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3061, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25139 (p : Pattern) (guard : d5502 p = 1) : d3062 p ≤ (0 : Int) + d2767 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3062, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25138 p hg
    simpa only [d3062, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3062, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3062, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25140 (p : Pattern) (guard : d5502 p = 1) : d3063 p ≤ (0 : Int) + d2768 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3063, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25139 p hg
    simpa only [d3063, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3063, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3063, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25141 (p : Pattern) (guard : d5502 p = 1) : d3064 p ≤ (0 : Int) + d2769 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3064, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25137 p hg
    simpa only [d3064, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3064, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25140 p hg
    simpa only [d3064, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25142 (p : Pattern) (guard : d5502 p = 1) : d3065 p ≤ (0 : Int) + d2770 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3065, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25131 p hg
    simpa only [d3065, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3065, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25141 p hg
    simpa only [d3065, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25143 (p : Pattern) (guard : d5502 p = 1) : d3066 p ≤ (0 : Int) + d2771 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3066, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25106 p hg
    simpa only [d3066, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3066, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25142 p hg
    simpa only [d3066, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25144 (p : Pattern) (guard : d5502 p = 1) : d3067 p ≤ (0 : Int) + d2772 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3067, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25068 p hg
    simpa only [d3067, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3067, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3067, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25145 (p : Pattern) (guard : d5502 p = 1) : d3068 p ≤ (0 : Int) + d2773 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3068, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25144 p hg
    simpa only [d3068, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3068, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3068, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25146 (p : Pattern) (guard : d5502 p = 1) : d3069 p ≤ (0 : Int) + d2774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3069, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25145 p hg
    simpa only [d3069, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3069, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3069, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25147 (p : Pattern) (guard : d5502 p = 1) : d3070 p ≤ (0 : Int) + d2775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3070, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25146 p hg
    simpa only [d3070, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3070, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3070, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25148 (p : Pattern) (guard : d5502 p = 1) : d3071 p ≤ (0 : Int) + d2776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3071, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25142 p hg
    simpa only [d3071, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3071, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25147 p hg
    simpa only [d3071, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25149 (p : Pattern) (guard : d5502 p = 1) : d3072 p ≤ (0 : Int) + d2777 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3072, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25143 p hg
    simpa only [d3072, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3072, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25148 p hg
    simpa only [d3072, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25150 (p : Pattern) (guard : d5502 p = 1) : d2998 p ≤ (0 : Int) + d2778 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2998, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25061 p hg
    simpa only [d2998, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2998, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25066 p hg
    simpa only [d2998, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25151 (p : Pattern) (guard : d5502 p = 1) : d3001 p ≤ (0 : Int) + d2779 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3001, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25150 p hg
    simpa only [d3001, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3001, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25069 p hg
    simpa only [d3001, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25152 (p : Pattern) (guard : d5502 p = 1) : d3014 p ≤ (0 : Int) + d2780 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3014, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25151 p hg
    simpa only [d3014, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3014, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25084 p hg
    simpa only [d3014, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25153 (p : Pattern) (guard : d5502 p = 1) : d3017 p ≤ (0 : Int) + d2781 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3017, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25061 p hg
    simpa only [d3017, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3017, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25090 p hg
    simpa only [d3017, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25154 (p : Pattern) (guard : d5502 p = 1) : d3019 p ≤ (0 : Int) + d2782 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3019, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25153 p hg
    simpa only [d3019, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3019, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25092 p hg
    simpa only [d3019, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25155 (p : Pattern) (guard : d5502 p = 1) : d3022 p ≤ (0 : Int) + d2783 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3022, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25154 p hg
    simpa only [d3022, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3022, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25095 p hg
    simpa only [d3022, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25156 (p : Pattern) (guard : d5502 p = 1) : d3031 p ≤ (0 : Int) + d2784 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3031, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25155 p hg
    simpa only [d3031, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3031, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25104 p hg
    simpa only [d3031, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25157 (p : Pattern) (guard : d5502 p = 1) : d3032 p ≤ (0 : Int) + d2785 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3032, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25152 p hg
    simpa only [d3032, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3032, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25156 p hg
    simpa only [d3032, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25158 (p : Pattern) (guard : d5502 p = 1) : d3066 p ≤ (0 : Int) + d2786 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3066, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25157 p hg
    simpa only [d3066, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3066, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25142 p hg
    simpa only [d3066, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25159 (p : Pattern) (guard : d5502 p = 1) : d3073 p ≤ (0 : Int) + d2787 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3073, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25142 p hg
    simpa only [d3073, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3073, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3073, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25160 (p : Pattern) (guard : d5502 p = 1) : d3074 p ≤ (0 : Int) + d2788 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3074, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25158 p hg
    simpa only [d3074, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3074, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25159 p hg
    simpa only [d3074, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25161 (p : Pattern) (guard : d5502 p = 1) : d3075 p ≤ (0 : Int) + d2789 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3075, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25149 p hg
    simpa only [d3075, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3075, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25160 p hg
    simpa only [d3075, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25162 (p : Pattern) (guard : d5502 p = 1) : d3076 p ≤ (0 : Int) + d2790 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3076, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25035 p hg
    simpa only [d3076, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3076, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25161 p hg
    simpa only [d3076, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25163 (p : Pattern) (guard : d5502 p = 1) : d3077 p ≤ (0 : Int) + d2791 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3077, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25056 p hg
    simpa only [d3077, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3077, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25162 p hg
    simpa only [d3077, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25164 (p : Pattern) (guard : d5502 p = 1) : d3078 p ≤ (0 : Int) + d2521 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d3078, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17222 p hg
    simpa only [d5502, d3078, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d3078, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17220 p hg
    simpa only [d5502, d3078, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25165 (p : Pattern) (guard : d5502 p = 1) : d3079 p ≤ (0 : Int) + d2522 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3079, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17221 p hg
    simpa only [d3079, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3079, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25164 p hg
    simpa only [d3079, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25166 (p : Pattern) (guard : d5502 p = 1) : d3080 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3080, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d3080, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3080, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25165 p hg
    simpa only [d3080, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25167 (p : Pattern) (guard : d5502 p = 1) : d2013 p ≤ (0 : Int) + d2602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2013, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17461 p hg
    simpa only [d2013, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2013, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2013, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25168 (p : Pattern) (guard : d5502 p = 1) : d3081 p ≤ (0 : Int) + d2603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3081, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25166 p hg
    simpa only [d3081, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3081, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25167 p hg
    simpa only [d3081, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25169 (p : Pattern) (guard : d5502 p = 1) : d3082 p ≤ (0 : Int) + d2604 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3082, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24978 p hg
    simpa only [d3082, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3082, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25168 p hg
    simpa only [d3082, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25170 (p : Pattern) (guard : d5502 p = 1) : d3083 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3083, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24978 p hg
    simpa only [d3083, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3083, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25169 p hg
    simpa only [d3083, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25171 (p : Pattern) (guard : d5502 p = 1) : d3084 p ≤ (0 : Int) + d2609 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3084, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25169 p hg
    simpa only [d3084, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3084, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24991 p hg
    simpa only [d3084, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25172 (p : Pattern) (guard : d5502 p = 1) : d3085 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3085, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25170 p hg
    simpa only [d3085, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3085, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25171 p hg
    simpa only [d3085, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25173 (p : Pattern) (guard : d5502 p = 1) : d3086 p ≤ (0 : Int) + d2792 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3086, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24963 p hg
    simpa only [d3086, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3086, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d3086, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25174 (p : Pattern) (guard : d5502 p = 1) : d3087 p ≤ (0 : Int) + d2793 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3087, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24994 p hg
    simpa only [d3087, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3087, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25173 p hg
    simpa only [d3087, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25175 (p : Pattern) (guard : d5502 p = 1) : d3088 p ≤ (0 : Int) + d2794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3088, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24963 p hg
    simpa only [d3088, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3088, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24933 p hg
    simpa only [d3088, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25176 (p : Pattern) (guard : d5502 p = 1) : d3089 p ≤ (0 : Int) + d2795 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3089, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24995 p hg
    simpa only [d3089, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3089, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3089, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25177 (p : Pattern) (guard : d5502 p = 1) : d3090 p ≤ (0 : Int) + d2796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3090, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25175 p hg
    simpa only [d3090, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3090, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25176 p hg
    simpa only [d3090, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25178 (p : Pattern) (guard : d5502 p = 1) : d3091 p ≤ (0 : Int) + d2797 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3091, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25174 p hg
    simpa only [d3091, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3091, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25177 p hg
    simpa only [d3091, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25179 (p : Pattern) (guard : d5502 p = 1) : d3092 p ≤ (0 : Int) + d2798 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3092, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24964 p hg
    simpa only [d3092, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3092, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25176 p hg
    simpa only [d3092, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25180 (p : Pattern) (guard : d5502 p = 1) : d3093 p ≤ (0 : Int) + d2799 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3093, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25179 p hg
    simpa only [d3093, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3093, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24971 p hg
    simpa only [d3093, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25181 (p : Pattern) (guard : d5502 p = 1) : d3094 p ≤ (0 : Int) + d2800 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3094, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25178 p hg
    simpa only [d3094, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3094, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25180 p hg
    simpa only [d3094, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25182 (p : Pattern) (guard : d5502 p = 1) : d3095 p ≤ (0 : Int) + d2801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3095, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25172 p hg
    simpa only [d3095, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3095, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25181 p hg
    simpa only [d3095, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25183 (p : Pattern) (guard : d5502 p = 1) : d3096 p ≤ (0 : Int) + d2541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d3096, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17125 p hg
    simpa only [d5502, d3096, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d3096, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17123 p hg
    simpa only [d5502, d3096, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25184 (p : Pattern) (guard : d5502 p = 1) : d3097 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3097, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17124 p hg
    simpa only [d3097, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3097, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25183 p hg
    simpa only [d3097, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25185 (p : Pattern) (guard : d5502 p = 1) : d3098 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3098, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d3098, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3098, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25184 p hg
    simpa only [d3098, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25186 (p : Pattern) (guard : d5502 p = 1) : d2031 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2031, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17481 p hg
    simpa only [d2031, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2031, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2031, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25187 (p : Pattern) (guard : d5502 p = 1) : d3099 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3099, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25185 p hg
    simpa only [d3099, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3099, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25186 p hg
    simpa only [d3099, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25188 (p : Pattern) (guard : d5502 p = 1) : d3100 p ≤ (0 : Int) + d2618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3100, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24978 p hg
    simpa only [d3100, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3100, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25187 p hg
    simpa only [d3100, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25189 (p : Pattern) (guard : d5502 p = 1) : d3101 p ≤ (0 : Int) + d2619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3101, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25168 p hg
    simpa only [d3101, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3101, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24990 p hg
    simpa only [d3101, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25190 (p : Pattern) (guard : d5502 p = 1) : d3102 p ≤ (0 : Int) + d2620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3102, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25188 p hg
    simpa only [d3102, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3102, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25189 p hg
    simpa only [d3102, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25191 (p : Pattern) (guard : d5502 p = 1) : d3103 p ≤ (0 : Int) + d2621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3103, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25168 p hg
    simpa only [d3103, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3103, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24956 p hg
    simpa only [d3103, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25192 (p : Pattern) (guard : d5502 p = 1) : d3104 p ≤ (0 : Int) + d2622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3104, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25191 p hg
    simpa only [d3104, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3104, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24960 p hg
    simpa only [d3104, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25193 (p : Pattern) (guard : d5502 p = 1) : d3105 p ≤ (0 : Int) + d2623 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3105, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25190 p hg
    simpa only [d3105, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3105, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25192 p hg
    simpa only [d3105, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25194 (p : Pattern) (guard : d5502 p = 1) : d3106 p ≤ (0 : Int) + d2802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3106, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25173 p hg
    simpa only [d3106, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3106, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d3106, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25195 (p : Pattern) (guard : d5502 p = 1) : d3107 p ≤ (0 : Int) + d2803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3107, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25176 p hg
    simpa only [d3107, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3107, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24970 p hg
    simpa only [d3107, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25196 (p : Pattern) (guard : d5502 p = 1) : d3108 p ≤ (0 : Int) + d2804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3108, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25194 p hg
    simpa only [d3108, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3108, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25195 p hg
    simpa only [d3108, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25197 (p : Pattern) (guard : d5502 p = 1) : d3109 p ≤ (0 : Int) + d2805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3109, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25176 p hg
    simpa only [d3109, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3109, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3109, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25198 (p : Pattern) (guard : d5502 p = 1) : d3110 p ≤ (0 : Int) + d2806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3110, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25197 p hg
    simpa only [d3110, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3110, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3110, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25199 (p : Pattern) (guard : d5502 p = 1) : d3111 p ≤ (0 : Int) + d2807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3111, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25196 p hg
    simpa only [d3111, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3111, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25198 p hg
    simpa only [d3111, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
