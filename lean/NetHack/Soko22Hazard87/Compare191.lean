import NetHack.Soko22Hazard87.Compare190
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47750 (p : Pattern) (guard : d369937 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369935 p = 1 := by simpa only [d369937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47748 p hg
    simpa only [d369937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369695 p = 1 := by simpa only [d369937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47404 p hg
    simpa only [d369937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47751 (p : Pattern) (guard : d369938 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369936 p = 1 := by simpa only [d369938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47749 p hg
    simpa only [d369938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369937 p = 1 := by simpa only [d369938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47750 p hg
    simpa only [d369938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47752 (p : Pattern) (guard : d369939 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369938 p = 1 := by simpa only [d369939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47751 p hg
    simpa only [d369939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369861 p = 1 := by simpa only [d369939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47674 p hg
    simpa only [d369939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47753 (p : Pattern) (guard : d369940 p = 1) : d50577 p ≤ (1 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369940, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d369940, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369939 p = 1 := by simpa only [d369940, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47752 p hg
    simpa only [d369940, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47754 (p : Pattern) (guard : d369941 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369941, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d369941, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369940 p = 1 := by simpa only [d369941, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47753 p hg
    simpa only [d369941, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47755 (p : Pattern) (guard : d369942 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369860 p = 1 := by simpa only [d369942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47673 p hg
    simpa only [d369942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369863 p = 1 := by simpa only [d369942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47676 p hg
    simpa only [d369942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47756 (p : Pattern) (guard : d369943 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369861 p = 1 := by simpa only [d369943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47674 p hg
    simpa only [d369943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369942 p = 1 := by simpa only [d369943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47755 p hg
    simpa only [d369943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47757 (p : Pattern) (guard : d369944 p = 1) : d50577 p ≤ (1 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369944, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d369944, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369943 p = 1 := by simpa only [d369944, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47756 p hg
    simpa only [d369944, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47758 (p : Pattern) (guard : d369945 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369945, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d369945, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369944 p = 1 := by simpa only [d369945, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47757 p hg
    simpa only [d369945, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47759 (p : Pattern) (guard : d369946 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369941 p = 1 := by simpa only [d369946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47754 p hg
    simpa only [d369946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369945 p = 1 := by simpa only [d369946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47758 p hg
    simpa only [d369946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47760 (p : Pattern) (guard : d369947 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369946 p = 1 := by simpa only [d369947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47759 p hg
    simpa only [d369947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369872 p = 1 := by simpa only [d369947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47685 p hg
    simpa only [d369947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47761 (p : Pattern) (guard : d369948 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369947 p = 1 := by simpa only [d369948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47760 p hg
    simpa only [d369948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47762 (p : Pattern) (guard : d369949 p = 1) : d50590 p ≤ (1 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369948 p = 1 := by simpa only [d369949, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47761 p hg
    simpa only [d369949, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369949, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d369949, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47763 (p : Pattern) (guard : d369950 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369950, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369950, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369949 p = 1 := by simpa only [d369950, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47762 p hg
    simpa only [d369950, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47764 (p : Pattern) (guard : d369951 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369950 p = 1 := by simpa only [d369951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47763 p hg
    simpa only [d369951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369877 p = 1 := by simpa only [d369951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47690 p hg
    simpa only [d369951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47765 (p : Pattern) (guard : d369952 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369951 p = 1 := by simpa only [d369952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47764 p hg
    simpa only [d369952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47766 (p : Pattern) (guard : d369953 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369952 p = 1 := by simpa only [d369953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47765 p hg
    simpa only [d369953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47767 (p : Pattern) (guard : d369954 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369953 p = 1 := by simpa only [d369954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47766 p hg
    simpa only [d369954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47768 (p : Pattern) (guard : d369955 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369954 p = 1 := by simpa only [d369955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47767 p hg
    simpa only [d369955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369885 p = 1 := by simpa only [d369955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47698 p hg
    simpa only [d369955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47769 (p : Pattern) (guard : d369956 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369955 p = 1 := by simpa only [d369956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47768 p hg
    simpa only [d369956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47770 (p : Pattern) (guard : d369957 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369877 p = 1 := by simpa only [d369957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47690 p hg
    simpa only [d369957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47771 (p : Pattern) (guard : d369958 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369957 p = 1 := by simpa only [d369958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47770 p hg
    simpa only [d369958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47772 (p : Pattern) (guard : d369959 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369958 p = 1 := by simpa only [d369959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47771 p hg
    simpa only [d369959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47773 (p : Pattern) (guard : d369960 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369959 p = 1 := by simpa only [d369960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47772 p hg
    simpa only [d369960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47774 (p : Pattern) (guard : d369961 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369960 p = 1 := by simpa only [d369961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47773 p hg
    simpa only [d369961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47775 (p : Pattern) (guard : d369962 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369961 p = 1 := by simpa only [d369962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d369962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47776 (p : Pattern) (guard : d369963 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369956 p = 1 := by simpa only [d369963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47769 p hg
    simpa only [d369963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369962 p = 1 := by simpa only [d369963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47775 p hg
    simpa only [d369963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47777 (p : Pattern) (guard : d369964 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d369925 p = 1 := by simpa only [d369964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47738 p hg
    simpa only [d369964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369963 p = 1 := by simpa only [d369964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47776 p hg
    simpa only [d369964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47778 (p : Pattern) (guard : d369965 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d369916 p = 1 := by simpa only [d369965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47729 p hg
    simpa only [d369965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369964 p = 1 := by simpa only [d369965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47777 p hg
    simpa only [d369965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47779 (p : Pattern) (guard : d369966 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369965 p = 1 := by simpa only [d369966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47778 p hg
    simpa only [d369966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47780 (p : Pattern) (guard : d369967 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369909 p = 1 := by simpa only [d369967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47722 p hg
    simpa only [d369967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47781 (p : Pattern) (guard : d369968 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369911 p = 1 := by simpa only [d369968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47724 p hg
    simpa only [d369968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47782 (p : Pattern) (guard : d369969 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369967 p = 1 := by simpa only [d369969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d369969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369968 p = 1 := by simpa only [d369969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47781 p hg
    simpa only [d369969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47783 (p : Pattern) (guard : d369970 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369969 p = 1 := by simpa only [d369970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47782 p hg
    simpa only [d369970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47784 (p : Pattern) (guard : d369971 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369970 p = 1 := by simpa only [d369971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47783 p hg
    simpa only [d369971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47785 (p : Pattern) (guard : d369972 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369971 p = 1 := by simpa only [d369972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47784 p hg
    simpa only [d369972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47786 (p : Pattern) (guard : d369973 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369918 p = 1 := by simpa only [d369973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47731 p hg
    simpa only [d369973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47787 (p : Pattern) (guard : d369974 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369921 p = 1 := by simpa only [d369974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47734 p hg
    simpa only [d369974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47788 (p : Pattern) (guard : d369975 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369973 p = 1 := by simpa only [d369975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47786 p hg
    simpa only [d369975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369974 p = 1 := by simpa only [d369975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47787 p hg
    simpa only [d369975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47789 (p : Pattern) (guard : d369976 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369975 p = 1 := by simpa only [d369976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47788 p hg
    simpa only [d369976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47790 (p : Pattern) (guard : d369977 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369976 p = 1 := by simpa only [d369977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47789 p hg
    simpa only [d369977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47791 (p : Pattern) (guard : d369978 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369953 p = 1 := by simpa only [d369978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47766 p hg
    simpa only [d369978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47792 (p : Pattern) (guard : d369979 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369978 p = 1 := by simpa only [d369979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47791 p hg
    simpa only [d369979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369898 p = 1 := by simpa only [d369979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47711 p hg
    simpa only [d369979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47793 (p : Pattern) (guard : d369980 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369979 p = 1 := by simpa only [d369980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47792 p hg
    simpa only [d369980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47794 (p : Pattern) (guard : d369981 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369959 p = 1 := by simpa only [d369981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47772 p hg
    simpa only [d369981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47795 (p : Pattern) (guard : d369982 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369981 p = 1 := by simpa only [d369982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47794 p hg
    simpa only [d369982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47796 (p : Pattern) (guard : d369983 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369982 p = 1 := by simpa only [d369983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47795 p hg
    simpa only [d369983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47797 (p : Pattern) (guard : d369984 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369980 p = 1 := by simpa only [d369984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47793 p hg
    simpa only [d369984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369983 p = 1 := by simpa only [d369984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47796 p hg
    simpa only [d369984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47798 (p : Pattern) (guard : d369985 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d369977 p = 1 := by simpa only [d369985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47790 p hg
    simpa only [d369985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369984 p = 1 := by simpa only [d369985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47797 p hg
    simpa only [d369985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47799 (p : Pattern) (guard : d369986 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d369972 p = 1 := by simpa only [d369986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47785 p hg
    simpa only [d369986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369985 p = 1 := by simpa only [d369986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47798 p hg
    simpa only [d369986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47800 (p : Pattern) (guard : d369987 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369965 p = 1 := by simpa only [d369987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47778 p hg
    simpa only [d369987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369986 p = 1 := by simpa only [d369987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47799 p hg
    simpa only [d369987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47801 (p : Pattern) (guard : d369988 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369966 p = 1 := by simpa only [d369988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47779 p hg
    simpa only [d369988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369987 p = 1 := by simpa only [d369988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47800 p hg
    simpa only [d369988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47802 (p : Pattern) (guard : d369989 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369889 p = 1 := by simpa only [d369989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47702 p hg
    simpa only [d369989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47803 (p : Pattern) (guard : d369990 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369989 p = 1 := by simpa only [d369990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47802 p hg
    simpa only [d369990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47804 (p : Pattern) (guard : d369991 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369990 p = 1 := by simpa only [d369991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47803 p hg
    simpa only [d369991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47805 (p : Pattern) (guard : d369992 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369991 p = 1 := by simpa only [d369992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47804 p hg
    simpa only [d369992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47806 (p : Pattern) (guard : d369993 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369992 p = 1 := by simpa only [d369993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47805 p hg
    simpa only [d369993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47807 (p : Pattern) (guard : d369994 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369894 p = 1 := by simpa only [d369994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47707 p hg
    simpa only [d369994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369993 p = 1 := by simpa only [d369994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47806 p hg
    simpa only [d369994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47808 (p : Pattern) (guard : d369995 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369899 p = 1 := by simpa only [d369995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47712 p hg
    simpa only [d369995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47809 (p : Pattern) (guard : d369996 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369995 p = 1 := by simpa only [d369996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47808 p hg
    simpa only [d369996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47810 (p : Pattern) (guard : d369997 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369996 p = 1 := by simpa only [d369997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47809 p hg
    simpa only [d369997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47811 (p : Pattern) (guard : d369998 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369997 p = 1 := by simpa only [d369998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47810 p hg
    simpa only [d369998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47812 (p : Pattern) (guard : d369999 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369998 p = 1 := by simpa only [d369999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47811 p hg
    simpa only [d369999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47813 (p : Pattern) (guard : d370000 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369993 p = 1 := by simpa only [d370000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47806 p hg
    simpa only [d370000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369999 p = 1 := by simpa only [d370000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47812 p hg
    simpa only [d370000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47814 (p : Pattern) (guard : d370001 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369994 p = 1 := by simpa only [d370001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47807 p hg
    simpa only [d370001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370000 p = 1 := by simpa only [d370001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47813 p hg
    simpa only [d370001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47815 (p : Pattern) (guard : d370002 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369988 p = 1 := by simpa only [d370002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47801 p hg
    simpa only [d370002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370001 p = 1 := by simpa only [d370002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47814 p hg
    simpa only [d370002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47816 (p : Pattern) (guard : d370003 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d370002 p = 1 := by simpa only [d370003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47815 p hg
    simpa only [d370003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d370003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47817 (p : Pattern) (guard : d370004 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 50 with
  | false =>
    have hg : d369908 p = 1 := by simpa only [d370004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47721 p hg
    simpa only [d370004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370003 p = 1 := by simpa only [d370004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47816 p hg
    simpa only [d370004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47818 (p : Pattern) (guard : d369926 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46723 p hg
    simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46055 p = 1 := by simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47475 p hg
    simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47819 (p : Pattern) (guard : d369927 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369926 p = 1 := by simpa only [d369927, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47818 p hg
    simpa only [d369927, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369927, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369927, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47820 (p : Pattern) (guard : d369928 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369927 p = 1 := by simpa only [d369928, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47819 p hg
    simpa only [d369928, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369928, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369928, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47821 (p : Pattern) (guard : d369929 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369929, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d369929, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369928 p = 1 := by simpa only [d369929, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47820 p hg
    simpa only [d369929, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47822 (p : Pattern) (guard : d369930 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369929 p = 1 := by simpa only [d369930, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47821 p hg
    simpa only [d369930, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369930, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d369930, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47823 (p : Pattern) (guard : d369931 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47475 p hg
    simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369690 p = 1 := by simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47491 p hg
    simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47824 (p : Pattern) (guard : d369932 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369931 p = 1 := by simpa only [d369932, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47823 p hg
    simpa only [d369932, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369932, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369932, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47825 (p : Pattern) (guard : d369933 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369932 p = 1 := by simpa only [d369933, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47824 p hg
    simpa only [d369933, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369933, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369933, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47826 (p : Pattern) (guard : d369934 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369934, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d369934, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369933 p = 1 := by simpa only [d369934, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47825 p hg
    simpa only [d369934, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47827 (p : Pattern) (guard : d369935 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369934 p = 1 := by simpa only [d369935, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47826 p hg
    simpa only [d369935, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369935, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d369935, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47828 (p : Pattern) (guard : d369936 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369930 p = 1 := by simpa only [d369936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47822 p hg
    simpa only [d369936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369935 p = 1 := by simpa only [d369936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47827 p hg
    simpa only [d369936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47829 (p : Pattern) (guard : d369937 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369935 p = 1 := by simpa only [d369937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47827 p hg
    simpa only [d369937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369695 p = 1 := by simpa only [d369937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47496 p hg
    simpa only [d369937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47830 (p : Pattern) (guard : d369938 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369936 p = 1 := by simpa only [d369938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47828 p hg
    simpa only [d369938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369937 p = 1 := by simpa only [d369938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47829 p hg
    simpa only [d369938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47831 (p : Pattern) (guard : d369855 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46946 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46723 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47832 (p : Pattern) (guard : d369856 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369855 p = 1 := by simpa only [d369856, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47831 p hg
    simpa only [d369856, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369856, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369856, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47833 (p : Pattern) (guard : d369857 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369856 p = 1 := by simpa only [d369857, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47832 p hg
    simpa only [d369857, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369857, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369857, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47834 (p : Pattern) (guard : d369858 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369858, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d369858, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369857 p = 1 := by simpa only [d369858, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47833 p hg
    simpa only [d369858, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47835 (p : Pattern) (guard : d369859 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369858 p = 1 := by simpa only [d369859, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47834 p hg
    simpa only [d369859, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369859, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d369859, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47836 (p : Pattern) (guard : d369860 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369695 p = 1 := by simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47496 p hg
    simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369859 p = 1 := by simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47835 p hg
    simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47837 (p : Pattern) (guard : d369861 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369688 p = 1 := by simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47489 p hg
    simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369860 p = 1 := by simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47836 p hg
    simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47838 (p : Pattern) (guard : d369939 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369938 p = 1 := by simpa only [d369939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47830 p hg
    simpa only [d369939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369861 p = 1 := by simpa only [d369939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47837 p hg
    simpa only [d369939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47839 (p : Pattern) (guard : d369940 p = 1) : d50664 p ≤ (1 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369940, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d369940, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369939 p = 1 := by simpa only [d369940, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47838 p hg
    simpa only [d369940, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47840 (p : Pattern) (guard : d369941 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369941, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d369941, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369940 p = 1 := by simpa only [d369941, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47839 p hg
    simpa only [d369941, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47841 (p : Pattern) (guard : d369863 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369859 p = 1 := by simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47835 p hg
    simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46731 p hg
    simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47842 (p : Pattern) (guard : d369942 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369860 p = 1 := by simpa only [d369942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47836 p hg
    simpa only [d369942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369863 p = 1 := by simpa only [d369942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47841 p hg
    simpa only [d369942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47843 (p : Pattern) (guard : d369943 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369861 p = 1 := by simpa only [d369943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47837 p hg
    simpa only [d369943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369942 p = 1 := by simpa only [d369943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47842 p hg
    simpa only [d369943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47844 (p : Pattern) (guard : d369944 p = 1) : d50664 p ≤ (1 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369944, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d369944, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369943 p = 1 := by simpa only [d369944, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47843 p hg
    simpa only [d369944, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47845 (p : Pattern) (guard : d369945 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369945, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d369945, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369944 p = 1 := by simpa only [d369945, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47844 p hg
    simpa only [d369945, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47846 (p : Pattern) (guard : d369946 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369941 p = 1 := by simpa only [d369946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47840 p hg
    simpa only [d369946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369945 p = 1 := by simpa only [d369946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47845 p hg
    simpa only [d369946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47847 (p : Pattern) (guard : d369862 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369507 p = 1 := by simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47184 p hg
    simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369859 p = 1 := by simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47835 p hg
    simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47848 (p : Pattern) (guard : d369864 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369862 p = 1 := by simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47847 p hg
    simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369863 p = 1 := by simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47841 p hg
    simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47849 (p : Pattern) (guard : d369865 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369861 p = 1 := by simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47837 p hg
    simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369864 p = 1 := by simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47848 p hg
    simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47850 (p : Pattern) (guard : d369866 p = 1) : d50664 p ≤ (1 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369866, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d369866, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369865 p = 1 := by simpa only [d369866, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47849 p hg
    simpa only [d369866, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47851 (p : Pattern) (guard : d369867 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369867, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d369867, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369866 p = 1 := by simpa only [d369867, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47850 p hg
    simpa only [d369867, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47852 (p : Pattern) (guard : d369868 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369863 p = 1 := by simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47841 p hg
    simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46731 p hg
    simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47853 (p : Pattern) (guard : d369869 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369864 p = 1 := by simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47848 p hg
    simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369868 p = 1 := by simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47852 p hg
    simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47854 (p : Pattern) (guard : d369870 p = 1) : d50664 p ≤ (1 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369870, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d369870, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369869 p = 1 := by simpa only [d369870, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d369870, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47855 (p : Pattern) (guard : d369871 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369871, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d369871, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369870 p = 1 := by simpa only [d369871, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47854 p hg
    simpa only [d369871, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47856 (p : Pattern) (guard : d369872 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369867 p = 1 := by simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47851 p hg
    simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369871 p = 1 := by simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47855 p hg
    simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47857 (p : Pattern) (guard : d369947 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369946 p = 1 := by simpa only [d369947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47846 p hg
    simpa only [d369947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369872 p = 1 := by simpa only [d369947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47856 p hg
    simpa only [d369947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47858 (p : Pattern) (guard : d369948 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369947 p = 1 := by simpa only [d369948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47857 p hg
    simpa only [d369948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47859 (p : Pattern) (guard : d369949 p = 1) : d50673 p ≤ (1 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369948 p = 1 := by simpa only [d369949, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47858 p hg
    simpa only [d369949, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369949, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d369949, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47860 (p : Pattern) (guard : d369950 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369950, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d369950, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369949 p = 1 := by simpa only [d369950, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47859 p hg
    simpa only [d369950, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47861 (p : Pattern) (guard : d369873 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369871 p = 1 := by simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47855 p hg
    simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47862 (p : Pattern) (guard : d369874 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369872 p = 1 := by simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47856 p hg
    simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369873 p = 1 := by simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47861 p hg
    simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47863 (p : Pattern) (guard : d369875 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369874 p = 1 := by simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47862 p hg
    simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47864 (p : Pattern) (guard : d369876 p = 1) : d50673 p ≤ (1 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369875 p = 1 := by simpa only [d369876, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47863 p hg
    simpa only [d369876, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369876, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d369876, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47865 (p : Pattern) (guard : d369877 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369877, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d369877, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369876 p = 1 := by simpa only [d369877, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47864 p hg
    simpa only [d369877, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47866 (p : Pattern) (guard : d369951 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369950 p = 1 := by simpa only [d369951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47860 p hg
    simpa only [d369951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369877 p = 1 := by simpa only [d369951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d369951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47867 (p : Pattern) (guard : d369952 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369951 p = 1 := by simpa only [d369952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47866 p hg
    simpa only [d369952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47868 (p : Pattern) (guard : d369953 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369952 p = 1 := by simpa only [d369953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47867 p hg
    simpa only [d369953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47869 (p : Pattern) (guard : d369978 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369953 p = 1 := by simpa only [d369978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47868 p hg
    simpa only [d369978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47870 (p : Pattern) (guard : d369878 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369873 p = 1 := by simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47861 p hg
    simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47871 (p : Pattern) (guard : d369879 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369878 p = 1 := by simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47870 p hg
    simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47872 (p : Pattern) (guard : d369880 p = 1) : d50673 p ≤ (1 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369879 p = 1 := by simpa only [d369880, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d369880, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369880, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d369880, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47873 (p : Pattern) (guard : d369881 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369881, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d369881, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369880 p = 1 := by simpa only [d369881, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47872 p hg
    simpa only [d369881, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47874 (p : Pattern) (guard : d369882 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369877 p = 1 := by simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369881 p = 1 := by simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47873 p hg
    simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47875 (p : Pattern) (guard : d369883 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369882 p = 1 := by simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47874 p hg
    simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47876 (p : Pattern) (guard : d369884 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369883 p = 1 := by simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47875 p hg
    simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47877 (p : Pattern) (guard : d369898 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369884 p = 1 := by simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47876 p hg
    simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47878 (p : Pattern) (guard : d369979 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369978 p = 1 := by simpa only [d369979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47869 p hg
    simpa only [d369979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369898 p = 1 := by simpa only [d369979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47877 p hg
    simpa only [d369979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47879 (p : Pattern) (guard : d369980 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369979 p = 1 := by simpa only [d369980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47878 p hg
    simpa only [d369980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47880 (p : Pattern) (guard : d369957 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369877 p = 1 := by simpa only [d369957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d369957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47881 (p : Pattern) (guard : d369958 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369957 p = 1 := by simpa only [d369958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47880 p hg
    simpa only [d369958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47882 (p : Pattern) (guard : d369959 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369958 p = 1 := by simpa only [d369959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47881 p hg
    simpa only [d369959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47883 (p : Pattern) (guard : d369981 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369959 p = 1 := by simpa only [d369981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47882 p hg
    simpa only [d369981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47884 (p : Pattern) (guard : d369982 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369981 p = 1 := by simpa only [d369982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47883 p hg
    simpa only [d369982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47885 (p : Pattern) (guard : d369983 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369982 p = 1 := by simpa only [d369983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47884 p hg
    simpa only [d369983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47886 (p : Pattern) (guard : d369984 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369980 p = 1 := by simpa only [d369984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47879 p hg
    simpa only [d369984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369983 p = 1 := by simpa only [d369984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47885 p hg
    simpa only [d369984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47887 (p : Pattern) (guard : d370005 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d370005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369984 p = 1 := by simpa only [d370005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47886 p hg
    simpa only [d370005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47888 (p : Pattern) (guard : d370006 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d370006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370005 p = 1 := by simpa only [d370006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47887 p hg
    simpa only [d370006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47889 (p : Pattern) (guard : d370007 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370007, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d370007, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370006 p = 1 := by simpa only [d370007, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47888 p hg
    simpa only [d370007, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47890 (p : Pattern) (guard : d370008 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d370008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370007 p = 1 := by simpa only [d370008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47889 p hg
    simpa only [d370008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47891 (p : Pattern) (guard : d369886 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369881 p = 1 := by simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47873 p hg
    simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47892 (p : Pattern) (guard : d369887 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369886 p = 1 := by simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47891 p hg
    simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47893 (p : Pattern) (guard : d369888 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369887 p = 1 := by simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47892 p hg
    simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47894 (p : Pattern) (guard : d369899 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369888 p = 1 := by simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47893 p hg
    simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47895 (p : Pattern) (guard : d369995 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369899 p = 1 := by simpa only [d369995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47894 p hg
    simpa only [d369995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47896 (p : Pattern) (guard : d369996 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369995 p = 1 := by simpa only [d369996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47895 p hg
    simpa only [d369996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47897 (p : Pattern) (guard : d369997 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369996 p = 1 := by simpa only [d369997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47896 p hg
    simpa only [d369997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47898 (p : Pattern) (guard : d369998 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369997 p = 1 := by simpa only [d369998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47897 p hg
    simpa only [d369998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47899 (p : Pattern) (guard : d369999 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369998 p = 1 := by simpa only [d369999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47898 p hg
    simpa only [d369999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47900 (p : Pattern) (guard : d370009 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370009, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d370009, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369999 p = 1 := by simpa only [d370009, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47899 p hg
    simpa only [d370009, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47901 (p : Pattern) (guard : d370010 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d370010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370009 p = 1 := by simpa only [d370010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47900 p hg
    simpa only [d370010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47902 (p : Pattern) (guard : d370011 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 69 with
  | false =>
    have hg : d370008 p = 1 := by simpa only [d370011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47890 p hg
    simpa only [d370011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370010 p = 1 := by simpa only [d370011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47901 p hg
    simpa only [d370011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47903 (p : Pattern) (guard : d370012 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 51 with
  | false =>
    have hg : d370011 p = 1 := by simpa only [d370012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47902 p hg
    simpa only [d370012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d370012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47904 (p : Pattern) (guard : d370013 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 50 with
  | false =>
    have hg : d370012 p = 1 := by simpa only [d370013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47903 p hg
    simpa only [d370013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d370013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47905 (p : Pattern) (guard : d370014 p = 1) : d50676 p ≤ (1 : Int) + d367880 p := by
  cases selected : p 49 with
  | false =>
    have hg : d370004 p = 1 := by simpa only [d370014, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47817 p hg
    simpa only [d370014, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370013 p = 1 := by simpa only [d370014, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47904 p hg
    simpa only [d370014, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47906 (p : Pattern) (guard : d369926 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46776 p hg
    simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46055 p = 1 := by simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47558 p hg
    simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47907 (p : Pattern) (guard : d370015 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370015, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d370015, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369926 p = 1 := by simpa only [d370015, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47906 p hg
    simpa only [d370015, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47908 (p : Pattern) (guard : d369927 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369926 p = 1 := by simpa only [d369927, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47739 p hg
    simpa only [d369927, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369927, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369927, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47909 (p : Pattern) (guard : d370016 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d370015 p = 1 := by simpa only [d370016, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47907 p hg
    simpa only [d370016, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369927 p = 1 := by simpa only [d370016, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47908 p hg
    simpa only [d370016, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47910 (p : Pattern) (guard : d369926 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46793 p hg
    simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46055 p = 1 := by simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47568 p hg
    simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47911 (p : Pattern) (guard : d369927 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369926 p = 1 := by simpa only [d369927, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47910 p hg
    simpa only [d369927, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369927, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369927, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47912 (p : Pattern) (guard : d369928 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369927 p = 1 := by simpa only [d369928, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47911 p hg
    simpa only [d369928, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369928, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369928, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47913 (p : Pattern) (guard : d370017 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d370016 p = 1 := by simpa only [d370017, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47909 p hg
    simpa only [d370017, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369928 p = 1 := by simpa only [d370017, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47912 p hg
    simpa only [d370017, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47914 (p : Pattern) (guard : d370018 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d370017 p = 1 := by simpa only [d370018, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47913 p hg
    simpa only [d370018, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370018, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d370018, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47915 (p : Pattern) (guard : d369931 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47558 p hg
    simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369690 p = 1 := by simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47588 p hg
    simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47916 (p : Pattern) (guard : d370019 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370019, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d370019, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369931 p = 1 := by simpa only [d370019, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47915 p hg
    simpa only [d370019, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47917 (p : Pattern) (guard : d369932 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369931 p = 1 := by simpa only [d369932, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47744 p hg
    simpa only [d369932, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369932, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369932, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47918 (p : Pattern) (guard : d370020 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d370019 p = 1 := by simpa only [d370020, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47916 p hg
    simpa only [d370020, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369932 p = 1 := by simpa only [d370020, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47917 p hg
    simpa only [d370020, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47919 (p : Pattern) (guard : d369931 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47568 p hg
    simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369690 p = 1 := by simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47594 p hg
    simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47920 (p : Pattern) (guard : d369932 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369931 p = 1 := by simpa only [d369932, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47919 p hg
    simpa only [d369932, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369932, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369932, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47921 (p : Pattern) (guard : d369933 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369932 p = 1 := by simpa only [d369933, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47920 p hg
    simpa only [d369933, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369933, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369933, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47922 (p : Pattern) (guard : d370021 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d370020 p = 1 := by simpa only [d370021, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47918 p hg
    simpa only [d370021, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369933 p = 1 := by simpa only [d370021, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47921 p hg
    simpa only [d370021, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47923 (p : Pattern) (guard : d370022 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d370021 p = 1 := by simpa only [d370022, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47922 p hg
    simpa only [d370022, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370022, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d370022, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47924 (p : Pattern) (guard : d370023 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d370018 p = 1 := by simpa only [d370023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47914 p hg
    simpa only [d370023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370022 p = 1 := by simpa only [d370023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47923 p hg
    simpa only [d370023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47925 (p : Pattern) (guard : d370024 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d370022 p = 1 := by simpa only [d370024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47923 p hg
    simpa only [d370024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369786 p = 1 := by simpa only [d370024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47599 p hg
    simpa only [d370024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47926 (p : Pattern) (guard : d370025 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d370023 p = 1 := by simpa only [d370025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47924 p hg
    simpa only [d370025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370024 p = 1 := by simpa only [d370025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47925 p hg
    simpa only [d370025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47927 (p : Pattern) (guard : d369855 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46995 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46776 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47928 (p : Pattern) (guard : d370026 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370026, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d370026, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369855 p = 1 := by simpa only [d370026, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47927 p hg
    simpa only [d370026, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47929 (p : Pattern) (guard : d369856 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369855 p = 1 := by simpa only [d369856, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47668 p hg
    simpa only [d369856, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369856, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369856, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47930 (p : Pattern) (guard : d370027 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d370026 p = 1 := by simpa only [d370027, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47928 p hg
    simpa only [d370027, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369856 p = 1 := by simpa only [d370027, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47929 p hg
    simpa only [d370027, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47931 (p : Pattern) (guard : d369855 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47017 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46793 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47932 (p : Pattern) (guard : d369856 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369855 p = 1 := by simpa only [d369856, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47931 p hg
    simpa only [d369856, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369856, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369856, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47933 (p : Pattern) (guard : d369857 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369856 p = 1 := by simpa only [d369857, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47932 p hg
    simpa only [d369857, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369857, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369857, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47934 (p : Pattern) (guard : d370028 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d370027 p = 1 := by simpa only [d370028, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47930 p hg
    simpa only [d370028, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369857 p = 1 := by simpa only [d370028, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47933 p hg
    simpa only [d370028, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47935 (p : Pattern) (guard : d370029 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d370028 p = 1 := by simpa only [d370029, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47934 p hg
    simpa only [d370029, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370029, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d370029, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47936 (p : Pattern) (guard : d370030 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369786 p = 1 := by simpa only [d370030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47599 p hg
    simpa only [d370030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370029 p = 1 := by simpa only [d370030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47935 p hg
    simpa only [d370030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47937 (p : Pattern) (guard : d370031 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369782 p = 1 := by simpa only [d370031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47586 p hg
    simpa only [d370031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370030 p = 1 := by simpa only [d370031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47936 p hg
    simpa only [d370031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47938 (p : Pattern) (guard : d370032 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d370025 p = 1 := by simpa only [d370032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47926 p hg
    simpa only [d370032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370031 p = 1 := by simpa only [d370032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47937 p hg
    simpa only [d370032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47939 (p : Pattern) (guard : d370033 p = 1) : d50734 p ≤ (1 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370033, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d370033, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370032 p = 1 := by simpa only [d370033, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47938 p hg
    simpa only [d370033, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47940 (p : Pattern) (guard : d370034 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370034, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d370034, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370033 p = 1 := by simpa only [d370034, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47939 p hg
    simpa only [d370034, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47941 (p : Pattern) (guard : d370035 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d370029 p = 1 := by simpa only [d370035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47935 p hg
    simpa only [d370035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46800 p hg
    simpa only [d370035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47942 (p : Pattern) (guard : d370036 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d370030 p = 1 := by simpa only [d370036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47936 p hg
    simpa only [d370036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370035 p = 1 := by simpa only [d370036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47941 p hg
    simpa only [d370036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47943 (p : Pattern) (guard : d370037 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d370031 p = 1 := by simpa only [d370037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47937 p hg
    simpa only [d370037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370036 p = 1 := by simpa only [d370037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47942 p hg
    simpa only [d370037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47944 (p : Pattern) (guard : d370038 p = 1) : d50734 p ≤ (1 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370038, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d370038, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370037 p = 1 := by simpa only [d370038, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47943 p hg
    simpa only [d370038, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47945 (p : Pattern) (guard : d370039 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370039, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d370039, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370038 p = 1 := by simpa only [d370039, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47944 p hg
    simpa only [d370039, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47946 (p : Pattern) (guard : d370040 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d370034 p = 1 := by simpa only [d370040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47940 p hg
    simpa only [d370040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370039 p = 1 := by simpa only [d370040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47945 p hg
    simpa only [d370040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47947 (p : Pattern) (guard : d370041 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369578 p = 1 := by simpa only [d370041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47268 p hg
    simpa only [d370041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370029 p = 1 := by simpa only [d370041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47935 p hg
    simpa only [d370041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47948 (p : Pattern) (guard : d370042 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d370041 p = 1 := by simpa only [d370042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47947 p hg
    simpa only [d370042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370035 p = 1 := by simpa only [d370042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47941 p hg
    simpa only [d370042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47949 (p : Pattern) (guard : d370043 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d370031 p = 1 := by simpa only [d370043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47937 p hg
    simpa only [d370043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370042 p = 1 := by simpa only [d370043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47948 p hg
    simpa only [d370043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47950 (p : Pattern) (guard : d370044 p = 1) : d50734 p ≤ (1 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370044, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d370044, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370043 p = 1 := by simpa only [d370044, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47949 p hg
    simpa only [d370044, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47951 (p : Pattern) (guard : d370045 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370045, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d370045, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370044 p = 1 := by simpa only [d370045, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47950 p hg
    simpa only [d370045, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47952 (p : Pattern) (guard : d370046 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d370035 p = 1 := by simpa only [d370046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47941 p hg
    simpa only [d370046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46800 p hg
    simpa only [d370046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47953 (p : Pattern) (guard : d370047 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d370042 p = 1 := by simpa only [d370047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47948 p hg
    simpa only [d370047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370046 p = 1 := by simpa only [d370047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47952 p hg
    simpa only [d370047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47954 (p : Pattern) (guard : d370048 p = 1) : d50734 p ≤ (1 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370048, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d370048, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370047 p = 1 := by simpa only [d370048, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47953 p hg
    simpa only [d370048, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47955 (p : Pattern) (guard : d370049 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370049, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d370049, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370048 p = 1 := by simpa only [d370049, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47954 p hg
    simpa only [d370049, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47956 (p : Pattern) (guard : d370050 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d370045 p = 1 := by simpa only [d370050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47951 p hg
    simpa only [d370050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370049 p = 1 := by simpa only [d370050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47955 p hg
    simpa only [d370050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47957 (p : Pattern) (guard : d370051 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d370040 p = 1 := by simpa only [d370051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47946 p hg
    simpa only [d370051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370050 p = 1 := by simpa only [d370051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47956 p hg
    simpa only [d370051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47958 (p : Pattern) (guard : d370052 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d370051 p = 1 := by simpa only [d370052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47957 p hg
    simpa only [d370052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d370052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47959 (p : Pattern) (guard : d370053 p = 1) : d50737 p ≤ (1 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d370052 p = 1 := by simpa only [d370053, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47958 p hg
    simpa only [d370053, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370053, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d370053, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47960 (p : Pattern) (guard : d370054 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370054, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d370054, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370053 p = 1 := by simpa only [d370054, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47959 p hg
    simpa only [d370054, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47961 (p : Pattern) (guard : d370055 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d370049 p = 1 := by simpa only [d370055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47955 p hg
    simpa only [d370055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d370055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47962 (p : Pattern) (guard : d370056 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d370050 p = 1 := by simpa only [d370056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47956 p hg
    simpa only [d370056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370055 p = 1 := by simpa only [d370056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47961 p hg
    simpa only [d370056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47963 (p : Pattern) (guard : d370057 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d370056 p = 1 := by simpa only [d370057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47962 p hg
    simpa only [d370057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d370057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47964 (p : Pattern) (guard : d370058 p = 1) : d50737 p ≤ (1 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d370057 p = 1 := by simpa only [d370058, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47963 p hg
    simpa only [d370058, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370058, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d370058, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47965 (p : Pattern) (guard : d370059 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370059, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d370059, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370058 p = 1 := by simpa only [d370059, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47964 p hg
    simpa only [d370059, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47966 (p : Pattern) (guard : d370060 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d370054 p = 1 := by simpa only [d370060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47960 p hg
    simpa only [d370060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370059 p = 1 := by simpa only [d370060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47965 p hg
    simpa only [d370060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47967 (p : Pattern) (guard : d370061 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d370060 p = 1 := by simpa only [d370061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47966 p hg
    simpa only [d370061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47968 (p : Pattern) (guard : d370062 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d370061 p = 1 := by simpa only [d370062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47967 p hg
    simpa only [d370062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47969 (p : Pattern) (guard : d370063 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d370062 p = 1 := by simpa only [d370063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47968 p hg
    simpa only [d370063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47970 (p : Pattern) (guard : d370064 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d370055 p = 1 := by simpa only [d370064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47961 p hg
    simpa only [d370064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d370064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47971 (p : Pattern) (guard : d370065 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d370064 p = 1 := by simpa only [d370065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47970 p hg
    simpa only [d370065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d370065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47972 (p : Pattern) (guard : d370066 p = 1) : d50737 p ≤ (1 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d370065 p = 1 := by simpa only [d370066, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47971 p hg
    simpa only [d370066, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370066, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d370066, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47973 (p : Pattern) (guard : d370067 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370067, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d370067, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370066 p = 1 := by simpa only [d370067, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47972 p hg
    simpa only [d370067, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47974 (p : Pattern) (guard : d370068 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d370059 p = 1 := by simpa only [d370068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47965 p hg
    simpa only [d370068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370067 p = 1 := by simpa only [d370068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47973 p hg
    simpa only [d370068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47975 (p : Pattern) (guard : d370069 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d370068 p = 1 := by simpa only [d370069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47974 p hg
    simpa only [d370069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47976 (p : Pattern) (guard : d370070 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d370069 p = 1 := by simpa only [d370070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47975 p hg
    simpa only [d370070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47977 (p : Pattern) (guard : d370071 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d370070 p = 1 := by simpa only [d370071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47976 p hg
    simpa only [d370071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47978 (p : Pattern) (guard : d370072 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d370063 p = 1 := by simpa only [d370072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47969 p hg
    simpa only [d370072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370071 p = 1 := by simpa only [d370072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47977 p hg
    simpa only [d370072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47979 (p : Pattern) (guard : d370073 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d370072 p = 1 := by simpa only [d370073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47978 p hg
    simpa only [d370073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47980 (p : Pattern) (guard : d370074 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d370059 p = 1 := by simpa only [d370074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47965 p hg
    simpa only [d370074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47981 (p : Pattern) (guard : d370075 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d370074 p = 1 := by simpa only [d370075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47980 p hg
    simpa only [d370075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47982 (p : Pattern) (guard : d370076 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d370075 p = 1 := by simpa only [d370076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47981 p hg
    simpa only [d370076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47983 (p : Pattern) (guard : d370077 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d370076 p = 1 := by simpa only [d370077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47982 p hg
    simpa only [d370077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47984 (p : Pattern) (guard : d370078 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d370077 p = 1 := by simpa only [d370078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47983 p hg
    simpa only [d370078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47985 (p : Pattern) (guard : d370079 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d370078 p = 1 := by simpa only [d370079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47984 p hg
    simpa only [d370079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47986 (p : Pattern) (guard : d370080 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d370073 p = 1 := by simpa only [d370080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47979 p hg
    simpa only [d370080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370079 p = 1 := by simpa only [d370080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47985 p hg
    simpa only [d370080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47987 (p : Pattern) (guard : d370081 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370080 p = 1 := by simpa only [d370081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47986 p hg
    simpa only [d370081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47988 (p : Pattern) (guard : d370082 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370081 p = 1 := by simpa only [d370082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47987 p hg
    simpa only [d370082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47989 (p : Pattern) (guard : d370083 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370083, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d370083, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370082 p = 1 := by simpa only [d370083, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47988 p hg
    simpa only [d370083, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47990 (p : Pattern) (guard : d370084 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d370084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370083 p = 1 := by simpa only [d370084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47989 p hg
    simpa only [d370084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47991 (p : Pattern) (guard : d370085 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d370067 p = 1 := by simpa only [d370085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47973 p hg
    simpa only [d370085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47992 (p : Pattern) (guard : d370086 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d370085 p = 1 := by simpa only [d370086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47991 p hg
    simpa only [d370086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47993 (p : Pattern) (guard : d370087 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d370086 p = 1 := by simpa only [d370087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47992 p hg
    simpa only [d370087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47994 (p : Pattern) (guard : d370088 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d370087 p = 1 := by simpa only [d370088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47993 p hg
    simpa only [d370088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47995 (p : Pattern) (guard : d370089 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d370088 p = 1 := by simpa only [d370089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47994 p hg
    simpa only [d370089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47996 (p : Pattern) (guard : d370090 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370089 p = 1 := by simpa only [d370090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47995 p hg
    simpa only [d370090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47997 (p : Pattern) (guard : d370091 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d370090 p = 1 := by simpa only [d370091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47996 p hg
    simpa only [d370091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47998 (p : Pattern) (guard : d370092 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370091 p = 1 := by simpa only [d370092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47997 p hg
    simpa only [d370092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47999 (p : Pattern) (guard : d370093 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d370093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370092 p = 1 := by simpa only [d370093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47998 p hg
    simpa only [d370093, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
