import NetHack.Soko22Hazard87.Compare051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13000 (p : Pattern) (guard : d161069 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161068 p = 1 := by simpa only [d161069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12999 p hg
    simpa only [d161069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13001 (p : Pattern) (guard : d161070 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161069 p = 1 := by simpa only [d161070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13000 p hg
    simpa only [d161070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13002 (p : Pattern) (guard : d161071 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161070 p = 1 := by simpa only [d161071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13001 p hg
    simpa only [d161071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13003 (p : Pattern) (guard : d161072 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161071 p = 1 := by simpa only [d161072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13002 p hg
    simpa only [d161072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13004 (p : Pattern) (guard : d161073 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161072 p = 1 := by simpa only [d161073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13003 p hg
    simpa only [d161073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13005 (p : Pattern) (guard : d161074 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161073 p = 1 := by simpa only [d161074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13004 p hg
    simpa only [d161074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13006 (p : Pattern) (guard : d161075 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d161049 p = 1 := by simpa only [d161075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12909 p hg
    simpa only [d161075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161074 p = 1 := by simpa only [d161075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13005 p hg
    simpa only [d161075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13007 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d321, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8298 p hg
    simpa only [d321, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13008 (p : Pattern) (guard : d322 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13007 p hg
    simpa only [d322, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d322, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13009 (p : Pattern) (guard : d160000 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13008 p hg
    simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13010 (p : Pattern) (guard : d160001 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160000 p = 1 := by simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13009 p hg
    simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13011 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d753, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8490 p hg
    simpa only [d753, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13012 (p : Pattern) (guard : d754 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13011 p hg
    simpa only [d754, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d754, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13013 (p : Pattern) (guard : d160106 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13012 p hg
    simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13014 (p : Pattern) (guard : d160107 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160106 p = 1 := by simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13013 p hg
    simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13015 (p : Pattern) (guard : d160108 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160001 p = 1 := by simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13010 p hg
    simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160107 p = 1 := by simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13014 p hg
    simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13016 (p : Pattern) (guard : d160109 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160109, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d160109, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160108 p = 1 := by simpa only [d160109, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13015 p hg
    simpa only [d160109, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13017 (p : Pattern) (guard : d160110 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160110, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d160110, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160109 p = 1 := by simpa only [d160110, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13016 p hg
    simpa only [d160110, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13018 (p : Pattern) (guard : d160111 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160107 p = 1 := by simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13014 p hg
    simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13019 (p : Pattern) (guard : d160112 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160112, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d160112, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160111 p = 1 := by simpa only [d160112, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13018 p hg
    simpa only [d160112, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13020 (p : Pattern) (guard : d160113 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160113, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d160113, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160112 p = 1 := by simpa only [d160113, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13019 p hg
    simpa only [d160113, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13021 (p : Pattern) (guard : d160114 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160110 p = 1 := by simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13017 p hg
    simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160113 p = 1 := by simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13020 p hg
    simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13022 (p : Pattern) (guard : d160115 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160113 p = 1 := by simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13020 p hg
    simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13023 (p : Pattern) (guard : d160116 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160114 p = 1 := by simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13021 p hg
    simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160115 p = 1 := by simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13022 p hg
    simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13024 (p : Pattern) (guard : d160117 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160116 p = 1 := by simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13023 p hg
    simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13025 (p : Pattern) (guard : d160118 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160117 p = 1 := by simpa only [d160118, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13024 p hg
    simpa only [d160118, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160118, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d160118, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13026 (p : Pattern) (guard : d160119 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160119, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160119, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160118 p = 1 := by simpa only [d160119, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13025 p hg
    simpa only [d160119, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13027 (p : Pattern) (guard : d160120 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160115 p = 1 := by simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13022 p hg
    simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13028 (p : Pattern) (guard : d160121 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160120 p = 1 := by simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13027 p hg
    simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13029 (p : Pattern) (guard : d160122 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160121 p = 1 := by simpa only [d160122, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13028 p hg
    simpa only [d160122, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160122, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d160122, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13030 (p : Pattern) (guard : d160123 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160123, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160123, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160122 p = 1 := by simpa only [d160123, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13029 p hg
    simpa only [d160123, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13031 (p : Pattern) (guard : d160124 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160119 p = 1 := by simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13026 p hg
    simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160123 p = 1 := by simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13030 p hg
    simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13032 (p : Pattern) (guard : d160125 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160124 p = 1 := by simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13031 p hg
    simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13033 (p : Pattern) (guard : d160126 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160125 p = 1 := by simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13032 p hg
    simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13034 (p : Pattern) (guard : d160127 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160126 p = 1 := by simpa only [d160127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13033 p hg
    simpa only [d160127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13035 (p : Pattern) (guard : d160128 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160123 p = 1 := by simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13030 p hg
    simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13036 (p : Pattern) (guard : d160129 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160128 p = 1 := by simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13035 p hg
    simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13037 (p : Pattern) (guard : d160130 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160129 p = 1 := by simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13036 p hg
    simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13038 (p : Pattern) (guard : d160131 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160130 p = 1 := by simpa only [d160131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13037 p hg
    simpa only [d160131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13039 (p : Pattern) (guard : d160132 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160127 p = 1 := by simpa only [d160132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13034 p hg
    simpa only [d160132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160131 p = 1 := by simpa only [d160132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13038 p hg
    simpa only [d160132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13040 (p : Pattern) (guard : d160133 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160132 p = 1 := by simpa only [d160133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13039 p hg
    simpa only [d160133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13041 (p : Pattern) (guard : d160134 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160133 p = 1 := by simpa only [d160134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13040 p hg
    simpa only [d160134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13042 (p : Pattern) (guard : d160135 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160134 p = 1 := by simpa only [d160135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13041 p hg
    simpa only [d160135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13043 (p : Pattern) (guard : d160136 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160135 p = 1 := by simpa only [d160136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13042 p hg
    simpa only [d160136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13044 (p : Pattern) (guard : d160137 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160136 p = 1 := by simpa only [d160137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13043 p hg
    simpa only [d160137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13045 (p : Pattern) (guard : d160140 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160126 p = 1 := by simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13033 p hg
    simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13046 (p : Pattern) (guard : d160141 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160130 p = 1 := by simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13037 p hg
    simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13047 (p : Pattern) (guard : d160142 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160140 p = 1 := by simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13045 p hg
    simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160141 p = 1 := by simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13046 p hg
    simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13048 (p : Pattern) (guard : d160143 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160142 p = 1 := by simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13047 p hg
    simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13049 (p : Pattern) (guard : d160144 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160143 p = 1 := by simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13048 p hg
    simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13050 (p : Pattern) (guard : d160145 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160144 p = 1 := by simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13049 p hg
    simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13051 (p : Pattern) (guard : d160146 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160145 p = 1 := by simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13050 p hg
    simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13052 (p : Pattern) (guard : d160147 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160136 p = 1 := by simpa only [d160147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13043 p hg
    simpa only [d160147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160146 p = 1 := by simpa only [d160147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13051 p hg
    simpa only [d160147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13053 (p : Pattern) (guard : d160148 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160137 p = 1 := by simpa only [d160148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13044 p hg
    simpa only [d160148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160147 p = 1 := by simpa only [d160148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13052 p hg
    simpa only [d160148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13054 (p : Pattern) (guard : d160149 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160148 p = 1 := by simpa only [d160149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13053 p hg
    simpa only [d160149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13055 (p : Pattern) (guard : d161076 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160149 p = 1 := by simpa only [d161076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13054 p hg
    simpa only [d161076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13056 (p : Pattern) (guard : d161077 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161076 p = 1 := by simpa only [d161077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13055 p hg
    simpa only [d161077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13057 (p : Pattern) (guard : d321 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d321, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8356 p hg
    simpa only [d321, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13058 (p : Pattern) (guard : d322 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13057 p hg
    simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13059 (p : Pattern) (guard : d160000 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13058 p hg
    simpa only [d160000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13060 (p : Pattern) (guard : d160001 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160000 p = 1 := by simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13059 p hg
    simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13061 (p : Pattern) (guard : d753 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d753, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8562 p hg
    simpa only [d753, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13062 (p : Pattern) (guard : d754 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13061 p hg
    simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13063 (p : Pattern) (guard : d160106 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13062 p hg
    simpa only [d160106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13064 (p : Pattern) (guard : d160107 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160106 p = 1 := by simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13063 p hg
    simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13065 (p : Pattern) (guard : d160108 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160001 p = 1 := by simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13060 p hg
    simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160107 p = 1 := by simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13064 p hg
    simpa only [d160108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13066 (p : Pattern) (guard : d160109 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160109, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d160109, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160108 p = 1 := by simpa only [d160109, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13065 p hg
    simpa only [d160109, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13067 (p : Pattern) (guard : d160110 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160110, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d160110, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160109 p = 1 := by simpa only [d160110, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13066 p hg
    simpa only [d160110, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13068 (p : Pattern) (guard : d160111 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160107 p = 1 := by simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13064 p hg
    simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13069 (p : Pattern) (guard : d160112 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160112, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d160112, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160111 p = 1 := by simpa only [d160112, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13068 p hg
    simpa only [d160112, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13070 (p : Pattern) (guard : d160113 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160113, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d160113, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160112 p = 1 := by simpa only [d160113, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13069 p hg
    simpa only [d160113, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13071 (p : Pattern) (guard : d160114 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160110 p = 1 := by simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13067 p hg
    simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160113 p = 1 := by simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13070 p hg
    simpa only [d160114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13072 (p : Pattern) (guard : d160115 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160113 p = 1 := by simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13070 p hg
    simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13073 (p : Pattern) (guard : d160116 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160114 p = 1 := by simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13071 p hg
    simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160115 p = 1 := by simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13072 p hg
    simpa only [d160116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13074 (p : Pattern) (guard : d160117 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160116 p = 1 := by simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13073 p hg
    simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13075 (p : Pattern) (guard : d160118 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160117 p = 1 := by simpa only [d160118, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13074 p hg
    simpa only [d160118, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160118, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d160118, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13076 (p : Pattern) (guard : d160119 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d160119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160118 p = 1 := by simpa only [d160119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13075 p hg
    simpa only [d160119, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13077 (p : Pattern) (guard : d160120 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160115 p = 1 := by simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13072 p hg
    simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13078 (p : Pattern) (guard : d160121 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160120 p = 1 := by simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13077 p hg
    simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13079 (p : Pattern) (guard : d160122 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160121 p = 1 := by simpa only [d160122, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13078 p hg
    simpa only [d160122, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160122, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d160122, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13080 (p : Pattern) (guard : d160123 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160123, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d160123, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160122 p = 1 := by simpa only [d160123, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13079 p hg
    simpa only [d160123, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13081 (p : Pattern) (guard : d160124 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160119 p = 1 := by simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13076 p hg
    simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160123 p = 1 := by simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13080 p hg
    simpa only [d160124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13082 (p : Pattern) (guard : d160125 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160124 p = 1 := by simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13081 p hg
    simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13083 (p : Pattern) (guard : d160126 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160125 p = 1 := by simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13082 p hg
    simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13084 (p : Pattern) (guard : d160140 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160126 p = 1 := by simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13083 p hg
    simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13085 (p : Pattern) (guard : d160128 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160123 p = 1 := by simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13080 p hg
    simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13086 (p : Pattern) (guard : d160129 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160128 p = 1 := by simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13085 p hg
    simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13087 (p : Pattern) (guard : d160130 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160129 p = 1 := by simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13086 p hg
    simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13088 (p : Pattern) (guard : d160141 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160130 p = 1 := by simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13087 p hg
    simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13089 (p : Pattern) (guard : d160142 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160140 p = 1 := by simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13084 p hg
    simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160141 p = 1 := by simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13088 p hg
    simpa only [d160142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13090 (p : Pattern) (guard : d160143 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160142 p = 1 := by simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13089 p hg
    simpa only [d160143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13091 (p : Pattern) (guard : d160144 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160143 p = 1 := by simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13090 p hg
    simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13092 (p : Pattern) (guard : d160145 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160144 p = 1 := by simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13091 p hg
    simpa only [d160145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13093 (p : Pattern) (guard : d160146 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160145 p = 1 := by simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13092 p hg
    simpa only [d160146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13094 (p : Pattern) (guard : d161078 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161078, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161078, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160146 p = 1 := by simpa only [d161078, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13093 p hg
    simpa only [d161078, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13095 (p : Pattern) (guard : d161079 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161078 p = 1 := by simpa only [d161079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13094 p hg
    simpa only [d161079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13096 (p : Pattern) (guard : d161080 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161079 p = 1 := by simpa only [d161080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13095 p hg
    simpa only [d161080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13097 (p : Pattern) (guard : d161081 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161080 p = 1 := by simpa only [d161081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13096 p hg
    simpa only [d161081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13098 (p : Pattern) (guard : d161082 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161081 p = 1 := by simpa only [d161082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13097 p hg
    simpa only [d161082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13099 (p : Pattern) (guard : d161083 p = 1) : d47768 p ≤ (-2 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161077 p = 1 := by simpa only [d161083, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13056 p hg
    simpa only [d161083, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161082 p = 1 := by simpa only [d161083, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13098 p hg
    simpa only [d161083, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13100 (p : Pattern) (guard : d412 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d412, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d412, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318 p = 1 := by simpa only [d412, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8405 p hg
    simpa only [d412, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13101 (p : Pattern) (guard : d413 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d412 p = 1 := by simpa only [d413, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13100 p hg
    simpa only [d413, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d319 p = 1 := by simpa only [d413, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8407 p hg
    simpa only [d413, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13102 (p : Pattern) (guard : d414 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d413 p = 1 := by simpa only [d414, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13101 p hg
    simpa only [d414, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d414, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8423 p hg
    simpa only [d414, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13103 (p : Pattern) (guard : d415 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d414 p = 1 := by simpa only [d415, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13102 p hg
    simpa only [d415, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d415, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d415, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13104 (p : Pattern) (guard : d160061 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d415 p = 1 := by simpa only [d160061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13103 p hg
    simpa only [d160061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13105 (p : Pattern) (guard : d160062 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160061 p = 1 := by simpa only [d160062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13104 p hg
    simpa only [d160062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13106 (p : Pattern) (guard : d971 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d971, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d971, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d750 p = 1 := by simpa only [d971, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8643 p hg
    simpa only [d971, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13107 (p : Pattern) (guard : d972 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d971 p = 1 := by simpa only [d972, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13106 p hg
    simpa only [d972, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d751 p = 1 := by simpa only [d972, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8645 p hg
    simpa only [d972, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13108 (p : Pattern) (guard : d973 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d972 p = 1 := by simpa only [d973, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13107 p hg
    simpa only [d973, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d973, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8649 p hg
    simpa only [d973, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13109 (p : Pattern) (guard : d974 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d973 p = 1 := by simpa only [d974, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13108 p hg
    simpa only [d974, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d974, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d974, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13110 (p : Pattern) (guard : d160247 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d974 p = 1 := by simpa only [d160247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13109 p hg
    simpa only [d160247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13111 (p : Pattern) (guard : d160248 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160247 p = 1 := by simpa only [d160248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13110 p hg
    simpa only [d160248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13112 (p : Pattern) (guard : d160249 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160062 p = 1 := by simpa only [d160249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13105 p hg
    simpa only [d160249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160248 p = 1 := by simpa only [d160249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13111 p hg
    simpa only [d160249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13113 (p : Pattern) (guard : d160250 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160250, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d160250, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160249 p = 1 := by simpa only [d160250, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13112 p hg
    simpa only [d160250, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13114 (p : Pattern) (guard : d160251 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160251, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d160251, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160250 p = 1 := by simpa only [d160251, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13113 p hg
    simpa only [d160251, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13115 (p : Pattern) (guard : d160253 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160248 p = 1 := by simpa only [d160253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13111 p hg
    simpa only [d160253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13116 (p : Pattern) (guard : d160254 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160254, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d160254, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160253 p = 1 := by simpa only [d160254, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13115 p hg
    simpa only [d160254, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13117 (p : Pattern) (guard : d160255 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160255, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d160255, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160254 p = 1 := by simpa only [d160255, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13116 p hg
    simpa only [d160255, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13118 (p : Pattern) (guard : d160256 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160251 p = 1 := by simpa only [d160256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13114 p hg
    simpa only [d160256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160255 p = 1 := by simpa only [d160256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13117 p hg
    simpa only [d160256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13119 (p : Pattern) (guard : d160261 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160255 p = 1 := by simpa only [d160261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13117 p hg
    simpa only [d160261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13120 (p : Pattern) (guard : d160262 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160256 p = 1 := by simpa only [d160262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13118 p hg
    simpa only [d160262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160261 p = 1 := by simpa only [d160262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13119 p hg
    simpa only [d160262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13121 (p : Pattern) (guard : d160263 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160262 p = 1 := by simpa only [d160263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13120 p hg
    simpa only [d160263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13122 (p : Pattern) (guard : d160264 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160263 p = 1 := by simpa only [d160264, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13121 p hg
    simpa only [d160264, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160264, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d160264, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13123 (p : Pattern) (guard : d160265 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160265, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160265, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160264 p = 1 := by simpa only [d160265, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13122 p hg
    simpa only [d160265, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13124 (p : Pattern) (guard : d160270 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160261 p = 1 := by simpa only [d160270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13119 p hg
    simpa only [d160270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13125 (p : Pattern) (guard : d160271 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160270 p = 1 := by simpa only [d160271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13124 p hg
    simpa only [d160271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13126 (p : Pattern) (guard : d160272 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160271 p = 1 := by simpa only [d160272, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13125 p hg
    simpa only [d160272, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160272, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d160272, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13127 (p : Pattern) (guard : d160273 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160273, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160273, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160272 p = 1 := by simpa only [d160273, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13126 p hg
    simpa only [d160273, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13128 (p : Pattern) (guard : d160274 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160265 p = 1 := by simpa only [d160274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13123 p hg
    simpa only [d160274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160273 p = 1 := by simpa only [d160274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13127 p hg
    simpa only [d160274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13129 (p : Pattern) (guard : d160275 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160274 p = 1 := by simpa only [d160275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13128 p hg
    simpa only [d160275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13130 (p : Pattern) (guard : d160276 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160275 p = 1 := by simpa only [d160276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13129 p hg
    simpa only [d160276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13131 (p : Pattern) (guard : d160277 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160276 p = 1 := by simpa only [d160277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13130 p hg
    simpa only [d160277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13132 (p : Pattern) (guard : d160291 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160273 p = 1 := by simpa only [d160291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13127 p hg
    simpa only [d160291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13133 (p : Pattern) (guard : d160292 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160291 p = 1 := by simpa only [d160292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13132 p hg
    simpa only [d160292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13134 (p : Pattern) (guard : d160293 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160292 p = 1 := by simpa only [d160293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13133 p hg
    simpa only [d160293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13135 (p : Pattern) (guard : d160294 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160293 p = 1 := by simpa only [d160294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13134 p hg
    simpa only [d160294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13136 (p : Pattern) (guard : d161084 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160277 p = 1 := by simpa only [d161084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13131 p hg
    simpa only [d161084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160294 p = 1 := by simpa only [d161084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13135 p hg
    simpa only [d161084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13137 (p : Pattern) (guard : d161085 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161084 p = 1 := by simpa only [d161085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13136 p hg
    simpa only [d161085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13138 (p : Pattern) (guard : d161086 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d161085 p = 1 := by simpa only [d161086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13137 p hg
    simpa only [d161086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13139 (p : Pattern) (guard : d161087 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161086 p = 1 := by simpa only [d161087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13138 p hg
    simpa only [d161087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13140 (p : Pattern) (guard : d161088 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161087 p = 1 := by simpa only [d161088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13139 p hg
    simpa only [d161088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13141 (p : Pattern) (guard : d161089 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161089, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161089, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161088 p = 1 := by simpa only [d161089, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13140 p hg
    simpa only [d161089, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13142 (p : Pattern) (guard : d161090 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161089 p = 1 := by simpa only [d161090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13141 p hg
    simpa only [d161090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13143 (p : Pattern) (guard : d161091 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161090 p = 1 := by simpa only [d161091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13142 p hg
    simpa only [d161091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13144 (p : Pattern) (guard : d161092 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161091 p = 1 := by simpa only [d161092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13143 p hg
    simpa only [d161092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13145 (p : Pattern) (guard : d161093 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161092 p = 1 := by simpa only [d161093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13144 p hg
    simpa only [d161093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13146 (p : Pattern) (guard : d161094 p = 1) : d47865 p ≤ (-2 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161093 p = 1 := by simpa only [d161094, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13145 p hg
    simpa only [d161094, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161094, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12901 p hg
    simpa only [d161094, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13147 (p : Pattern) (guard : d161095 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d161083 p = 1 := by simpa only [d161095, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13099 p hg
    simpa only [d161095, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161094 p = 1 := by simpa only [d161095, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13146 p hg
    simpa only [d161095, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13148 (p : Pattern) (guard : d161096 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161095 p = 1 := by simpa only [d161096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13147 p hg
    simpa only [d161096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13149 (p : Pattern) (guard : d161097 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161096 p = 1 := by simpa only [d161097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13148 p hg
    simpa only [d161097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13150 (p : Pattern) (guard : d161098 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161097 p = 1 := by simpa only [d161098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13149 p hg
    simpa only [d161098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13151 (p : Pattern) (guard : d161099 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161098 p = 1 := by simpa only [d161099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13150 p hg
    simpa only [d161099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13152 (p : Pattern) (guard : d161100 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161099 p = 1 := by simpa only [d161100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13151 p hg
    simpa only [d161100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13153 (p : Pattern) (guard : d161101 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161100 p = 1 := by simpa only [d161101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13152 p hg
    simpa only [d161101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13154 (p : Pattern) (guard : d161102 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161101 p = 1 := by simpa only [d161102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13153 p hg
    simpa only [d161102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13155 (p : Pattern) (guard : d161103 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d161075 p = 1 := by simpa only [d161103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13006 p hg
    simpa only [d161103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161102 p = 1 := by simpa only [d161103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13154 p hg
    simpa only [d161103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13156 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d1112, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8739 p hg
    simpa only [d1112, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13157 (p : Pattern) (guard : d1113 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13156 p hg
    simpa only [d1113, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d1113, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13158 (p : Pattern) (guard : d160315 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13157 p hg
    simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13159 (p : Pattern) (guard : d160316 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160315 p = 1 := by simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13158 p hg
    simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13160 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d1123, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8750 p hg
    simpa only [d1123, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13161 (p : Pattern) (guard : d1124 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13160 p hg
    simpa only [d1124, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d1124, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13162 (p : Pattern) (guard : d160317 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13161 p hg
    simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13163 (p : Pattern) (guard : d160318 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160317 p = 1 := by simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13162 p hg
    simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13164 (p : Pattern) (guard : d160319 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160316 p = 1 := by simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13159 p hg
    simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160318 p = 1 := by simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13163 p hg
    simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13165 (p : Pattern) (guard : d160320 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160320, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d160320, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160319 p = 1 := by simpa only [d160320, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13164 p hg
    simpa only [d160320, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13166 (p : Pattern) (guard : d160321 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160321, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d160321, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160320 p = 1 := by simpa only [d160321, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13165 p hg
    simpa only [d160321, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13167 (p : Pattern) (guard : d160322 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160318 p = 1 := by simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13163 p hg
    simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13168 (p : Pattern) (guard : d160323 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160323, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d160323, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160322 p = 1 := by simpa only [d160323, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13167 p hg
    simpa only [d160323, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13169 (p : Pattern) (guard : d160324 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160324, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d160324, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160323 p = 1 := by simpa only [d160324, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13168 p hg
    simpa only [d160324, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13170 (p : Pattern) (guard : d160325 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160321 p = 1 := by simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13166 p hg
    simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160324 p = 1 := by simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13169 p hg
    simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13171 (p : Pattern) (guard : d160326 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160324 p = 1 := by simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13169 p hg
    simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13172 (p : Pattern) (guard : d160327 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160325 p = 1 := by simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13170 p hg
    simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160326 p = 1 := by simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13171 p hg
    simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13173 (p : Pattern) (guard : d160328 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160327 p = 1 := by simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13172 p hg
    simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13174 (p : Pattern) (guard : d160329 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160328 p = 1 := by simpa only [d160329, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13173 p hg
    simpa only [d160329, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160329, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d160329, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13175 (p : Pattern) (guard : d160330 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160330, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160330, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160329 p = 1 := by simpa only [d160330, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13174 p hg
    simpa only [d160330, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13176 (p : Pattern) (guard : d160331 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160326 p = 1 := by simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13171 p hg
    simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13177 (p : Pattern) (guard : d160332 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160331 p = 1 := by simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13176 p hg
    simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13178 (p : Pattern) (guard : d160333 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160332 p = 1 := by simpa only [d160333, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13177 p hg
    simpa only [d160333, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160333, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d160333, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13179 (p : Pattern) (guard : d160334 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160334, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160334, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160333 p = 1 := by simpa only [d160334, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13178 p hg
    simpa only [d160334, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13180 (p : Pattern) (guard : d160335 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160330 p = 1 := by simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13175 p hg
    simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160334 p = 1 := by simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13179 p hg
    simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13181 (p : Pattern) (guard : d160336 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160335 p = 1 := by simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13180 p hg
    simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13182 (p : Pattern) (guard : d160337 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160336 p = 1 := by simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13181 p hg
    simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13183 (p : Pattern) (guard : d160338 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160337 p = 1 := by simpa only [d160338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13182 p hg
    simpa only [d160338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13184 (p : Pattern) (guard : d160339 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160334 p = 1 := by simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13179 p hg
    simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13185 (p : Pattern) (guard : d160340 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160339 p = 1 := by simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13184 p hg
    simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13186 (p : Pattern) (guard : d160341 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160340 p = 1 := by simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13185 p hg
    simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13187 (p : Pattern) (guard : d160342 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160341 p = 1 := by simpa only [d160342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13186 p hg
    simpa only [d160342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13188 (p : Pattern) (guard : d160343 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160338 p = 1 := by simpa only [d160343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13183 p hg
    simpa only [d160343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160342 p = 1 := by simpa only [d160343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13187 p hg
    simpa only [d160343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13189 (p : Pattern) (guard : d160344 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160343 p = 1 := by simpa only [d160344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13188 p hg
    simpa only [d160344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13190 (p : Pattern) (guard : d160345 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160344 p = 1 := by simpa only [d160345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13189 p hg
    simpa only [d160345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13191 (p : Pattern) (guard : d160346 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160345 p = 1 := by simpa only [d160346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13190 p hg
    simpa only [d160346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13192 (p : Pattern) (guard : d160347 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160346 p = 1 := by simpa only [d160347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13191 p hg
    simpa only [d160347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13193 (p : Pattern) (guard : d160348 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160347 p = 1 := by simpa only [d160348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13192 p hg
    simpa only [d160348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13194 (p : Pattern) (guard : d160351 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160337 p = 1 := by simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13182 p hg
    simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13195 (p : Pattern) (guard : d160352 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160341 p = 1 := by simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13186 p hg
    simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13196 (p : Pattern) (guard : d160353 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160351 p = 1 := by simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13194 p hg
    simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160352 p = 1 := by simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13195 p hg
    simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13197 (p : Pattern) (guard : d160354 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160353 p = 1 := by simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13196 p hg
    simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13198 (p : Pattern) (guard : d160355 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160354 p = 1 := by simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13197 p hg
    simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13199 (p : Pattern) (guard : d160356 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160355 p = 1 := by simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13198 p hg
    simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13200 (p : Pattern) (guard : d160357 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160356 p = 1 := by simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13199 p hg
    simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13201 (p : Pattern) (guard : d160358 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160347 p = 1 := by simpa only [d160358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13192 p hg
    simpa only [d160358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160357 p = 1 := by simpa only [d160358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13200 p hg
    simpa only [d160358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13202 (p : Pattern) (guard : d160359 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160348 p = 1 := by simpa only [d160359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13193 p hg
    simpa only [d160359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160358 p = 1 := by simpa only [d160359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13201 p hg
    simpa only [d160359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13203 (p : Pattern) (guard : d160360 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160359 p = 1 := by simpa only [d160360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13202 p hg
    simpa only [d160360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13204 (p : Pattern) (guard : d161104 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160360 p = 1 := by simpa only [d161104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13203 p hg
    simpa only [d161104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13205 (p : Pattern) (guard : d161105 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161104 p = 1 := by simpa only [d161105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13204 p hg
    simpa only [d161105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13206 (p : Pattern) (guard : d1112 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d1112, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8847 p hg
    simpa only [d1112, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13207 (p : Pattern) (guard : d1113 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13206 p hg
    simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13208 (p : Pattern) (guard : d160315 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13207 p hg
    simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13209 (p : Pattern) (guard : d160316 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160315 p = 1 := by simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13208 p hg
    simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13210 (p : Pattern) (guard : d1123 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d1123, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8858 p hg
    simpa only [d1123, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13211 (p : Pattern) (guard : d1124 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13210 p hg
    simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13212 (p : Pattern) (guard : d160317 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13211 p hg
    simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13213 (p : Pattern) (guard : d160318 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160317 p = 1 := by simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13212 p hg
    simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13214 (p : Pattern) (guard : d160319 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160316 p = 1 := by simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13209 p hg
    simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160318 p = 1 := by simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13213 p hg
    simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13215 (p : Pattern) (guard : d160320 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160320, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d160320, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160319 p = 1 := by simpa only [d160320, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13214 p hg
    simpa only [d160320, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13216 (p : Pattern) (guard : d160321 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160321, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d160321, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160320 p = 1 := by simpa only [d160321, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13215 p hg
    simpa only [d160321, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13217 (p : Pattern) (guard : d160322 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160318 p = 1 := by simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13213 p hg
    simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13218 (p : Pattern) (guard : d160323 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160323, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d160323, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160322 p = 1 := by simpa only [d160323, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13217 p hg
    simpa only [d160323, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13219 (p : Pattern) (guard : d160324 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160324, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d160324, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160323 p = 1 := by simpa only [d160324, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13218 p hg
    simpa only [d160324, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13220 (p : Pattern) (guard : d160325 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160321 p = 1 := by simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13216 p hg
    simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160324 p = 1 := by simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13219 p hg
    simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13221 (p : Pattern) (guard : d160326 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160324 p = 1 := by simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13219 p hg
    simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13222 (p : Pattern) (guard : d160327 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160325 p = 1 := by simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13220 p hg
    simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160326 p = 1 := by simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13221 p hg
    simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13223 (p : Pattern) (guard : d160328 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160327 p = 1 := by simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13222 p hg
    simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13224 (p : Pattern) (guard : d160329 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160328 p = 1 := by simpa only [d160329, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13223 p hg
    simpa only [d160329, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160329, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d160329, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13225 (p : Pattern) (guard : d160330 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160330, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d160330, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160329 p = 1 := by simpa only [d160330, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13224 p hg
    simpa only [d160330, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13226 (p : Pattern) (guard : d160331 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160326 p = 1 := by simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13221 p hg
    simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13227 (p : Pattern) (guard : d160332 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160331 p = 1 := by simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13226 p hg
    simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13228 (p : Pattern) (guard : d160333 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160332 p = 1 := by simpa only [d160333, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13227 p hg
    simpa only [d160333, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160333, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d160333, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13229 (p : Pattern) (guard : d160334 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160334, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d160334, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160333 p = 1 := by simpa only [d160334, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13228 p hg
    simpa only [d160334, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13230 (p : Pattern) (guard : d160335 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160330 p = 1 := by simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13225 p hg
    simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160334 p = 1 := by simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13229 p hg
    simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13231 (p : Pattern) (guard : d160336 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160335 p = 1 := by simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13230 p hg
    simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13232 (p : Pattern) (guard : d160337 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160336 p = 1 := by simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13231 p hg
    simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13233 (p : Pattern) (guard : d160351 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160337 p = 1 := by simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13232 p hg
    simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13234 (p : Pattern) (guard : d160339 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160334 p = 1 := by simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13229 p hg
    simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13235 (p : Pattern) (guard : d160340 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160339 p = 1 := by simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13234 p hg
    simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13236 (p : Pattern) (guard : d160341 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160340 p = 1 := by simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13235 p hg
    simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13237 (p : Pattern) (guard : d160352 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160341 p = 1 := by simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13236 p hg
    simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13238 (p : Pattern) (guard : d160353 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160351 p = 1 := by simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13233 p hg
    simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160352 p = 1 := by simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13237 p hg
    simpa only [d160353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13239 (p : Pattern) (guard : d160354 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160353 p = 1 := by simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13238 p hg
    simpa only [d160354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13240 (p : Pattern) (guard : d160355 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160354 p = 1 := by simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13239 p hg
    simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13241 (p : Pattern) (guard : d160356 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160355 p = 1 := by simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13240 p hg
    simpa only [d160356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13242 (p : Pattern) (guard : d160357 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160356 p = 1 := by simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13241 p hg
    simpa only [d160357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13243 (p : Pattern) (guard : d161106 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161106, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161106, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160357 p = 1 := by simpa only [d161106, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13242 p hg
    simpa only [d161106, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13244 (p : Pattern) (guard : d161107 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161106 p = 1 := by simpa only [d161107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13243 p hg
    simpa only [d161107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13245 (p : Pattern) (guard : d161108 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161107 p = 1 := by simpa only [d161108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13244 p hg
    simpa only [d161108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13246 (p : Pattern) (guard : d161109 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161108 p = 1 := by simpa only [d161109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13245 p hg
    simpa only [d161109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13247 (p : Pattern) (guard : d161110 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161109 p = 1 := by simpa only [d161110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13246 p hg
    simpa only [d161110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13248 (p : Pattern) (guard : d161111 p = 1) : d47768 p ≤ (-2 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161105 p = 1 := by simpa only [d161111, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13205 p hg
    simpa only [d161111, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161110 p = 1 := by simpa only [d161111, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13247 p hg
    simpa only [d161111, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13249 (p : Pattern) (guard : d1385 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1385, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d1385, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1109 p = 1 := by simpa only [d1385, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8976 p hg
    simpa only [d1385, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
