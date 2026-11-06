/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Range
namespace NetHack.Sokoban41.Diagram
def d785 (pattern : Ten) : Int := if pattern.a then d356 pattern else d1 pattern
theorem range785 (pattern : Ten) : 0 ≤ d785 pattern ∧ d785 pattern ≤ 10 := by
  unfold d785
  split
  · exact range356 pattern
  · exact range1 pattern
def d786 (pattern : Ten) : Int := if pattern.f then d0 pattern else d785 pattern
theorem range786 (pattern : Ten) : 0 ≤ d786 pattern ∧ d786 pattern ≤ 10 := by
  unfold d786
  split
  · exact range0 pattern
  · exact range785 pattern
def d787 (pattern : Ten) : Int := if pattern.j then d359 pattern else d786 pattern
theorem range787 (pattern : Ten) : 0 ≤ d787 pattern ∧ d787 pattern ≤ 10 := by
  unfold d787
  split
  · exact range359 pattern
  · exact range786 pattern
def d788 (pattern : Ten) : Int := if pattern.i then d606 pattern else d787 pattern
theorem range788 (pattern : Ten) : 0 ≤ d788 pattern ∧ d788 pattern ≤ 10 := by
  unfold d788
  split
  · exact range606 pattern
  · exact range787 pattern
def d789 (pattern : Ten) : Int := if pattern.h then d607 pattern else d788 pattern
theorem range789 (pattern : Ten) : 0 ≤ d789 pattern ∧ d789 pattern ≤ 10 := by
  unfold d789
  split
  · exact range607 pattern
  · exact range788 pattern
def d790 (pattern : Ten) : Int := if pattern.g then d608 pattern else d789 pattern
theorem range790 (pattern : Ten) : 0 ≤ d790 pattern ∧ d790 pattern ≤ 10 := by
  unfold d790
  split
  · exact range608 pattern
  · exact range789 pattern
def d791 (pattern : Ten) : Int := if pattern.c then d609 pattern else d790 pattern
theorem range791 (pattern : Ten) : 0 ≤ d791 pattern ∧ d791 pattern ≤ 10 := by
  unfold d791
  split
  · exact range609 pattern
  · exact range790 pattern
def d792 (pattern : Ten) : Int := if pattern.e then d610 pattern else d791 pattern
theorem range792 (pattern : Ten) : 0 ≤ d792 pattern ∧ d792 pattern ≤ 10 := by
  unfold d792
  split
  · exact range610 pattern
  · exact range791 pattern
def d793 (pattern : Ten) : Int := if pattern.d then d611 pattern else d792 pattern
theorem range793 (pattern : Ten) : 0 ≤ d793 pattern ∧ d793 pattern ≤ 10 := by
  unfold d793
  split
  · exact range611 pattern
  · exact range792 pattern
def d794 (pattern : Ten) : Int := if pattern.j then d0 pattern else d358 pattern
theorem range794 (pattern : Ten) : 0 ≤ d794 pattern ∧ d794 pattern ≤ 10 := by
  unfold d794
  split
  · exact range0 pattern
  · exact range358 pattern
def d795 (pattern : Ten) : Int := if pattern.i then d0 pattern else d794 pattern
theorem range795 (pattern : Ten) : 0 ≤ d795 pattern ∧ d795 pattern ≤ 10 := by
  unfold d795
  split
  · exact range0 pattern
  · exact range794 pattern
def d796 (pattern : Ten) : Int := if pattern.h then d0 pattern else d795 pattern
theorem range796 (pattern : Ten) : 0 ≤ d796 pattern ∧ d796 pattern ≤ 10 := by
  unfold d796
  split
  · exact range0 pattern
  · exact range795 pattern
def d797 (pattern : Ten) : Int := if pattern.g then d0 pattern else d796 pattern
theorem range797 (pattern : Ten) : 0 ≤ d797 pattern ∧ d797 pattern ≤ 10 := by
  unfold d797
  split
  · exact range0 pattern
  · exact range796 pattern
def d798 (pattern : Ten) : Int := if pattern.c then d0 pattern else d797 pattern
theorem range798 (pattern : Ten) : 0 ≤ d798 pattern ∧ d798 pattern ≤ 10 := by
  unfold d798
  split
  · exact range0 pattern
  · exact range797 pattern
def d799 (pattern : Ten) : Int := if pattern.e then d0 pattern else d798 pattern
theorem range799 (pattern : Ten) : 0 ≤ d799 pattern ∧ d799 pattern ≤ 10 := by
  unfold d799
  split
  · exact range0 pattern
  · exact range798 pattern
def d800 (pattern : Ten) : Int := if pattern.d then d0 pattern else d799 pattern
theorem range800 (pattern : Ten) : 0 ≤ d800 pattern ∧ d800 pattern ≤ 10 := by
  unfold d800
  split
  · exact range0 pattern
  · exact range799 pattern
def d801 (pattern : Ten) : Int := if pattern.j then d9 pattern else d5 pattern
theorem range801 (pattern : Ten) : 0 ≤ d801 pattern ∧ d801 pattern ≤ 10 := by
  unfold d801
  split
  · exact range9 pattern
  · exact range5 pattern
def d802 (pattern : Ten) : Int := if pattern.i then d801 pattern else d86 pattern
theorem range802 (pattern : Ten) : 0 ≤ d802 pattern ∧ d802 pattern ≤ 10 := by
  unfold d802
  split
  · exact range801 pattern
  · exact range86 pattern
def d803 (pattern : Ten) : Int := if pattern.h then d49 pattern else d802 pattern
theorem range803 (pattern : Ten) : 0 ≤ d803 pattern ∧ d803 pattern ≤ 10 := by
  unfold d803
  split
  · exact range49 pattern
  · exact range802 pattern
def d804 (pattern : Ten) : Int := if pattern.g then d72 pattern else d803 pattern
theorem range804 (pattern : Ten) : 0 ≤ d804 pattern ∧ d804 pattern ≤ 10 := by
  unfold d804
  split
  · exact range72 pattern
  · exact range803 pattern
def d805 (pattern : Ten) : Int := if pattern.j then d10 pattern else d7 pattern
theorem range805 (pattern : Ten) : 0 ≤ d805 pattern ∧ d805 pattern ≤ 10 := by
  unfold d805
  split
  · exact range10 pattern
  · exact range7 pattern
def d806 (pattern : Ten) : Int := if pattern.i then d10 pattern else d805 pattern
theorem range806 (pattern : Ten) : 0 ≤ d806 pattern ∧ d806 pattern ≤ 10 := by
  unfold d806
  split
  · exact range10 pattern
  · exact range805 pattern
def d807 (pattern : Ten) : Int := if pattern.h then d10 pattern else d806 pattern
theorem range807 (pattern : Ten) : 0 ≤ d807 pattern ∧ d807 pattern ≤ 10 := by
  unfold d807
  split
  · exact range10 pattern
  · exact range806 pattern
def d808 (pattern : Ten) : Int := if pattern.g then d10 pattern else d807 pattern
theorem range808 (pattern : Ten) : 0 ≤ d808 pattern ∧ d808 pattern ≤ 10 := by
  unfold d808
  split
  · exact range10 pattern
  · exact range807 pattern
def d809 (pattern : Ten) : Int := if pattern.c then d808 pattern else d804 pattern
theorem range809 (pattern : Ten) : 0 ≤ d809 pattern ∧ d809 pattern ≤ 10 := by
  unfold d809
  split
  · exact range808 pattern
  · exact range804 pattern
def d810 (pattern : Ten) : Int := if pattern.h then d10 pattern else d51 pattern
theorem range810 (pattern : Ten) : 0 ≤ d810 pattern ∧ d810 pattern ≤ 10 := by
  unfold d810
  split
  · exact range10 pattern
  · exact range51 pattern
def d811 (pattern : Ten) : Int := if pattern.g then d10 pattern else d810 pattern
theorem range811 (pattern : Ten) : 0 ≤ d811 pattern ∧ d811 pattern ≤ 10 := by
  unfold d811
  split
  · exact range10 pattern
  · exact range810 pattern
def d812 (pattern : Ten) : Int := if pattern.c then d10 pattern else d811 pattern
theorem range812 (pattern : Ten) : 0 ≤ d812 pattern ∧ d812 pattern ≤ 10 := by
  unfold d812
  split
  · exact range10 pattern
  · exact range811 pattern
def d813 (pattern : Ten) : Int := if pattern.e then d812 pattern else d809 pattern
theorem range813 (pattern : Ten) : 0 ≤ d813 pattern ∧ d813 pattern ≤ 10 := by
  unfold d813
  split
  · exact range812 pattern
  · exact range809 pattern
def d814 (pattern : Ten) : Int := if pattern.c then d10 pattern else d808 pattern
theorem range814 (pattern : Ten) : 0 ≤ d814 pattern ∧ d814 pattern ≤ 10 := by
  unfold d814
  split
  · exact range10 pattern
  · exact range808 pattern
def d815 (pattern : Ten) : Int := if pattern.e then d10 pattern else d814 pattern
theorem range815 (pattern : Ten) : 0 ≤ d815 pattern ∧ d815 pattern ≤ 10 := by
  unfold d815
  split
  · exact range10 pattern
  · exact range814 pattern
def d816 (pattern : Ten) : Int := if pattern.d then d815 pattern else d813 pattern
theorem range816 (pattern : Ten) : 0 ≤ d816 pattern ∧ d816 pattern ≤ 10 := by
  unfold d816
  split
  · exact range815 pattern
  · exact range813 pattern
end NetHack.Sokoban41.Diagram
