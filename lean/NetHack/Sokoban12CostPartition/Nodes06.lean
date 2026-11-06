/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Nodes05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d720 (p : Pattern) : Int := if p 158 then d674 p else d719 p
theorem agree720 (p q : Pattern) (h : Agree support p q) : d720 p = d720 q := by
  simp only [d720, h 158 (by decide), agree674 p q h, agree719 p q h]
theorem nonnegative720 (p : Pattern) : 0 ≤ d720 p :=
  nonnegative_ite (p 158) (nonnegative674 p) (nonnegative719 p)
def d721 (p : Pattern) : Int := if p 160 then d712 p else d43 p
theorem agree721 (p q : Pattern) (h : Agree support p q) : d721 p = d721 q := by
  simp only [d721, h 160 (by decide), agree712 p q h, agree43 p q h]
theorem nonnegative721 (p : Pattern) : 0 ≤ d721 p :=
  nonnegative_ite (p 160) (nonnegative712 p) (nonnegative43 p)
def d722 (p : Pattern) : Int := if p 159 then d713 p else d721 p
theorem agree722 (p q : Pattern) (h : Agree support p q) : d722 p = d722 q := by
  simp only [d722, h 159 (by decide), agree713 p q h, agree721 p q h]
theorem nonnegative722 (p : Pattern) : 0 ≤ d722 p :=
  nonnegative_ite (p 159) (nonnegative713 p) (nonnegative721 p)
def d723 (p : Pattern) : Int := if p 158 then d684 p else d722 p
theorem agree723 (p q : Pattern) (h : Agree support p q) : d723 p = d723 q := by
  simp only [d723, h 158 (by decide), agree684 p q h, agree722 p q h]
theorem nonnegative723 (p : Pattern) : 0 ≤ d723 p :=
  nonnegative_ite (p 158) (nonnegative684 p) (nonnegative722 p)
def d724 (p : Pattern) : Int := if p 141 then d723 p else d720 p
theorem agree724 (p q : Pattern) (h : Agree support p q) : d724 p = d724 q := by
  simp only [d724, h 141 (by decide), agree723 p q h, agree720 p q h]
theorem nonnegative724 (p : Pattern) : 0 ≤ d724 p :=
  nonnegative_ite (p 141) (nonnegative723 p) (nonnegative720 p)
def d725 (p : Pattern) : Int := if p 134 then d702 p else d724 p
theorem agree725 (p q : Pattern) (h : Agree support p q) : d725 p = d725 q := by
  simp only [d725, h 134 (by decide), agree702 p q h, agree724 p q h]
theorem nonnegative725 (p : Pattern) : 0 ≤ d725 p :=
  nonnegative_ite (p 134) (nonnegative702 p) (nonnegative724 p)
def d726 (p : Pattern) : Int := if p 133 then d725 p else d717 p
theorem agree726 (p q : Pattern) (h : Agree support p q) : d726 p = d726 q := by
  simp only [d726, h 133 (by decide), agree725 p q h, agree717 p q h]
theorem nonnegative726 (p : Pattern) : 0 ≤ d726 p :=
  nonnegative_ite (p 133) (nonnegative725 p) (nonnegative717 p)
def d727 (p : Pattern) : Int := if p 158 then d674 p else d709 p
theorem agree727 (p q : Pattern) (h : Agree support p q) : d727 p = d727 q := by
  simp only [d727, h 158 (by decide), agree674 p q h, agree709 p q h]
theorem nonnegative727 (p : Pattern) : 0 ≤ d727 p :=
  nonnegative_ite (p 158) (nonnegative674 p) (nonnegative709 p)
def d728 (p : Pattern) : Int := if p 158 then d684 p else d714 p
theorem agree728 (p q : Pattern) (h : Agree support p q) : d728 p = d728 q := by
  simp only [d728, h 158 (by decide), agree684 p q h, agree714 p q h]
theorem nonnegative728 (p : Pattern) : 0 ≤ d728 p :=
  nonnegative_ite (p 158) (nonnegative684 p) (nonnegative714 p)
def d729 (p : Pattern) : Int := if p 141 then d728 p else d727 p
theorem agree729 (p q : Pattern) (h : Agree support p q) : d729 p = d729 q := by
  simp only [d729, h 141 (by decide), agree728 p q h, agree727 p q h]
theorem nonnegative729 (p : Pattern) : 0 ≤ d729 p :=
  nonnegative_ite (p 141) (nonnegative728 p) (nonnegative727 p)
def d730 (p : Pattern) : Int := if p 134 then d702 p else d729 p
theorem agree730 (p q : Pattern) (h : Agree support p q) : d730 p = d730 q := by
  simp only [d730, h 134 (by decide), agree702 p q h, agree729 p q h]
theorem nonnegative730 (p : Pattern) : 0 ≤ d730 p :=
  nonnegative_ite (p 134) (nonnegative702 p) (nonnegative729 p)
def d731 (p : Pattern) : Int := if p 133 then d702 p else d730 p
theorem agree731 (p q : Pattern) (h : Agree support p q) : d731 p = d731 q := by
  simp only [d731, h 133 (by decide), agree702 p q h, agree730 p q h]
theorem nonnegative731 (p : Pattern) : 0 ≤ d731 p :=
  nonnegative_ite (p 133) (nonnegative702 p) (nonnegative730 p)
def d732 (p : Pattern) : Int := if p 132 then d731 p else d726 p
theorem agree732 (p q : Pattern) (h : Agree support p q) : d732 p = d732 q := by
  simp only [d732, h 132 (by decide), agree731 p q h, agree726 p q h]
theorem nonnegative732 (p : Pattern) : 0 ≤ d732 p :=
  nonnegative_ite (p 132) (nonnegative731 p) (nonnegative726 p)
def d733 (p : Pattern) : Int := if p 108 then d732 p else d704 p
theorem agree733 (p q : Pattern) (h : Agree support p q) : d733 p = d733 q := by
  simp only [d733, h 108 (by decide), agree732 p q h, agree704 p q h]
theorem nonnegative733 (p : Pattern) : 0 ≤ d733 p :=
  nonnegative_ite (p 108) (nonnegative732 p) (nonnegative704 p)
def d734 (p : Pattern) : Int := if p 108 then d1 p else d0 p
theorem agree734 (p q : Pattern) (h : Agree support p q) : d734 p = d734 q := by
  simp only [d734, h 108 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative734 (p : Pattern) : 0 ≤ d734 p :=
  nonnegative_ite (p 108) (nonnegative1 p) (nonnegative0 p)
def d735 (p : Pattern) : Int := if p 108 then d0 p else d1 p
theorem agree735 (p q : Pattern) (h : Agree support p q) : d735 p = d735 q := by
  simp only [d735, h 108 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative735 (p : Pattern) : 0 ≤ d735 p :=
  nonnegative_ite (p 108) (nonnegative0 p) (nonnegative1 p)
def d736 (p : Pattern) : Int := if p 134 then d1 p else d0 p
theorem agree736 (p q : Pattern) (h : Agree support p q) : d736 p = d736 q := by
  simp only [d736, h 134 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative736 (p : Pattern) : 0 ≤ d736 p :=
  nonnegative_ite (p 134) (nonnegative1 p) (nonnegative0 p)
def d737 (p : Pattern) : Int := if p 134 then d0 p else d1 p
theorem agree737 (p q : Pattern) (h : Agree support p q) : d737 p = d737 q := by
  simp only [d737, h 134 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative737 (p : Pattern) : 0 ≤ d737 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative1 p)
def d738 (p : Pattern) : Int := if p 108 then d737 p else d0 p
theorem agree738 (p q : Pattern) (h : Agree support p q) : d738 p = d738 q := by
  simp only [d738, h 108 (by decide), agree737 p q h, agree0 p q h]
theorem nonnegative738 (p : Pattern) : 0 ≤ d738 p :=
  nonnegative_ite (p 108) (nonnegative737 p) (nonnegative0 p)
def d739 (p : Pattern) : Int := if p 132 then d1 p else d0 p
theorem agree739 (p q : Pattern) (h : Agree support p q) : d739 p = d739 q := by
  simp only [d739, h 132 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative739 (p : Pattern) : 0 ≤ d739 p :=
  nonnegative_ite (p 132) (nonnegative1 p) (nonnegative0 p)
def d740 (p : Pattern) : Int := if p 132 then d0 p else d1 p
theorem agree740 (p q : Pattern) (h : Agree support p q) : d740 p = d740 q := by
  simp only [d740, h 132 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative740 (p : Pattern) : 0 ≤ d740 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative1 p)
def d741 (p : Pattern) : Int := if p 158 then d1 p else d0 p
theorem agree741 (p q : Pattern) (h : Agree support p q) : d741 p = d741 q := by
  simp only [d741, h 158 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative741 (p : Pattern) : 0 ≤ d741 p :=
  nonnegative_ite (p 158) (nonnegative1 p) (nonnegative0 p)
def d742 (p : Pattern) : Int := if p 158 then d0 p else d1 p
theorem agree742 (p q : Pattern) (h : Agree support p q) : d742 p = d742 q := by
  simp only [d742, h 158 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative742 (p : Pattern) : 0 ≤ d742 p :=
  nonnegative_ite (p 158) (nonnegative0 p) (nonnegative1 p)
def d743 (p : Pattern) : Int := if p 132 then d742 p else d0 p
theorem agree743 (p q : Pattern) (h : Agree support p q) : d743 p = d743 q := by
  simp only [d743, h 132 (by decide), agree742 p q h, agree0 p q h]
theorem nonnegative743 (p : Pattern) : 0 ≤ d743 p :=
  nonnegative_ite (p 132) (nonnegative742 p) (nonnegative0 p)
def d744 (p : Pattern) : Int := if p 134 then d336 p else d64 p
theorem agree744 (p q : Pattern) (h : Agree support p q) : d744 p = d744 q := by
  simp only [d744, h 134 (by decide), agree336 p q h, agree64 p q h]
theorem nonnegative744 (p : Pattern) : 0 ≤ d744 p :=
  nonnegative_ite (p 134) (nonnegative336 p) (nonnegative64 p)
def d745 (p : Pattern) : Int := if p 141 then d130 p else d123 p
theorem agree745 (p q : Pattern) (h : Agree support p q) : d745 p = d745 q := by
  simp only [d745, h 141 (by decide), agree130 p q h, agree123 p q h]
theorem nonnegative745 (p : Pattern) : 0 ≤ d745 p :=
  nonnegative_ite (p 141) (nonnegative130 p) (nonnegative123 p)
def d746 (p : Pattern) : Int := if p 134 then d745 p else d335 p
theorem agree746 (p q : Pattern) (h : Agree support p q) : d746 p = d746 q := by
  simp only [d746, h 134 (by decide), agree745 p q h, agree335 p q h]
theorem nonnegative746 (p : Pattern) : 0 ≤ d746 p :=
  nonnegative_ite (p 134) (nonnegative745 p) (nonnegative335 p)
def d747 (p : Pattern) : Int := if p 133 then d746 p else d744 p
theorem agree747 (p q : Pattern) (h : Agree support p q) : d747 p = d747 q := by
  simp only [d747, h 133 (by decide), agree746 p q h, agree744 p q h]
theorem nonnegative747 (p : Pattern) : 0 ≤ d747 p :=
  nonnegative_ite (p 133) (nonnegative746 p) (nonnegative744 p)
def d748 (p : Pattern) : Int := if p 141 then d148 p else d141 p
theorem agree748 (p q : Pattern) (h : Agree support p q) : d748 p = d748 q := by
  simp only [d748, h 141 (by decide), agree148 p q h, agree141 p q h]
theorem nonnegative748 (p : Pattern) : 0 ≤ d748 p :=
  nonnegative_ite (p 141) (nonnegative148 p) (nonnegative141 p)
def d749 (p : Pattern) : Int := if p 134 then d66 p else d748 p
theorem agree749 (p q : Pattern) (h : Agree support p q) : d749 p = d749 q := by
  simp only [d749, h 134 (by decide), agree66 p q h, agree748 p q h]
theorem nonnegative749 (p : Pattern) : 0 ≤ d749 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative748 p)
def d750 (p : Pattern) : Int := if p 133 then d749 p else d67 p
theorem agree750 (p q : Pattern) (h : Agree support p q) : d750 p = d750 q := by
  simp only [d750, h 133 (by decide), agree749 p q h, agree67 p q h]
theorem nonnegative750 (p : Pattern) : 0 ≤ d750 p :=
  nonnegative_ite (p 133) (nonnegative749 p) (nonnegative67 p)
def d751 (p : Pattern) : Int := if p 108 then d750 p else d747 p
theorem agree751 (p q : Pattern) (h : Agree support p q) : d751 p = d751 q := by
  simp only [d751, h 108 (by decide), agree750 p q h, agree747 p q h]
theorem nonnegative751 (p : Pattern) : 0 ≤ d751 p :=
  nonnegative_ite (p 108) (nonnegative750 p) (nonnegative747 p)
def d752 (p : Pattern) : Int := if p 133 then d1 p else d0 p
theorem agree752 (p q : Pattern) (h : Agree support p q) : d752 p = d752 q := by
  simp only [d752, h 133 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative752 (p : Pattern) : 0 ≤ d752 p :=
  nonnegative_ite (p 133) (nonnegative1 p) (nonnegative0 p)
def d753 (p : Pattern) : Int := if p 133 then d0 p else d1 p
theorem agree753 (p q : Pattern) (h : Agree support p q) : d753 p = d753 q := by
  simp only [d753, h 133 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative753 (p : Pattern) : 0 ≤ d753 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative1 p)
def d754 (p : Pattern) : Int := if p 132 then d0 p else d753 p
theorem agree754 (p q : Pattern) (h : Agree support p q) : d754 p = d754 q := by
  simp only [d754, h 132 (by decide), agree0 p q h, agree753 p q h]
theorem nonnegative754 (p : Pattern) : 0 ≤ d754 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative753 p)
def d755 (p : Pattern) : Int := if p 108 then d0 p else d737 p
theorem agree755 (p q : Pattern) (h : Agree support p q) : d755 p = d755 q := by
  simp only [d755, h 108 (by decide), agree0 p q h, agree737 p q h]
theorem nonnegative755 (p : Pattern) : 0 ≤ d755 p :=
  nonnegative_ite (p 108) (nonnegative0 p) (nonnegative737 p)
def d756 (p : Pattern) : Int := if p 108 then d0 p else d736 p
theorem agree756 (p q : Pattern) (h : Agree support p q) : d756 p = d756 q := by
  simp only [d756, h 108 (by decide), agree0 p q h, agree736 p q h]
theorem nonnegative756 (p : Pattern) : 0 ≤ d756 p :=
  nonnegative_ite (p 108) (nonnegative0 p) (nonnegative736 p)
def d757 (p : Pattern) : Int := if p 160 then d1 p else d0 p
theorem agree757 (p q : Pattern) (h : Agree support p q) : d757 p = d757 q := by
  simp only [d757, h 160 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative757 (p : Pattern) : 0 ≤ d757 p :=
  nonnegative_ite (p 160) (nonnegative1 p) (nonnegative0 p)
def d758 (p : Pattern) : Int := if p 160 then d0 p else d1 p
theorem agree758 (p q : Pattern) (h : Agree support p q) : d758 p = d758 q := by
  simp only [d758, h 160 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative758 (p : Pattern) : 0 ≤ d758 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative1 p)
def d759 (p : Pattern) : Int := if p 134 then d758 p else d0 p
theorem agree759 (p q : Pattern) (h : Agree support p q) : d759 p = d759 q := by
  simp only [d759, h 134 (by decide), agree758 p q h, agree0 p q h]
theorem nonnegative759 (p : Pattern) : 0 ≤ d759 p :=
  nonnegative_ite (p 134) (nonnegative758 p) (nonnegative0 p)
def d760 (p : Pattern) : Int := if p 108 then d0 p else d759 p
theorem agree760 (p q : Pattern) (h : Agree support p q) : d760 p = d760 q := by
  simp only [d760, h 108 (by decide), agree0 p q h, agree759 p q h]
theorem nonnegative760 (p : Pattern) : 0 ≤ d760 p :=
  nonnegative_ite (p 108) (nonnegative0 p) (nonnegative759 p)
def d761 (p : Pattern) : Int := if p 133 then d458 p else d451 p
theorem agree761 (p q : Pattern) (h : Agree support p q) : d761 p = d761 q := by
  simp only [d761, h 133 (by decide), agree458 p q h, agree451 p q h]
theorem nonnegative761 (p : Pattern) : 0 ≤ d761 p :=
  nonnegative_ite (p 133) (nonnegative458 p) (nonnegative451 p)
def d762 (p : Pattern) : Int := if p 133 then d66 p else d458 p
theorem agree762 (p q : Pattern) (h : Agree support p q) : d762 p = d762 q := by
  simp only [d762, h 133 (by decide), agree66 p q h, agree458 p q h]
theorem nonnegative762 (p : Pattern) : 0 ≤ d762 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative458 p)
def d763 (p : Pattern) : Int := if p 132 then d762 p else d761 p
theorem agree763 (p q : Pattern) (h : Agree support p q) : d763 p = d763 q := by
  simp only [d763, h 132 (by decide), agree762 p q h, agree761 p q h]
theorem nonnegative763 (p : Pattern) : 0 ≤ d763 p :=
  nonnegative_ite (p 132) (nonnegative762 p) (nonnegative761 p)
def d764 (p : Pattern) : Int := if p 108 then d0 p else d753 p
theorem agree764 (p q : Pattern) (h : Agree support p q) : d764 p = d764 q := by
  simp only [d764, h 108 (by decide), agree0 p q h, agree753 p q h]
theorem nonnegative764 (p : Pattern) : 0 ≤ d764 p :=
  nonnegative_ite (p 108) (nonnegative0 p) (nonnegative753 p)
def d765 (p : Pattern) : Int := if p 133 then d0 p else d737 p
theorem agree765 (p q : Pattern) (h : Agree support p q) : d765 p = d765 q := by
  simp only [d765, h 133 (by decide), agree0 p q h, agree737 p q h]
theorem nonnegative765 (p : Pattern) : 0 ≤ d765 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative737 p)
def d766 (p : Pattern) : Int := if p 108 then d0 p else d765 p
theorem agree766 (p q : Pattern) (h : Agree support p q) : d766 p = d766 q := by
  simp only [d766, h 108 (by decide), agree0 p q h, agree765 p q h]
theorem nonnegative766 (p : Pattern) : 0 ≤ d766 p :=
  nonnegative_ite (p 108) (nonnegative0 p) (nonnegative765 p)
def d767 (p : Pattern) : Int := if p 141 then d1 p else d0 p
theorem agree767 (p q : Pattern) (h : Agree support p q) : d767 p = d767 q := by
  simp only [d767, h 141 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative767 (p : Pattern) : 0 ≤ d767 p :=
  nonnegative_ite (p 141) (nonnegative1 p) (nonnegative0 p)
def d768 (p : Pattern) : Int := if p 141 then d0 p else d1 p
theorem agree768 (p q : Pattern) (h : Agree support p q) : d768 p = d768 q := by
  simp only [d768, h 141 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative768 (p : Pattern) : 0 ≤ d768 p :=
  nonnegative_ite (p 141) (nonnegative0 p) (nonnegative1 p)
def d769 (p : Pattern) : Int := if p 168 then d1 p else d0 p
theorem agree769 (p q : Pattern) (h : Agree support p q) : d769 p = d769 q := by
  simp only [d769, h 168 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative769 (p : Pattern) : 0 ≤ d769 p :=
  nonnegative_ite (p 168) (nonnegative1 p) (nonnegative0 p)
def d770 (p : Pattern) : Int := if p 168 then d0 p else d1 p
theorem agree770 (p q : Pattern) (h : Agree support p q) : d770 p = d770 q := by
  simp only [d770, h 168 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative770 (p : Pattern) : 0 ≤ d770 p :=
  nonnegative_ite (p 168) (nonnegative0 p) (nonnegative1 p)
def d771 (p : Pattern) : Int := if p 132 then d753 p else d0 p
theorem agree771 (p q : Pattern) (h : Agree support p q) : d771 p = d771 q := by
  simp only [d771, h 132 (by decide), agree753 p q h, agree0 p q h]
theorem nonnegative771 (p : Pattern) : 0 ≤ d771 p :=
  nonnegative_ite (p 132) (nonnegative753 p) (nonnegative0 p)
def d772 (p : Pattern) : Int := if p 108 then d151 p else d133 p
theorem agree772 (p q : Pattern) (h : Agree support p q) : d772 p = d772 q := by
  simp only [d772, h 108 (by decide), agree151 p q h, agree133 p q h]
theorem nonnegative772 (p : Pattern) : 0 ≤ d772 p :=
  nonnegative_ite (p 108) (nonnegative151 p) (nonnegative133 p)
def d773 (p : Pattern) : Int := if p 132 then d0 p else d742 p
theorem agree773 (p q : Pattern) (h : Agree support p q) : d773 p = d773 q := by
  simp only [d773, h 132 (by decide), agree0 p q h, agree742 p q h]
theorem nonnegative773 (p : Pattern) : 0 ≤ d773 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative742 p)
def d774 (p : Pattern) : Int := if p 132 then d0 p else d741 p
theorem agree774 (p q : Pattern) (h : Agree support p q) : d774 p = d774 q := by
  simp only [d774, h 132 (by decide), agree0 p q h, agree741 p q h]
theorem nonnegative774 (p : Pattern) : 0 ≤ d774 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative741 p)
def d775 (p : Pattern) : Int := if p 141 then d129 p else d122 p
theorem agree775 (p q : Pattern) (h : Agree support p q) : d775 p = d775 q := by
  simp only [d775, h 141 (by decide), agree129 p q h, agree122 p q h]
theorem nonnegative775 (p : Pattern) : 0 ≤ d775 p :=
  nonnegative_ite (p 141) (nonnegative129 p) (nonnegative122 p)
def d776 (p : Pattern) : Int := if p 134 then d775 p else d64 p
theorem agree776 (p q : Pattern) (h : Agree support p q) : d776 p = d776 q := by
  simp only [d776, h 134 (by decide), agree775 p q h, agree64 p q h]
theorem nonnegative776 (p : Pattern) : 0 ≤ d776 p :=
  nonnegative_ite (p 134) (nonnegative775 p) (nonnegative64 p)
def d777 (p : Pattern) : Int := if p 133 then d776 p else d228 p
theorem agree777 (p q : Pattern) (h : Agree support p q) : d777 p = d777 q := by
  simp only [d777, h 133 (by decide), agree776 p q h, agree228 p q h]
theorem nonnegative777 (p : Pattern) : 0 ≤ d777 p :=
  nonnegative_ite (p 133) (nonnegative776 p) (nonnegative228 p)
def d778 (p : Pattern) : Int := if p 133 then d66 p else d776 p
theorem agree778 (p q : Pattern) (h : Agree support p q) : d778 p = d778 q := by
  simp only [d778, h 133 (by decide), agree66 p q h, agree776 p q h]
theorem nonnegative778 (p : Pattern) : 0 ≤ d778 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative776 p)
def d779 (p : Pattern) : Int := if p 132 then d778 p else d777 p
theorem agree779 (p q : Pattern) (h : Agree support p q) : d779 p = d779 q := by
  simp only [d779, h 132 (by decide), agree778 p q h, agree777 p q h]
theorem nonnegative779 (p : Pattern) : 0 ≤ d779 p :=
  nonnegative_ite (p 132) (nonnegative778 p) (nonnegative777 p)
def d780 (p : Pattern) : Int := if p 141 then d147 p else d140 p
theorem agree780 (p q : Pattern) (h : Agree support p q) : d780 p = d780 q := by
  simp only [d780, h 141 (by decide), agree147 p q h, agree140 p q h]
theorem nonnegative780 (p : Pattern) : 0 ≤ d780 p :=
  nonnegative_ite (p 141) (nonnegative147 p) (nonnegative140 p)
def d781 (p : Pattern) : Int := if p 134 then d66 p else d780 p
theorem agree781 (p q : Pattern) (h : Agree support p q) : d781 p = d781 q := by
  simp only [d781, h 134 (by decide), agree66 p q h, agree780 p q h]
theorem nonnegative781 (p : Pattern) : 0 ≤ d781 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative780 p)
def d782 (p : Pattern) : Int := if p 133 then d781 p else d67 p
theorem agree782 (p q : Pattern) (h : Agree support p q) : d782 p = d782 q := by
  simp only [d782, h 133 (by decide), agree781 p q h, agree67 p q h]
theorem nonnegative782 (p : Pattern) : 0 ≤ d782 p :=
  nonnegative_ite (p 133) (nonnegative781 p) (nonnegative67 p)
def d783 (p : Pattern) : Int := if p 141 then d155 p else d153 p
theorem agree783 (p q : Pattern) (h : Agree support p q) : d783 p = d783 q := by
  simp only [d783, h 141 (by decide), agree155 p q h, agree153 p q h]
theorem nonnegative783 (p : Pattern) : 0 ≤ d783 p :=
  nonnegative_ite (p 141) (nonnegative155 p) (nonnegative153 p)
def d784 (p : Pattern) : Int := if p 134 then d66 p else d783 p
theorem agree784 (p q : Pattern) (h : Agree support p q) : d784 p = d784 q := by
  simp only [d784, h 134 (by decide), agree66 p q h, agree783 p q h]
theorem nonnegative784 (p : Pattern) : 0 ≤ d784 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative783 p)
def d785 (p : Pattern) : Int := if p 133 then d66 p else d784 p
theorem agree785 (p q : Pattern) (h : Agree support p q) : d785 p = d785 q := by
  simp only [d785, h 133 (by decide), agree66 p q h, agree784 p q h]
theorem nonnegative785 (p : Pattern) : 0 ≤ d785 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative784 p)
def d786 (p : Pattern) : Int := if p 132 then d785 p else d782 p
theorem agree786 (p q : Pattern) (h : Agree support p q) : d786 p = d786 q := by
  simp only [d786, h 132 (by decide), agree785 p q h, agree782 p q h]
theorem nonnegative786 (p : Pattern) : 0 ≤ d786 p :=
  nonnegative_ite (p 132) (nonnegative785 p) (nonnegative782 p)
def d787 (p : Pattern) : Int := if p 108 then d786 p else d779 p
theorem agree787 (p q : Pattern) (h : Agree support p q) : d787 p = d787 q := by
  simp only [d787, h 108 (by decide), agree786 p q h, agree779 p q h]
theorem nonnegative787 (p : Pattern) : 0 ≤ d787 p :=
  nonnegative_ite (p 108) (nonnegative786 p) (nonnegative779 p)
def d788 (p : Pattern) : Int := if p 132 then d0 p else d752 p
theorem agree788 (p q : Pattern) (h : Agree support p q) : d788 p = d788 q := by
  simp only [d788, h 132 (by decide), agree0 p q h, agree752 p q h]
theorem nonnegative788 (p : Pattern) : 0 ≤ d788 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative752 p)
def d789 (p : Pattern) : Int := if p 133 then d737 p else d0 p
theorem agree789 (p q : Pattern) (h : Agree support p q) : d789 p = d789 q := by
  simp only [d789, h 133 (by decide), agree737 p q h, agree0 p q h]
theorem nonnegative789 (p : Pattern) : 0 ≤ d789 p :=
  nonnegative_ite (p 133) (nonnegative737 p) (nonnegative0 p)
def d790 (p : Pattern) : Int := if p 132 then d0 p else d789 p
theorem agree790 (p q : Pattern) (h : Agree support p q) : d790 p = d790 q := by
  simp only [d790, h 132 (by decide), agree0 p q h, agree789 p q h]
theorem nonnegative790 (p : Pattern) : 0 ≤ d790 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative789 p)
def d791 (p : Pattern) : Int := if p 132 then d213 p else d112 p
theorem agree791 (p q : Pattern) (h : Agree support p q) : d791 p = d791 q := by
  simp only [d791, h 132 (by decide), agree213 p q h, agree112 p q h]
theorem nonnegative791 (p : Pattern) : 0 ≤ d791 p :=
  nonnegative_ite (p 132) (nonnegative213 p) (nonnegative112 p)
def d792 (p : Pattern) : Int := if p 108 then d66 p else d791 p
theorem agree792 (p q : Pattern) (h : Agree support p q) : d792 p = d792 q := by
  simp only [d792, h 108 (by decide), agree66 p q h, agree791 p q h]
theorem nonnegative792 (p : Pattern) : 0 ≤ d792 p :=
  nonnegative_ite (p 108) (nonnegative66 p) (nonnegative791 p)
def d793 (p : Pattern) : Int := if p 159 then d1 p else d0 p
theorem agree793 (p q : Pattern) (h : Agree support p q) : d793 p = d793 q := by
  simp only [d793, h 159 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative793 (p : Pattern) : 0 ≤ d793 p :=
  nonnegative_ite (p 159) (nonnegative1 p) (nonnegative0 p)
def d794 (p : Pattern) : Int := if p 159 then d0 p else d1 p
theorem agree794 (p q : Pattern) (h : Agree support p q) : d794 p = d794 q := by
  simp only [d794, h 159 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative794 (p : Pattern) : 0 ≤ d794 p :=
  nonnegative_ite (p 159) (nonnegative0 p) (nonnegative1 p)
def d795 (p : Pattern) : Int := if p 132 then d0 p else d794 p
theorem agree795 (p q : Pattern) (h : Agree support p q) : d795 p = d795 q := by
  simp only [d795, h 132 (by decide), agree0 p q h, agree794 p q h]
theorem nonnegative795 (p : Pattern) : 0 ≤ d795 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative794 p)
def d796 (p : Pattern) : Int := if p 133 then d741 p else d0 p
theorem agree796 (p q : Pattern) (h : Agree support p q) : d796 p = d796 q := by
  simp only [d796, h 133 (by decide), agree741 p q h, agree0 p q h]
theorem nonnegative796 (p : Pattern) : 0 ≤ d796 p :=
  nonnegative_ite (p 133) (nonnegative741 p) (nonnegative0 p)
def d797 (p : Pattern) : Int := if p 133 then d742 p else d1 p
theorem agree797 (p q : Pattern) (h : Agree support p q) : d797 p = d797 q := by
  simp only [d797, h 133 (by decide), agree742 p q h, agree1 p q h]
theorem nonnegative797 (p : Pattern) : 0 ≤ d797 p :=
  nonnegative_ite (p 133) (nonnegative742 p) (nonnegative1 p)
def d798 (p : Pattern) : Int := if p 158 then d0 p else d794 p
theorem agree798 (p q : Pattern) (h : Agree support p q) : d798 p = d798 q := by
  simp only [d798, h 158 (by decide), agree0 p q h, agree794 p q h]
theorem nonnegative798 (p : Pattern) : 0 ≤ d798 p :=
  nonnegative_ite (p 158) (nonnegative0 p) (nonnegative794 p)
def d799 (p : Pattern) : Int := if p 133 then d798 p else d794 p
theorem agree799 (p q : Pattern) (h : Agree support p q) : d799 p = d799 q := by
  simp only [d799, h 133 (by decide), agree798 p q h, agree794 p q h]
theorem nonnegative799 (p : Pattern) : 0 ≤ d799 p :=
  nonnegative_ite (p 133) (nonnegative798 p) (nonnegative794 p)
def d800 (p : Pattern) : Int := if p 132 then d0 p else d799 p
theorem agree800 (p q : Pattern) (h : Agree support p q) : d800 p = d800 q := by
  simp only [d800, h 132 (by decide), agree0 p q h, agree799 p q h]
theorem nonnegative800 (p : Pattern) : 0 ≤ d800 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative799 p)
def d801 (p : Pattern) : Int := if p 133 then d0 p else d794 p
theorem agree801 (p q : Pattern) (h : Agree support p q) : d801 p = d801 q := by
  simp only [d801, h 133 (by decide), agree0 p q h, agree794 p q h]
theorem nonnegative801 (p : Pattern) : 0 ≤ d801 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative794 p)
def d802 (p : Pattern) : Int := if p 133 then d0 p else d793 p
theorem agree802 (p q : Pattern) (h : Agree support p q) : d802 p = d802 q := by
  simp only [d802, h 133 (by decide), agree0 p q h, agree793 p q h]
theorem nonnegative802 (p : Pattern) : 0 ≤ d802 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative793 p)
def d803 (p : Pattern) : Int := if p 158 then d55 p else d138 p
theorem agree803 (p q : Pattern) (h : Agree support p q) : d803 p = d803 q := by
  simp only [d803, h 158 (by decide), agree55 p q h, agree138 p q h]
theorem nonnegative803 (p : Pattern) : 0 ≤ d803 p :=
  nonnegative_ite (p 158) (nonnegative55 p) (nonnegative138 p)
def d804 (p : Pattern) : Int := if p 158 then d65 p else d145 p
theorem agree804 (p q : Pattern) (h : Agree support p q) : d804 p = d804 q := by
  simp only [d804, h 158 (by decide), agree65 p q h, agree145 p q h]
theorem nonnegative804 (p : Pattern) : 0 ≤ d804 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative145 p)
def d805 (p : Pattern) : Int := if p 141 then d804 p else d803 p
theorem agree805 (p q : Pattern) (h : Agree support p q) : d805 p = d805 q := by
  simp only [d805, h 141 (by decide), agree804 p q h, agree803 p q h]
theorem nonnegative805 (p : Pattern) : 0 ≤ d805 p :=
  nonnegative_ite (p 141) (nonnegative804 p) (nonnegative803 p)
def d806 (p : Pattern) : Int := if p 134 then d66 p else d805 p
theorem agree806 (p q : Pattern) (h : Agree support p q) : d806 p = d806 q := by
  simp only [d806, h 134 (by decide), agree66 p q h, agree805 p q h]
theorem nonnegative806 (p : Pattern) : 0 ≤ d806 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative805 p)
def d807 (p : Pattern) : Int := if p 133 then d806 p else d67 p
theorem agree807 (p q : Pattern) (h : Agree support p q) : d807 p = d807 q := by
  simp only [d807, h 133 (by decide), agree806 p q h, agree67 p q h]
theorem nonnegative807 (p : Pattern) : 0 ≤ d807 p :=
  nonnegative_ite (p 133) (nonnegative806 p) (nonnegative67 p)
def d808 (p : Pattern) : Int := if p 132 then d73 p else d807 p
theorem agree808 (p q : Pattern) (h : Agree support p q) : d808 p = d808 q := by
  simp only [d808, h 132 (by decide), agree73 p q h, agree807 p q h]
theorem nonnegative808 (p : Pattern) : 0 ≤ d808 p :=
  nonnegative_ite (p 132) (nonnegative73 p) (nonnegative807 p)
def d809 (p : Pattern) : Int := if p 108 then d808 p else d235 p
theorem agree809 (p q : Pattern) (h : Agree support p q) : d809 p = d809 q := by
  simp only [d809, h 108 (by decide), agree808 p q h, agree235 p q h]
theorem nonnegative809 (p : Pattern) : 0 ≤ d809 p :=
  nonnegative_ite (p 108) (nonnegative808 p) (nonnegative235 p)
def d810 (p : Pattern) : Int := if p 133 then d0 p else d736 p
theorem agree810 (p q : Pattern) (h : Agree support p q) : d810 p = d810 q := by
  simp only [d810, h 133 (by decide), agree0 p q h, agree736 p q h]
theorem nonnegative810 (p : Pattern) : 0 ≤ d810 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative736 p)
def d811 (p : Pattern) : Int := if p 133 then d70 p else d64 p
theorem agree811 (p q : Pattern) (h : Agree support p q) : d811 p = d811 q := by
  simp only [d811, h 133 (by decide), agree70 p q h, agree64 p q h]
theorem nonnegative811 (p : Pattern) : 0 ≤ d811 p :=
  nonnegative_ite (p 133) (nonnegative70 p) (nonnegative64 p)
def d812 (p : Pattern) : Int := if p 133 then d66 p else d70 p
theorem agree812 (p q : Pattern) (h : Agree support p q) : d812 p = d812 q := by
  simp only [d812, h 133 (by decide), agree66 p q h, agree70 p q h]
theorem nonnegative812 (p : Pattern) : 0 ≤ d812 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative70 p)
def d813 (p : Pattern) : Int := if p 132 then d812 p else d811 p
theorem agree813 (p q : Pattern) (h : Agree support p q) : d813 p = d813 q := by
  simp only [d813, h 132 (by decide), agree812 p q h, agree811 p q h]
theorem nonnegative813 (p : Pattern) : 0 ≤ d813 p :=
  nonnegative_ite (p 132) (nonnegative812 p) (nonnegative811 p)
def d814 (p : Pattern) : Int := if p 108 then d152 p else d134 p
theorem agree814 (p q : Pattern) (h : Agree support p q) : d814 p = d814 q := by
  simp only [d814, h 108 (by decide), agree152 p q h, agree134 p q h]
theorem nonnegative814 (p : Pattern) : 0 ≤ d814 p :=
  nonnegative_ite (p 108) (nonnegative152 p) (nonnegative134 p)
def d815 (p : Pattern) : Int := if p 133 then d0 p else d758 p
theorem agree815 (p q : Pattern) (h : Agree support p q) : d815 p = d815 q := by
  simp only [d815, h 133 (by decide), agree0 p q h, agree758 p q h]
theorem nonnegative815 (p : Pattern) : 0 ≤ d815 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative758 p)
def d816 (p : Pattern) : Int := if p 134 then d793 p else d0 p
theorem agree816 (p q : Pattern) (h : Agree support p q) : d816 p = d816 q := by
  simp only [d816, h 134 (by decide), agree793 p q h, agree0 p q h]
theorem nonnegative816 (p : Pattern) : 0 ≤ d816 p :=
  nonnegative_ite (p 134) (nonnegative793 p) (nonnegative0 p)
def d817 (p : Pattern) : Int := if p 134 then d794 p else d1 p
theorem agree817 (p q : Pattern) (h : Agree support p q) : d817 p = d817 q := by
  simp only [d817, h 134 (by decide), agree794 p q h, agree1 p q h]
theorem nonnegative817 (p : Pattern) : 0 ≤ d817 p :=
  nonnegative_ite (p 134) (nonnegative794 p) (nonnegative1 p)
def d818 (p : Pattern) : Int := if p 159 then d0 p else d758 p
theorem agree818 (p q : Pattern) (h : Agree support p q) : d818 p = d818 q := by
  simp only [d818, h 159 (by decide), agree0 p q h, agree758 p q h]
theorem nonnegative818 (p : Pattern) : 0 ≤ d818 p :=
  nonnegative_ite (p 159) (nonnegative0 p) (nonnegative758 p)
def d819 (p : Pattern) : Int := if p 134 then d818 p else d758 p
theorem agree819 (p q : Pattern) (h : Agree support p q) : d819 p = d819 q := by
  simp only [d819, h 134 (by decide), agree818 p q h, agree758 p q h]
theorem nonnegative819 (p : Pattern) : 0 ≤ d819 p :=
  nonnegative_ite (p 134) (nonnegative818 p) (nonnegative758 p)
def d820 (p : Pattern) : Int := if p 133 then d0 p else d819 p
theorem agree820 (p q : Pattern) (h : Agree support p q) : d820 p = d820 q := by
  simp only [d820, h 133 (by decide), agree0 p q h, agree819 p q h]
theorem nonnegative820 (p : Pattern) : 0 ≤ d820 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative819 p)
def d821 (p : Pattern) : Int := if p 133 then d0 p else d742 p
theorem agree821 (p q : Pattern) (h : Agree support p q) : d821 p = d821 q := by
  simp only [d821, h 133 (by decide), agree0 p q h, agree742 p q h]
theorem nonnegative821 (p : Pattern) : 0 ≤ d821 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative742 p)
def d822 (p : Pattern) : Int := if p 132 then d793 p else d0 p
theorem agree822 (p q : Pattern) (h : Agree support p q) : d822 p = d822 q := by
  simp only [d822, h 132 (by decide), agree793 p q h, agree0 p q h]
theorem nonnegative822 (p : Pattern) : 0 ≤ d822 p :=
  nonnegative_ite (p 132) (nonnegative793 p) (nonnegative0 p)
def d823 (p : Pattern) : Int := if p 132 then d794 p else d1 p
theorem agree823 (p q : Pattern) (h : Agree support p q) : d823 p = d823 q := by
  simp only [d823, h 132 (by decide), agree794 p q h, agree1 p q h]
theorem nonnegative823 (p : Pattern) : 0 ≤ d823 p :=
  nonnegative_ite (p 132) (nonnegative794 p) (nonnegative1 p)
def d824 (p : Pattern) : Int := if p 133 then d0 p else d798 p
theorem agree824 (p q : Pattern) (h : Agree support p q) : d824 p = d824 q := by
  simp only [d824, h 133 (by decide), agree0 p q h, agree798 p q h]
theorem nonnegative824 (p : Pattern) : 0 ≤ d824 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative798 p)
def d825 (p : Pattern) : Int := if p 132 then d824 p else d821 p
theorem agree825 (p q : Pattern) (h : Agree support p q) : d825 p = d825 q := by
  simp only [d825, h 132 (by decide), agree824 p q h, agree821 p q h]
theorem nonnegative825 (p : Pattern) : 0 ≤ d825 p :=
  nonnegative_ite (p 132) (nonnegative824 p) (nonnegative821 p)
def d826 (p : Pattern) : Int := if p 134 then d0 p else d758 p
theorem agree826 (p q : Pattern) (h : Agree support p q) : d826 p = d826 q := by
  simp only [d826, h 134 (by decide), agree0 p q h, agree758 p q h]
theorem nonnegative826 (p : Pattern) : 0 ≤ d826 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative758 p)
def d827 (p : Pattern) : Int := if p 134 then d0 p else d757 p
theorem agree827 (p q : Pattern) (h : Agree support p q) : d827 p = d827 q := by
  simp only [d827, h 134 (by decide), agree0 p q h, agree757 p q h]
theorem nonnegative827 (p : Pattern) : 0 ≤ d827 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative757 p)
def d828 (p : Pattern) : Int := if p 186 then d1 p else d0 p
theorem agree828 (p q : Pattern) (h : Agree support p q) : d828 p = d828 q := by
  simp only [d828, h 186 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative828 (p : Pattern) : 0 ≤ d828 p :=
  nonnegative_ite (p 186) (nonnegative1 p) (nonnegative0 p)
def d829 (p : Pattern) : Int := if p 186 then d0 p else d1 p
theorem agree829 (p q : Pattern) (h : Agree support p q) : d829 p = d829 q := by
  simp only [d829, h 186 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative829 (p : Pattern) : 0 ≤ d829 p :=
  nonnegative_ite (p 186) (nonnegative0 p) (nonnegative1 p)
def d830 (p : Pattern) : Int := if p 160 then d829 p else d0 p
theorem agree830 (p q : Pattern) (h : Agree support p q) : d830 p = d830 q := by
  simp only [d830, h 160 (by decide), agree829 p q h, agree0 p q h]
theorem nonnegative830 (p : Pattern) : 0 ≤ d830 p :=
  nonnegative_ite (p 160) (nonnegative829 p) (nonnegative0 p)
def d831 (p : Pattern) : Int := if p 134 then d0 p else d830 p
theorem agree831 (p q : Pattern) (h : Agree support p q) : d831 p = d831 q := by
  simp only [d831, h 134 (by decide), agree0 p q h, agree830 p q h]
theorem nonnegative831 (p : Pattern) : 0 ≤ d831 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative830 p)
def d832 (p : Pattern) : Int := if p 158 then d55 p else d7 p
theorem agree832 (p q : Pattern) (h : Agree support p q) : d832 p = d832 q := by
  simp only [d832, h 158 (by decide), agree55 p q h, agree7 p q h]
theorem nonnegative832 (p : Pattern) : 0 ≤ d832 p :=
  nonnegative_ite (p 158) (nonnegative55 p) (nonnegative7 p)
def d833 (p : Pattern) : Int := if p 158 then d65 p else d12 p
theorem agree833 (p q : Pattern) (h : Agree support p q) : d833 p = d833 q := by
  simp only [d833, h 158 (by decide), agree65 p q h, agree12 p q h]
theorem nonnegative833 (p : Pattern) : 0 ≤ d833 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative12 p)
def d834 (p : Pattern) : Int := if p 141 then d833 p else d832 p
theorem agree834 (p q : Pattern) (h : Agree support p q) : d834 p = d834 q := by
  simp only [d834, h 141 (by decide), agree833 p q h, agree832 p q h]
theorem nonnegative834 (p : Pattern) : 0 ≤ d834 p :=
  nonnegative_ite (p 141) (nonnegative833 p) (nonnegative832 p)
def d835 (p : Pattern) : Int := if p 133 then d834 p else d13 p
theorem agree835 (p q : Pattern) (h : Agree support p q) : d835 p = d835 q := by
  simp only [d835, h 133 (by decide), agree834 p q h, agree13 p q h]
theorem nonnegative835 (p : Pattern) : 0 ≤ d835 p :=
  nonnegative_ite (p 133) (nonnegative834 p) (nonnegative13 p)
def d836 (p : Pattern) : Int := if p 133 then d66 p else d834 p
theorem agree836 (p q : Pattern) (h : Agree support p q) : d836 p = d836 q := by
  simp only [d836, h 133 (by decide), agree66 p q h, agree834 p q h]
theorem nonnegative836 (p : Pattern) : 0 ≤ d836 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative834 p)
def d837 (p : Pattern) : Int := if p 132 then d836 p else d835 p
theorem agree837 (p q : Pattern) (h : Agree support p q) : d837 p = d837 q := by
  simp only [d837, h 132 (by decide), agree836 p q h, agree835 p q h]
theorem nonnegative837 (p : Pattern) : 0 ≤ d837 p :=
  nonnegative_ite (p 132) (nonnegative836 p) (nonnegative835 p)
def d838 (p : Pattern) : Int := if p 134 then d66 p else d13 p
theorem agree838 (p q : Pattern) (h : Agree support p q) : d838 p = d838 q := by
  simp only [d838, h 134 (by decide), agree66 p q h, agree13 p q h]
theorem nonnegative838 (p : Pattern) : 0 ≤ d838 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative13 p)
def d839 (p : Pattern) : Int := if p 134 then d66 p else d834 p
theorem agree839 (p q : Pattern) (h : Agree support p q) : d839 p = d839 q := by
  simp only [d839, h 134 (by decide), agree66 p q h, agree834 p q h]
theorem nonnegative839 (p : Pattern) : 0 ≤ d839 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative834 p)
end NetHack.Sokoban12CostPartition
