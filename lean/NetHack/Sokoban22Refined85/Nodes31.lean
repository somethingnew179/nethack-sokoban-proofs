/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes30
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d3720 (p : Pattern) : Int := if p 225 then d13 p else d3719 p
theorem agree3720 (p q : Pattern) (h : Agree support p q) : d3720 p = d3720 q := by
  simp only [d3720, h 225 (by decide), agree13 p q h, agree3719 p q h]
theorem nonnegative3720 (p : Pattern) : 0 ≤ d3720 p :=
  nonnegative_ite (p 225) (nonnegative13 p) (nonnegative3719 p)
def d3721 (p : Pattern) : Int := if p 224 then d13 p else d3720 p
theorem agree3721 (p q : Pattern) (h : Agree support p q) : d3721 p = d3721 q := by
  simp only [d3721, h 224 (by decide), agree13 p q h, agree3720 p q h]
theorem nonnegative3721 (p : Pattern) : 0 ≤ d3721 p :=
  nonnegative_ite (p 224) (nonnegative13 p) (nonnegative3720 p)
def d3722 (p : Pattern) : Int := if p 204 then d3545 p else d3721 p
theorem agree3722 (p q : Pattern) (h : Agree support p q) : d3722 p = d3722 q := by
  simp only [d3722, h 204 (by decide), agree3545 p q h, agree3721 p q h]
theorem nonnegative3722 (p : Pattern) : 0 ≤ d3722 p :=
  nonnegative_ite (p 204) (nonnegative3545 p) (nonnegative3721 p)
def d3723 (p : Pattern) : Int := if p 182 then d3550 p else d3722 p
theorem agree3723 (p q : Pattern) (h : Agree support p q) : d3723 p = d3723 q := by
  simp only [d3723, h 182 (by decide), agree3550 p q h, agree3722 p q h]
theorem nonnegative3723 (p : Pattern) : 0 ≤ d3723 p :=
  nonnegative_ite (p 182) (nonnegative3550 p) (nonnegative3722 p)
def d3724 (p : Pattern) : Int := if p 163 then d3553 p else d3723 p
theorem agree3724 (p q : Pattern) (h : Agree support p q) : d3724 p = d3724 q := by
  simp only [d3724, h 163 (by decide), agree3553 p q h, agree3723 p q h]
theorem nonnegative3724 (p : Pattern) : 0 ≤ d3724 p :=
  nonnegative_ite (p 163) (nonnegative3553 p) (nonnegative3723 p)
def d3725 (p : Pattern) : Int := if p 162 then d3564 p else d3724 p
theorem agree3725 (p q : Pattern) (h : Agree support p q) : d3725 p = d3725 q := by
  simp only [d3725, h 162 (by decide), agree3564 p q h, agree3724 p q h]
theorem nonnegative3725 (p : Pattern) : 0 ≤ d3725 p :=
  nonnegative_ite (p 162) (nonnegative3564 p) (nonnegative3724 p)
def d3726 (p : Pattern) : Int := if p 161 then d3575 p else d3725 p
theorem agree3726 (p q : Pattern) (h : Agree support p q) : d3726 p = d3726 q := by
  simp only [d3726, h 161 (by decide), agree3575 p q h, agree3725 p q h]
theorem nonnegative3726 (p : Pattern) : 0 ≤ d3726 p :=
  nonnegative_ite (p 161) (nonnegative3575 p) (nonnegative3725 p)
def d3727 (p : Pattern) : Int := if p 160 then d3614 p else d3726 p
theorem agree3727 (p q : Pattern) (h : Agree support p q) : d3727 p = d3727 q := by
  simp only [d3727, h 160 (by decide), agree3614 p q h, agree3726 p q h]
theorem nonnegative3727 (p : Pattern) : 0 ≤ d3727 p :=
  nonnegative_ite (p 160) (nonnegative3614 p) (nonnegative3726 p)
def d3728 (p : Pattern) : Int := if p 141 then d3713 p else d3727 p
theorem agree3728 (p q : Pattern) (h : Agree support p q) : d3728 p = d3728 q := by
  simp only [d3728, h 141 (by decide), agree3713 p q h, agree3727 p q h]
theorem nonnegative3728 (p : Pattern) : 0 ≤ d3728 p :=
  nonnegative_ite (p 141) (nonnegative3713 p) (nonnegative3727 p)
def d3729 (p : Pattern) : Int := if p 138 then d3695 p else d3728 p
theorem agree3729 (p q : Pattern) (h : Agree support p q) : d3729 p = d3729 q := by
  simp only [d3729, h 138 (by decide), agree3695 p q h, agree3728 p q h]
theorem nonnegative3729 (p : Pattern) : 0 ≤ d3729 p :=
  nonnegative_ite (p 138) (nonnegative3695 p) (nonnegative3728 p)
def d3730 (p : Pattern) : Int := if p 116 then d3705 p else d3729 p
theorem agree3730 (p q : Pattern) (h : Agree support p q) : d3730 p = d3730 q := by
  simp only [d3730, h 116 (by decide), agree3705 p q h, agree3729 p q h]
theorem nonnegative3730 (p : Pattern) : 0 ≤ d3730 p :=
  nonnegative_ite (p 116) (nonnegative3705 p) (nonnegative3729 p)
def d3731 (p : Pattern) : Int := if p 115 then d3717 p else d3730 p
theorem agree3731 (p q : Pattern) (h : Agree support p q) : d3731 p = d3731 q := by
  simp only [d3731, h 115 (by decide), agree3717 p q h, agree3730 p q h]
theorem nonnegative3731 (p : Pattern) : 0 ≤ d3731 p :=
  nonnegative_ite (p 115) (nonnegative3717 p) (nonnegative3730 p)
def d3732 (p : Pattern) : Int := if p 71 then d3731 p else d3718 p
theorem agree3732 (p q : Pattern) (h : Agree support p q) : d3732 p = d3732 q := by
  simp only [d3732, h 71 (by decide), agree3731 p q h, agree3718 p q h]
theorem nonnegative3732 (p : Pattern) : 0 ≤ d3732 p :=
  nonnegative_ite (p 71) (nonnegative3731 p) (nonnegative3718 p)
def d3733 (p : Pattern) : Int := if p 246 then d102 p else d428 p
theorem agree3733 (p q : Pattern) (h : Agree support p q) : d3733 p = d3733 q := by
  simp only [d3733, h 246 (by decide), agree102 p q h, agree428 p q h]
theorem nonnegative3733 (p : Pattern) : 0 ≤ d3733 p :=
  nonnegative_ite (p 246) (nonnegative102 p) (nonnegative428 p)
def d3734 (p : Pattern) : Int := if p 225 then d102 p else d3733 p
theorem agree3734 (p q : Pattern) (h : Agree support p q) : d3734 p = d3734 q := by
  simp only [d3734, h 225 (by decide), agree102 p q h, agree3733 p q h]
theorem nonnegative3734 (p : Pattern) : 0 ≤ d3734 p :=
  nonnegative_ite (p 225) (nonnegative102 p) (nonnegative3733 p)
def d3735 (p : Pattern) : Int := if p 224 then d102 p else d3734 p
theorem agree3735 (p q : Pattern) (h : Agree support p q) : d3735 p = d3735 q := by
  simp only [d3735, h 224 (by decide), agree102 p q h, agree3734 p q h]
theorem nonnegative3735 (p : Pattern) : 0 ≤ d3735 p :=
  nonnegative_ite (p 224) (nonnegative102 p) (nonnegative3734 p)
def d3736 (p : Pattern) : Int := if p 246 then d106 p else d102 p
theorem agree3736 (p q : Pattern) (h : Agree support p q) : d3736 p = d3736 q := by
  simp only [d3736, h 246 (by decide), agree106 p q h, agree102 p q h]
theorem nonnegative3736 (p : Pattern) : 0 ≤ d3736 p :=
  nonnegative_ite (p 246) (nonnegative106 p) (nonnegative102 p)
def d3737 (p : Pattern) : Int := if p 225 then d3736 p else d102 p
theorem agree3737 (p q : Pattern) (h : Agree support p q) : d3737 p = d3737 q := by
  simp only [d3737, h 225 (by decide), agree3736 p q h, agree102 p q h]
theorem nonnegative3737 (p : Pattern) : 0 ≤ d3737 p :=
  nonnegative_ite (p 225) (nonnegative3736 p) (nonnegative102 p)
def d3738 (p : Pattern) : Int := if p 224 then d3736 p else d3737 p
theorem agree3738 (p q : Pattern) (h : Agree support p q) : d3738 p = d3738 q := by
  simp only [d3738, h 224 (by decide), agree3736 p q h, agree3737 p q h]
theorem nonnegative3738 (p : Pattern) : 0 ≤ d3738 p :=
  nonnegative_ite (p 224) (nonnegative3736 p) (nonnegative3737 p)
def d3739 (p : Pattern) : Int := if p 204 then d3738 p else d3735 p
theorem agree3739 (p q : Pattern) (h : Agree support p q) : d3739 p = d3739 q := by
  simp only [d3739, h 204 (by decide), agree3738 p q h, agree3735 p q h]
theorem nonnegative3739 (p : Pattern) : 0 ≤ d3739 p :=
  nonnegative_ite (p 204) (nonnegative3738 p) (nonnegative3735 p)
def d3740 (p : Pattern) : Int := if p 246 then d115 p else d102 p
theorem agree3740 (p q : Pattern) (h : Agree support p q) : d3740 p = d3740 q := by
  simp only [d3740, h 246 (by decide), agree115 p q h, agree102 p q h]
theorem nonnegative3740 (p : Pattern) : 0 ≤ d3740 p :=
  nonnegative_ite (p 246) (nonnegative115 p) (nonnegative102 p)
def d3741 (p : Pattern) : Int := if p 225 then d3740 p else d102 p
theorem agree3741 (p q : Pattern) (h : Agree support p q) : d3741 p = d3741 q := by
  simp only [d3741, h 225 (by decide), agree3740 p q h, agree102 p q h]
theorem nonnegative3741 (p : Pattern) : 0 ≤ d3741 p :=
  nonnegative_ite (p 225) (nonnegative3740 p) (nonnegative102 p)
def d3742 (p : Pattern) : Int := if p 224 then d3740 p else d3741 p
theorem agree3742 (p q : Pattern) (h : Agree support p q) : d3742 p = d3742 q := by
  simp only [d3742, h 224 (by decide), agree3740 p q h, agree3741 p q h]
theorem nonnegative3742 (p : Pattern) : 0 ≤ d3742 p :=
  nonnegative_ite (p 224) (nonnegative3740 p) (nonnegative3741 p)
def d3743 (p : Pattern) : Int := if p 204 then d12 p else d3742 p
theorem agree3743 (p q : Pattern) (h : Agree support p q) : d3743 p = d3743 q := by
  simp only [d3743, h 204 (by decide), agree12 p q h, agree3742 p q h]
theorem nonnegative3743 (p : Pattern) : 0 ≤ d3743 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3742 p)
def d3744 (p : Pattern) : Int := if p 182 then d3743 p else d3739 p
theorem agree3744 (p q : Pattern) (h : Agree support p q) : d3744 p = d3744 q := by
  simp only [d3744, h 182 (by decide), agree3743 p q h, agree3739 p q h]
theorem nonnegative3744 (p : Pattern) : 0 ≤ d3744 p :=
  nonnegative_ite (p 182) (nonnegative3743 p) (nonnegative3739 p)
def d3745 (p : Pattern) : Int := if p 204 then d3738 p else d102 p
theorem agree3745 (p q : Pattern) (h : Agree support p q) : d3745 p = d3745 q := by
  simp only [d3745, h 204 (by decide), agree3738 p q h, agree102 p q h]
theorem nonnegative3745 (p : Pattern) : 0 ≤ d3745 p :=
  nonnegative_ite (p 204) (nonnegative3738 p) (nonnegative102 p)
def d3746 (p : Pattern) : Int := if p 182 then d3743 p else d3745 p
theorem agree3746 (p q : Pattern) (h : Agree support p q) : d3746 p = d3746 q := by
  simp only [d3746, h 182 (by decide), agree3743 p q h, agree3745 p q h]
theorem nonnegative3746 (p : Pattern) : 0 ≤ d3746 p :=
  nonnegative_ite (p 182) (nonnegative3743 p) (nonnegative3745 p)
def d3747 (p : Pattern) : Int := if p 163 then d3746 p else d3744 p
theorem agree3747 (p q : Pattern) (h : Agree support p q) : d3747 p = d3747 q := by
  simp only [d3747, h 163 (by decide), agree3746 p q h, agree3744 p q h]
theorem nonnegative3747 (p : Pattern) : 0 ≤ d3747 p :=
  nonnegative_ite (p 163) (nonnegative3746 p) (nonnegative3744 p)
def d3748 (p : Pattern) : Int := if p 246 then d23 p else d106 p
theorem agree3748 (p q : Pattern) (h : Agree support p q) : d3748 p = d3748 q := by
  simp only [d3748, h 246 (by decide), agree23 p q h, agree106 p q h]
theorem nonnegative3748 (p : Pattern) : 0 ≤ d3748 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative106 p)
def d3749 (p : Pattern) : Int := if p 225 then d3748 p else d106 p
theorem agree3749 (p q : Pattern) (h : Agree support p q) : d3749 p = d3749 q := by
  simp only [d3749, h 225 (by decide), agree3748 p q h, agree106 p q h]
theorem nonnegative3749 (p : Pattern) : 0 ≤ d3749 p :=
  nonnegative_ite (p 225) (nonnegative3748 p) (nonnegative106 p)
def d3750 (p : Pattern) : Int := if p 224 then d3748 p else d3749 p
theorem agree3750 (p q : Pattern) (h : Agree support p q) : d3750 p = d3750 q := by
  simp only [d3750, h 224 (by decide), agree3748 p q h, agree3749 p q h]
theorem nonnegative3750 (p : Pattern) : 0 ≤ d3750 p :=
  nonnegative_ite (p 224) (nonnegative3748 p) (nonnegative3749 p)
def d3751 (p : Pattern) : Int := if p 204 then d3750 p else d106 p
theorem agree3751 (p q : Pattern) (h : Agree support p q) : d3751 p = d3751 q := by
  simp only [d3751, h 204 (by decide), agree3750 p q h, agree106 p q h]
theorem nonnegative3751 (p : Pattern) : 0 ≤ d3751 p :=
  nonnegative_ite (p 204) (nonnegative3750 p) (nonnegative106 p)
def d3752 (p : Pattern) : Int := if p 246 then d119 p else d106 p
theorem agree3752 (p q : Pattern) (h : Agree support p q) : d3752 p = d3752 q := by
  simp only [d3752, h 246 (by decide), agree119 p q h, agree106 p q h]
theorem nonnegative3752 (p : Pattern) : 0 ≤ d3752 p :=
  nonnegative_ite (p 246) (nonnegative119 p) (nonnegative106 p)
def d3753 (p : Pattern) : Int := if p 225 then d3752 p else d106 p
theorem agree3753 (p q : Pattern) (h : Agree support p q) : d3753 p = d3753 q := by
  simp only [d3753, h 225 (by decide), agree3752 p q h, agree106 p q h]
theorem nonnegative3753 (p : Pattern) : 0 ≤ d3753 p :=
  nonnegative_ite (p 225) (nonnegative3752 p) (nonnegative106 p)
def d3754 (p : Pattern) : Int := if p 224 then d3752 p else d3753 p
theorem agree3754 (p q : Pattern) (h : Agree support p q) : d3754 p = d3754 q := by
  simp only [d3754, h 224 (by decide), agree3752 p q h, agree3753 p q h]
theorem nonnegative3754 (p : Pattern) : 0 ≤ d3754 p :=
  nonnegative_ite (p 224) (nonnegative3752 p) (nonnegative3753 p)
def d3755 (p : Pattern) : Int := if p 204 then d12 p else d3754 p
theorem agree3755 (p q : Pattern) (h : Agree support p q) : d3755 p = d3755 q := by
  simp only [d3755, h 204 (by decide), agree12 p q h, agree3754 p q h]
theorem nonnegative3755 (p : Pattern) : 0 ≤ d3755 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3754 p)
def d3756 (p : Pattern) : Int := if p 182 then d3755 p else d3751 p
theorem agree3756 (p q : Pattern) (h : Agree support p q) : d3756 p = d3756 q := by
  simp only [d3756, h 182 (by decide), agree3755 p q h, agree3751 p q h]
theorem nonnegative3756 (p : Pattern) : 0 ≤ d3756 p :=
  nonnegative_ite (p 182) (nonnegative3755 p) (nonnegative3751 p)
def d3757 (p : Pattern) : Int := if p 163 then d3756 p else d3746 p
theorem agree3757 (p q : Pattern) (h : Agree support p q) : d3757 p = d3757 q := by
  simp only [d3757, h 163 (by decide), agree3756 p q h, agree3746 p q h]
theorem nonnegative3757 (p : Pattern) : 0 ≤ d3757 p :=
  nonnegative_ite (p 163) (nonnegative3756 p) (nonnegative3746 p)
def d3758 (p : Pattern) : Int := if p 162 then d3757 p else d3747 p
theorem agree3758 (p q : Pattern) (h : Agree support p q) : d3758 p = d3758 q := by
  simp only [d3758, h 162 (by decide), agree3757 p q h, agree3747 p q h]
theorem nonnegative3758 (p : Pattern) : 0 ≤ d3758 p :=
  nonnegative_ite (p 162) (nonnegative3757 p) (nonnegative3747 p)
def d3759 (p : Pattern) : Int := if p 163 then d12 p else d3636 p
theorem agree3759 (p q : Pattern) (h : Agree support p q) : d3759 p = d3759 q := by
  simp only [d3759, h 163 (by decide), agree12 p q h, agree3636 p q h]
theorem nonnegative3759 (p : Pattern) : 0 ≤ d3759 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3636 p)
def d3760 (p : Pattern) : Int := if p 162 then d3759 p else d3757 p
theorem agree3760 (p q : Pattern) (h : Agree support p q) : d3760 p = d3760 q := by
  simp only [d3760, h 162 (by decide), agree3759 p q h, agree3757 p q h]
theorem nonnegative3760 (p : Pattern) : 0 ≤ d3760 p :=
  nonnegative_ite (p 162) (nonnegative3759 p) (nonnegative3757 p)
def d3761 (p : Pattern) : Int := if p 161 then d3760 p else d3758 p
theorem agree3761 (p q : Pattern) (h : Agree support p q) : d3761 p = d3761 q := by
  simp only [d3761, h 161 (by decide), agree3760 p q h, agree3758 p q h]
theorem nonnegative3761 (p : Pattern) : 0 ≤ d3761 p :=
  nonnegative_ite (p 161) (nonnegative3760 p) (nonnegative3758 p)
def d3762 (p : Pattern) : Int := if p 246 then d119 p else d102 p
theorem agree3762 (p q : Pattern) (h : Agree support p q) : d3762 p = d3762 q := by
  simp only [d3762, h 246 (by decide), agree119 p q h, agree102 p q h]
theorem nonnegative3762 (p : Pattern) : 0 ≤ d3762 p :=
  nonnegative_ite (p 246) (nonnegative119 p) (nonnegative102 p)
def d3763 (p : Pattern) : Int := if p 225 then d3762 p else d102 p
theorem agree3763 (p q : Pattern) (h : Agree support p q) : d3763 p = d3763 q := by
  simp only [d3763, h 225 (by decide), agree3762 p q h, agree102 p q h]
theorem nonnegative3763 (p : Pattern) : 0 ≤ d3763 p :=
  nonnegative_ite (p 225) (nonnegative3762 p) (nonnegative102 p)
def d3764 (p : Pattern) : Int := if p 225 then d1955 p else d3736 p
theorem agree3764 (p q : Pattern) (h : Agree support p q) : d3764 p = d3764 q := by
  simp only [d3764, h 225 (by decide), agree1955 p q h, agree3736 p q h]
theorem nonnegative3764 (p : Pattern) : 0 ≤ d3764 p :=
  nonnegative_ite (p 225) (nonnegative1955 p) (nonnegative3736 p)
def d3765 (p : Pattern) : Int := if p 224 then d3764 p else d3763 p
theorem agree3765 (p q : Pattern) (h : Agree support p q) : d3765 p = d3765 q := by
  simp only [d3765, h 224 (by decide), agree3764 p q h, agree3763 p q h]
theorem nonnegative3765 (p : Pattern) : 0 ≤ d3765 p :=
  nonnegative_ite (p 224) (nonnegative3764 p) (nonnegative3763 p)
def d3766 (p : Pattern) : Int := if p 204 then d3765 p else d102 p
theorem agree3766 (p q : Pattern) (h : Agree support p q) : d3766 p = d3766 q := by
  simp only [d3766, h 204 (by decide), agree3765 p q h, agree102 p q h]
theorem nonnegative3766 (p : Pattern) : 0 ≤ d3766 p :=
  nonnegative_ite (p 204) (nonnegative3765 p) (nonnegative102 p)
def d3767 (p : Pattern) : Int := if p 246 then d23 p else d115 p
theorem agree3767 (p q : Pattern) (h : Agree support p q) : d3767 p = d3767 q := by
  simp only [d3767, h 246 (by decide), agree23 p q h, agree115 p q h]
theorem nonnegative3767 (p : Pattern) : 0 ≤ d3767 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative115 p)
def d3768 (p : Pattern) : Int := if p 225 then d3767 p else d115 p
theorem agree3768 (p q : Pattern) (h : Agree support p q) : d3768 p = d3768 q := by
  simp only [d3768, h 225 (by decide), agree3767 p q h, agree115 p q h]
theorem nonnegative3768 (p : Pattern) : 0 ≤ d3768 p :=
  nonnegative_ite (p 225) (nonnegative3767 p) (nonnegative115 p)
def d3769 (p : Pattern) : Int := if p 246 then d119 p else d115 p
theorem agree3769 (p q : Pattern) (h : Agree support p q) : d3769 p = d3769 q := by
  simp only [d3769, h 246 (by decide), agree119 p q h, agree115 p q h]
theorem nonnegative3769 (p : Pattern) : 0 ≤ d3769 p :=
  nonnegative_ite (p 246) (nonnegative119 p) (nonnegative115 p)
def d3770 (p : Pattern) : Int := if p 225 then d1896 p else d3769 p
theorem agree3770 (p q : Pattern) (h : Agree support p q) : d3770 p = d3770 q := by
  simp only [d3770, h 225 (by decide), agree1896 p q h, agree3769 p q h]
theorem nonnegative3770 (p : Pattern) : 0 ≤ d3770 p :=
  nonnegative_ite (p 225) (nonnegative1896 p) (nonnegative3769 p)
def d3771 (p : Pattern) : Int := if p 224 then d3770 p else d3768 p
theorem agree3771 (p q : Pattern) (h : Agree support p q) : d3771 p = d3771 q := by
  simp only [d3771, h 224 (by decide), agree3770 p q h, agree3768 p q h]
theorem nonnegative3771 (p : Pattern) : 0 ≤ d3771 p :=
  nonnegative_ite (p 224) (nonnegative3770 p) (nonnegative3768 p)
def d3772 (p : Pattern) : Int := if p 204 then d12 p else d3771 p
theorem agree3772 (p q : Pattern) (h : Agree support p q) : d3772 p = d3772 q := by
  simp only [d3772, h 204 (by decide), agree12 p q h, agree3771 p q h]
theorem nonnegative3772 (p : Pattern) : 0 ≤ d3772 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3771 p)
def d3773 (p : Pattern) : Int := if p 182 then d3772 p else d3766 p
theorem agree3773 (p q : Pattern) (h : Agree support p q) : d3773 p = d3773 q := by
  simp only [d3773, h 182 (by decide), agree3772 p q h, agree3766 p q h]
theorem nonnegative3773 (p : Pattern) : 0 ≤ d3773 p :=
  nonnegative_ite (p 182) (nonnegative3772 p) (nonnegative3766 p)
def d3774 (p : Pattern) : Int := if p 225 then d317 p else d119 p
theorem agree3774 (p q : Pattern) (h : Agree support p q) : d3774 p = d3774 q := by
  simp only [d3774, h 225 (by decide), agree317 p q h, agree119 p q h]
theorem nonnegative3774 (p : Pattern) : 0 ≤ d3774 p :=
  nonnegative_ite (p 225) (nonnegative317 p) (nonnegative119 p)
def d3775 (p : Pattern) : Int := if p 246 then d39 p else d119 p
theorem agree3775 (p q : Pattern) (h : Agree support p q) : d3775 p = d3775 q := by
  simp only [d3775, h 246 (by decide), agree39 p q h, agree119 p q h]
theorem nonnegative3775 (p : Pattern) : 0 ≤ d3775 p :=
  nonnegative_ite (p 246) (nonnegative39 p) (nonnegative119 p)
def d3776 (p : Pattern) : Int := if p 225 then d317 p else d3775 p
theorem agree3776 (p q : Pattern) (h : Agree support p q) : d3776 p = d3776 q := by
  simp only [d3776, h 225 (by decide), agree317 p q h, agree3775 p q h]
theorem nonnegative3776 (p : Pattern) : 0 ≤ d3776 p :=
  nonnegative_ite (p 225) (nonnegative317 p) (nonnegative3775 p)
def d3777 (p : Pattern) : Int := if p 224 then d3776 p else d3774 p
theorem agree3777 (p q : Pattern) (h : Agree support p q) : d3777 p = d3777 q := by
  simp only [d3777, h 224 (by decide), agree3776 p q h, agree3774 p q h]
theorem nonnegative3777 (p : Pattern) : 0 ≤ d3777 p :=
  nonnegative_ite (p 224) (nonnegative3776 p) (nonnegative3774 p)
def d3778 (p : Pattern) : Int := if p 204 then d12 p else d3777 p
theorem agree3778 (p q : Pattern) (h : Agree support p q) : d3778 p = d3778 q := by
  simp only [d3778, h 204 (by decide), agree12 p q h, agree3777 p q h]
theorem nonnegative3778 (p : Pattern) : 0 ≤ d3778 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3777 p)
def d3779 (p : Pattern) : Int := if p 182 then d3778 p else d3766 p
theorem agree3779 (p q : Pattern) (h : Agree support p q) : d3779 p = d3779 q := by
  simp only [d3779, h 182 (by decide), agree3778 p q h, agree3766 p q h]
theorem nonnegative3779 (p : Pattern) : 0 ≤ d3779 p :=
  nonnegative_ite (p 182) (nonnegative3778 p) (nonnegative3766 p)
def d3780 (p : Pattern) : Int := if p 163 then d3779 p else d3773 p
theorem agree3780 (p q : Pattern) (h : Agree support p q) : d3780 p = d3780 q := by
  simp only [d3780, h 163 (by decide), agree3779 p q h, agree3773 p q h]
theorem nonnegative3780 (p : Pattern) : 0 ≤ d3780 p :=
  nonnegative_ite (p 163) (nonnegative3779 p) (nonnegative3773 p)
def d3781 (p : Pattern) : Int := if p 182 then d12 p else d3766 p
theorem agree3781 (p q : Pattern) (h : Agree support p q) : d3781 p = d3781 q := by
  simp only [d3781, h 182 (by decide), agree12 p q h, agree3766 p q h]
theorem nonnegative3781 (p : Pattern) : 0 ≤ d3781 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3766 p)
def d3782 (p : Pattern) : Int := if p 246 then d39 p else d106 p
theorem agree3782 (p q : Pattern) (h : Agree support p q) : d3782 p = d3782 q := by
  simp only [d3782, h 246 (by decide), agree39 p q h, agree106 p q h]
theorem nonnegative3782 (p : Pattern) : 0 ≤ d3782 p :=
  nonnegative_ite (p 246) (nonnegative39 p) (nonnegative106 p)
def d3783 (p : Pattern) : Int := if p 225 then d3782 p else d106 p
theorem agree3783 (p q : Pattern) (h : Agree support p q) : d3783 p = d3783 q := by
  simp only [d3783, h 225 (by decide), agree3782 p q h, agree106 p q h]
theorem nonnegative3783 (p : Pattern) : 0 ≤ d3783 p :=
  nonnegative_ite (p 225) (nonnegative3782 p) (nonnegative106 p)
def d3784 (p : Pattern) : Int := if p 225 then d348 p else d3748 p
theorem agree3784 (p q : Pattern) (h : Agree support p q) : d3784 p = d3784 q := by
  simp only [d3784, h 225 (by decide), agree348 p q h, agree3748 p q h]
theorem nonnegative3784 (p : Pattern) : 0 ≤ d3784 p :=
  nonnegative_ite (p 225) (nonnegative348 p) (nonnegative3748 p)
def d3785 (p : Pattern) : Int := if p 224 then d3784 p else d3783 p
theorem agree3785 (p q : Pattern) (h : Agree support p q) : d3785 p = d3785 q := by
  simp only [d3785, h 224 (by decide), agree3784 p q h, agree3783 p q h]
theorem nonnegative3785 (p : Pattern) : 0 ≤ d3785 p :=
  nonnegative_ite (p 224) (nonnegative3784 p) (nonnegative3783 p)
def d3786 (p : Pattern) : Int := if p 204 then d3785 p else d106 p
theorem agree3786 (p q : Pattern) (h : Agree support p q) : d3786 p = d3786 q := by
  simp only [d3786, h 204 (by decide), agree3785 p q h, agree106 p q h]
theorem nonnegative3786 (p : Pattern) : 0 ≤ d3786 p :=
  nonnegative_ite (p 204) (nonnegative3785 p) (nonnegative106 p)
def d3787 (p : Pattern) : Int := if p 182 then d12 p else d3786 p
theorem agree3787 (p q : Pattern) (h : Agree support p q) : d3787 p = d3787 q := by
  simp only [d3787, h 182 (by decide), agree12 p q h, agree3786 p q h]
theorem nonnegative3787 (p : Pattern) : 0 ≤ d3787 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3786 p)
def d3788 (p : Pattern) : Int := if p 163 then d3787 p else d3781 p
theorem agree3788 (p q : Pattern) (h : Agree support p q) : d3788 p = d3788 q := by
  simp only [d3788, h 163 (by decide), agree3787 p q h, agree3781 p q h]
theorem nonnegative3788 (p : Pattern) : 0 ≤ d3788 p :=
  nonnegative_ite (p 163) (nonnegative3787 p) (nonnegative3781 p)
def d3789 (p : Pattern) : Int := if p 162 then d3788 p else d3780 p
theorem agree3789 (p q : Pattern) (h : Agree support p q) : d3789 p = d3789 q := by
  simp only [d3789, h 162 (by decide), agree3788 p q h, agree3780 p q h]
theorem nonnegative3789 (p : Pattern) : 0 ≤ d3789 p :=
  nonnegative_ite (p 162) (nonnegative3788 p) (nonnegative3780 p)
def d3790 (p : Pattern) : Int := if p 163 then d12 p else d3648 p
theorem agree3790 (p q : Pattern) (h : Agree support p q) : d3790 p = d3790 q := by
  simp only [d3790, h 163 (by decide), agree12 p q h, agree3648 p q h]
theorem nonnegative3790 (p : Pattern) : 0 ≤ d3790 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3648 p)
def d3791 (p : Pattern) : Int := if p 162 then d3790 p else d3788 p
theorem agree3791 (p q : Pattern) (h : Agree support p q) : d3791 p = d3791 q := by
  simp only [d3791, h 162 (by decide), agree3790 p q h, agree3788 p q h]
theorem nonnegative3791 (p : Pattern) : 0 ≤ d3791 p :=
  nonnegative_ite (p 162) (nonnegative3790 p) (nonnegative3788 p)
def d3792 (p : Pattern) : Int := if p 161 then d3791 p else d3789 p
theorem agree3792 (p q : Pattern) (h : Agree support p q) : d3792 p = d3792 q := by
  simp only [d3792, h 161 (by decide), agree3791 p q h, agree3789 p q h]
theorem nonnegative3792 (p : Pattern) : 0 ≤ d3792 p :=
  nonnegative_ite (p 161) (nonnegative3791 p) (nonnegative3789 p)
def d3793 (p : Pattern) : Int := if p 160 then d3792 p else d3761 p
theorem agree3793 (p q : Pattern) (h : Agree support p q) : d3793 p = d3793 q := by
  simp only [d3793, h 160 (by decide), agree3792 p q h, agree3761 p q h]
theorem nonnegative3793 (p : Pattern) : 0 ≤ d3793 p :=
  nonnegative_ite (p 160) (nonnegative3792 p) (nonnegative3761 p)
def d3794 (p : Pattern) : Int := if p 225 then d3769 p else d115 p
theorem agree3794 (p q : Pattern) (h : Agree support p q) : d3794 p = d3794 q := by
  simp only [d3794, h 225 (by decide), agree3769 p q h, agree115 p q h]
theorem nonnegative3794 (p : Pattern) : 0 ≤ d3794 p :=
  nonnegative_ite (p 225) (nonnegative3769 p) (nonnegative115 p)
def d3795 (p : Pattern) : Int := if p 224 then d3769 p else d3794 p
theorem agree3795 (p q : Pattern) (h : Agree support p q) : d3795 p = d3795 q := by
  simp only [d3795, h 224 (by decide), agree3769 p q h, agree3794 p q h]
theorem nonnegative3795 (p : Pattern) : 0 ≤ d3795 p :=
  nonnegative_ite (p 224) (nonnegative3769 p) (nonnegative3794 p)
def d3796 (p : Pattern) : Int := if p 204 then d3795 p else d115 p
theorem agree3796 (p q : Pattern) (h : Agree support p q) : d3796 p = d3796 q := by
  simp only [d3796, h 204 (by decide), agree3795 p q h, agree115 p q h]
theorem nonnegative3796 (p : Pattern) : 0 ≤ d3796 p :=
  nonnegative_ite (p 204) (nonnegative3795 p) (nonnegative115 p)
def d3797 (p : Pattern) : Int := if p 246 then d106 p else d115 p
theorem agree3797 (p q : Pattern) (h : Agree support p q) : d3797 p = d3797 q := by
  simp only [d3797, h 246 (by decide), agree106 p q h, agree115 p q h]
theorem nonnegative3797 (p : Pattern) : 0 ≤ d3797 p :=
  nonnegative_ite (p 246) (nonnegative106 p) (nonnegative115 p)
def d3798 (p : Pattern) : Int := if p 225 then d3797 p else d115 p
theorem agree3798 (p q : Pattern) (h : Agree support p q) : d3798 p = d3798 q := by
  simp only [d3798, h 225 (by decide), agree3797 p q h, agree115 p q h]
theorem nonnegative3798 (p : Pattern) : 0 ≤ d3798 p :=
  nonnegative_ite (p 225) (nonnegative3797 p) (nonnegative115 p)
def d3799 (p : Pattern) : Int := if p 224 then d3797 p else d3798 p
theorem agree3799 (p q : Pattern) (h : Agree support p q) : d3799 p = d3799 q := by
  simp only [d3799, h 224 (by decide), agree3797 p q h, agree3798 p q h]
theorem nonnegative3799 (p : Pattern) : 0 ≤ d3799 p :=
  nonnegative_ite (p 224) (nonnegative3797 p) (nonnegative3798 p)
def d3800 (p : Pattern) : Int := if p 204 then d12 p else d3799 p
theorem agree3800 (p q : Pattern) (h : Agree support p q) : d3800 p = d3800 q := by
  simp only [d3800, h 204 (by decide), agree12 p q h, agree3799 p q h]
theorem nonnegative3800 (p : Pattern) : 0 ≤ d3800 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3799 p)
def d3801 (p : Pattern) : Int := if p 182 then d3800 p else d3796 p
theorem agree3801 (p q : Pattern) (h : Agree support p q) : d3801 p = d3801 q := by
  simp only [d3801, h 182 (by decide), agree3800 p q h, agree3796 p q h]
theorem nonnegative3801 (p : Pattern) : 0 ≤ d3801 p :=
  nonnegative_ite (p 182) (nonnegative3800 p) (nonnegative3796 p)
def d3802 (p : Pattern) : Int := if p 163 then d3801 p else d3746 p
theorem agree3802 (p q : Pattern) (h : Agree support p q) : d3802 p = d3802 q := by
  simp only [d3802, h 163 (by decide), agree3801 p q h, agree3746 p q h]
theorem nonnegative3802 (p : Pattern) : 0 ≤ d3802 p :=
  nonnegative_ite (p 163) (nonnegative3801 p) (nonnegative3746 p)
def d3803 (p : Pattern) : Int := if p 163 then d3636 p else d3756 p
theorem agree3803 (p q : Pattern) (h : Agree support p q) : d3803 p = d3803 q := by
  simp only [d3803, h 163 (by decide), agree3636 p q h, agree3756 p q h]
theorem nonnegative3803 (p : Pattern) : 0 ≤ d3803 p :=
  nonnegative_ite (p 163) (nonnegative3636 p) (nonnegative3756 p)
def d3804 (p : Pattern) : Int := if p 162 then d3803 p else d3802 p
theorem agree3804 (p q : Pattern) (h : Agree support p q) : d3804 p = d3804 q := by
  simp only [d3804, h 162 (by decide), agree3803 p q h, agree3802 p q h]
theorem nonnegative3804 (p : Pattern) : 0 ≤ d3804 p :=
  nonnegative_ite (p 162) (nonnegative3803 p) (nonnegative3802 p)
def d3805 (p : Pattern) : Int := if p 163 then d3639 p else d3756 p
theorem agree3805 (p q : Pattern) (h : Agree support p q) : d3805 p = d3805 q := by
  simp only [d3805, h 163 (by decide), agree3639 p q h, agree3756 p q h]
theorem nonnegative3805 (p : Pattern) : 0 ≤ d3805 p :=
  nonnegative_ite (p 163) (nonnegative3639 p) (nonnegative3756 p)
def d3806 (p : Pattern) : Int := if p 162 then d12 p else d3805 p
theorem agree3806 (p q : Pattern) (h : Agree support p q) : d3806 p = d3806 q := by
  simp only [d3806, h 162 (by decide), agree12 p q h, agree3805 p q h]
theorem nonnegative3806 (p : Pattern) : 0 ≤ d3806 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3805 p)
def d3807 (p : Pattern) : Int := if p 161 then d3806 p else d3804 p
theorem agree3807 (p q : Pattern) (h : Agree support p q) : d3807 p = d3807 q := by
  simp only [d3807, h 161 (by decide), agree3806 p q h, agree3804 p q h]
theorem nonnegative3807 (p : Pattern) : 0 ≤ d3807 p :=
  nonnegative_ite (p 161) (nonnegative3806 p) (nonnegative3804 p)
def d3808 (p : Pattern) : Int := if p 204 then d3771 p else d115 p
theorem agree3808 (p q : Pattern) (h : Agree support p q) : d3808 p = d3808 q := by
  simp only [d3808, h 204 (by decide), agree3771 p q h, agree115 p q h]
theorem nonnegative3808 (p : Pattern) : 0 ≤ d3808 p :=
  nonnegative_ite (p 204) (nonnegative3771 p) (nonnegative115 p)
def d3809 (p : Pattern) : Int := if p 182 then d12 p else d3808 p
theorem agree3809 (p q : Pattern) (h : Agree support p q) : d3809 p = d3809 q := by
  simp only [d3809, h 182 (by decide), agree12 p q h, agree3808 p q h]
theorem nonnegative3809 (p : Pattern) : 0 ≤ d3809 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3808 p)
def d3810 (p : Pattern) : Int := if p 163 then d3809 p else d3779 p
theorem agree3810 (p q : Pattern) (h : Agree support p q) : d3810 p = d3810 q := by
  simp only [d3810, h 163 (by decide), agree3809 p q h, agree3779 p q h]
theorem nonnegative3810 (p : Pattern) : 0 ≤ d3810 p :=
  nonnegative_ite (p 163) (nonnegative3809 p) (nonnegative3779 p)
def d3811 (p : Pattern) : Int := if p 163 then d3648 p else d3787 p
theorem agree3811 (p q : Pattern) (h : Agree support p q) : d3811 p = d3811 q := by
  simp only [d3811, h 163 (by decide), agree3648 p q h, agree3787 p q h]
theorem nonnegative3811 (p : Pattern) : 0 ≤ d3811 p :=
  nonnegative_ite (p 163) (nonnegative3648 p) (nonnegative3787 p)
def d3812 (p : Pattern) : Int := if p 162 then d3811 p else d3810 p
theorem agree3812 (p q : Pattern) (h : Agree support p q) : d3812 p = d3812 q := by
  simp only [d3812, h 162 (by decide), agree3811 p q h, agree3810 p q h]
theorem nonnegative3812 (p : Pattern) : 0 ≤ d3812 p :=
  nonnegative_ite (p 162) (nonnegative3811 p) (nonnegative3810 p)
def d3813 (p : Pattern) : Int := if p 163 then d3650 p else d3787 p
theorem agree3813 (p q : Pattern) (h : Agree support p q) : d3813 p = d3813 q := by
  simp only [d3813, h 163 (by decide), agree3650 p q h, agree3787 p q h]
theorem nonnegative3813 (p : Pattern) : 0 ≤ d3813 p :=
  nonnegative_ite (p 163) (nonnegative3650 p) (nonnegative3787 p)
def d3814 (p : Pattern) : Int := if p 162 then d12 p else d3813 p
theorem agree3814 (p q : Pattern) (h : Agree support p q) : d3814 p = d3814 q := by
  simp only [d3814, h 162 (by decide), agree12 p q h, agree3813 p q h]
theorem nonnegative3814 (p : Pattern) : 0 ≤ d3814 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3813 p)
def d3815 (p : Pattern) : Int := if p 161 then d3814 p else d3812 p
theorem agree3815 (p q : Pattern) (h : Agree support p q) : d3815 p = d3815 q := by
  simp only [d3815, h 161 (by decide), agree3814 p q h, agree3812 p q h]
theorem nonnegative3815 (p : Pattern) : 0 ≤ d3815 p :=
  nonnegative_ite (p 161) (nonnegative3814 p) (nonnegative3812 p)
def d3816 (p : Pattern) : Int := if p 160 then d3815 p else d3807 p
theorem agree3816 (p q : Pattern) (h : Agree support p q) : d3816 p = d3816 q := by
  simp only [d3816, h 160 (by decide), agree3815 p q h, agree3807 p q h]
theorem nonnegative3816 (p : Pattern) : 0 ≤ d3816 p :=
  nonnegative_ite (p 160) (nonnegative3815 p) (nonnegative3807 p)
def d3817 (p : Pattern) : Int := if p 141 then d3816 p else d3793 p
theorem agree3817 (p q : Pattern) (h : Agree support p q) : d3817 p = d3817 q := by
  simp only [d3817, h 141 (by decide), agree3816 p q h, agree3793 p q h]
theorem nonnegative3817 (p : Pattern) : 0 ≤ d3817 p :=
  nonnegative_ite (p 141) (nonnegative3816 p) (nonnegative3793 p)
def d3818 (p : Pattern) : Int := if p 225 then d3762 p else d3736 p
theorem agree3818 (p q : Pattern) (h : Agree support p q) : d3818 p = d3818 q := by
  simp only [d3818, h 225 (by decide), agree3762 p q h, agree3736 p q h]
theorem nonnegative3818 (p : Pattern) : 0 ≤ d3818 p :=
  nonnegative_ite (p 225) (nonnegative3762 p) (nonnegative3736 p)
def d3819 (p : Pattern) : Int := if p 224 then d3818 p else d3763 p
theorem agree3819 (p q : Pattern) (h : Agree support p q) : d3819 p = d3819 q := by
  simp only [d3819, h 224 (by decide), agree3818 p q h, agree3763 p q h]
theorem nonnegative3819 (p : Pattern) : 0 ≤ d3819 p :=
  nonnegative_ite (p 224) (nonnegative3818 p) (nonnegative3763 p)
def d3820 (p : Pattern) : Int := if p 204 then d3819 p else d102 p
theorem agree3820 (p q : Pattern) (h : Agree support p q) : d3820 p = d3820 q := by
  simp only [d3820, h 204 (by decide), agree3819 p q h, agree102 p q h]
theorem nonnegative3820 (p : Pattern) : 0 ≤ d3820 p :=
  nonnegative_ite (p 204) (nonnegative3819 p) (nonnegative102 p)
def d3821 (p : Pattern) : Int := if p 204 then d12 p else d3738 p
theorem agree3821 (p q : Pattern) (h : Agree support p q) : d3821 p = d3821 q := by
  simp only [d3821, h 204 (by decide), agree12 p q h, agree3738 p q h]
theorem nonnegative3821 (p : Pattern) : 0 ≤ d3821 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3738 p)
def d3822 (p : Pattern) : Int := if p 182 then d3821 p else d3820 p
theorem agree3822 (p q : Pattern) (h : Agree support p q) : d3822 p = d3822 q := by
  simp only [d3822, h 182 (by decide), agree3821 p q h, agree3820 p q h]
theorem nonnegative3822 (p : Pattern) : 0 ≤ d3822 p :=
  nonnegative_ite (p 182) (nonnegative3821 p) (nonnegative3820 p)
def d3823 (p : Pattern) : Int := if p 246 then d23 p else d102 p
theorem agree3823 (p q : Pattern) (h : Agree support p q) : d3823 p = d3823 q := by
  simp only [d3823, h 246 (by decide), agree23 p q h, agree102 p q h]
theorem nonnegative3823 (p : Pattern) : 0 ≤ d3823 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative102 p)
def d3824 (p : Pattern) : Int := if p 225 then d3823 p else d3736 p
theorem agree3824 (p q : Pattern) (h : Agree support p q) : d3824 p = d3824 q := by
  simp only [d3824, h 225 (by decide), agree3823 p q h, agree3736 p q h]
theorem nonnegative3824 (p : Pattern) : 0 ≤ d3824 p :=
  nonnegative_ite (p 225) (nonnegative3823 p) (nonnegative3736 p)
def d3825 (p : Pattern) : Int := if p 224 then d3824 p else d3763 p
theorem agree3825 (p q : Pattern) (h : Agree support p q) : d3825 p = d3825 q := by
  simp only [d3825, h 224 (by decide), agree3824 p q h, agree3763 p q h]
theorem nonnegative3825 (p : Pattern) : 0 ≤ d3825 p :=
  nonnegative_ite (p 224) (nonnegative3824 p) (nonnegative3763 p)
def d3826 (p : Pattern) : Int := if p 204 then d12 p else d3825 p
theorem agree3826 (p q : Pattern) (h : Agree support p q) : d3826 p = d3826 q := by
  simp only [d3826, h 204 (by decide), agree12 p q h, agree3825 p q h]
theorem nonnegative3826 (p : Pattern) : 0 ≤ d3826 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3825 p)
def d3827 (p : Pattern) : Int := if p 182 then d3826 p else d3766 p
theorem agree3827 (p q : Pattern) (h : Agree support p q) : d3827 p = d3827 q := by
  simp only [d3827, h 182 (by decide), agree3826 p q h, agree3766 p q h]
theorem nonnegative3827 (p : Pattern) : 0 ≤ d3827 p :=
  nonnegative_ite (p 182) (nonnegative3826 p) (nonnegative3766 p)
def d3828 (p : Pattern) : Int := if p 163 then d3827 p else d3822 p
theorem agree3828 (p q : Pattern) (h : Agree support p q) : d3828 p = d3828 q := by
  simp only [d3828, h 163 (by decide), agree3827 p q h, agree3822 p q h]
theorem nonnegative3828 (p : Pattern) : 0 ≤ d3828 p :=
  nonnegative_ite (p 163) (nonnegative3827 p) (nonnegative3822 p)
def d3829 (p : Pattern) : Int := if p 204 then d12 p else d3765 p
theorem agree3829 (p q : Pattern) (h : Agree support p q) : d3829 p = d3829 q := by
  simp only [d3829, h 204 (by decide), agree12 p q h, agree3765 p q h]
theorem nonnegative3829 (p : Pattern) : 0 ≤ d3829 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3765 p)
def d3830 (p : Pattern) : Int := if p 182 then d3829 p else d3766 p
theorem agree3830 (p q : Pattern) (h : Agree support p q) : d3830 p = d3830 q := by
  simp only [d3830, h 182 (by decide), agree3829 p q h, agree3766 p q h]
theorem nonnegative3830 (p : Pattern) : 0 ≤ d3830 p :=
  nonnegative_ite (p 182) (nonnegative3829 p) (nonnegative3766 p)
def d3831 (p : Pattern) : Int := if p 204 then d12 p else d3785 p
theorem agree3831 (p q : Pattern) (h : Agree support p q) : d3831 p = d3831 q := by
  simp only [d3831, h 204 (by decide), agree12 p q h, agree3785 p q h]
theorem nonnegative3831 (p : Pattern) : 0 ≤ d3831 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3785 p)
def d3832 (p : Pattern) : Int := if p 182 then d3831 p else d3786 p
theorem agree3832 (p q : Pattern) (h : Agree support p q) : d3832 p = d3832 q := by
  simp only [d3832, h 182 (by decide), agree3831 p q h, agree3786 p q h]
theorem nonnegative3832 (p : Pattern) : 0 ≤ d3832 p :=
  nonnegative_ite (p 182) (nonnegative3831 p) (nonnegative3786 p)
def d3833 (p : Pattern) : Int := if p 163 then d3832 p else d3830 p
theorem agree3833 (p q : Pattern) (h : Agree support p q) : d3833 p = d3833 q := by
  simp only [d3833, h 163 (by decide), agree3832 p q h, agree3830 p q h]
theorem nonnegative3833 (p : Pattern) : 0 ≤ d3833 p :=
  nonnegative_ite (p 163) (nonnegative3832 p) (nonnegative3830 p)
def d3834 (p : Pattern) : Int := if p 162 then d3833 p else d3828 p
theorem agree3834 (p q : Pattern) (h : Agree support p q) : d3834 p = d3834 q := by
  simp only [d3834, h 162 (by decide), agree3833 p q h, agree3828 p q h]
theorem nonnegative3834 (p : Pattern) : 0 ≤ d3834 p :=
  nonnegative_ite (p 162) (nonnegative3833 p) (nonnegative3828 p)
def d3835 (p : Pattern) : Int := if p 162 then d3759 p else d3833 p
theorem agree3835 (p q : Pattern) (h : Agree support p q) : d3835 p = d3835 q := by
  simp only [d3835, h 162 (by decide), agree3759 p q h, agree3833 p q h]
theorem nonnegative3835 (p : Pattern) : 0 ≤ d3835 p :=
  nonnegative_ite (p 162) (nonnegative3759 p) (nonnegative3833 p)
def d3836 (p : Pattern) : Int := if p 161 then d3835 p else d3834 p
theorem agree3836 (p q : Pattern) (h : Agree support p q) : d3836 p = d3836 q := by
  simp only [d3836, h 161 (by decide), agree3835 p q h, agree3834 p q h]
theorem nonnegative3836 (p : Pattern) : 0 ≤ d3836 p :=
  nonnegative_ite (p 161) (nonnegative3835 p) (nonnegative3834 p)
def d3837 (p : Pattern) : Int := if p 182 then d3772 p else d3808 p
theorem agree3837 (p q : Pattern) (h : Agree support p q) : d3837 p = d3837 q := by
  simp only [d3837, h 182 (by decide), agree3772 p q h, agree3808 p q h]
theorem nonnegative3837 (p : Pattern) : 0 ≤ d3837 p :=
  nonnegative_ite (p 182) (nonnegative3772 p) (nonnegative3808 p)
def d3838 (p : Pattern) : Int := if p 204 then d3777 p else d119 p
theorem agree3838 (p q : Pattern) (h : Agree support p q) : d3838 p = d3838 q := by
  simp only [d3838, h 204 (by decide), agree3777 p q h, agree119 p q h]
theorem nonnegative3838 (p : Pattern) : 0 ≤ d3838 p :=
  nonnegative_ite (p 204) (nonnegative3777 p) (nonnegative119 p)
def d3839 (p : Pattern) : Int := if p 182 then d3778 p else d3838 p
theorem agree3839 (p q : Pattern) (h : Agree support p q) : d3839 p = d3839 q := by
  simp only [d3839, h 182 (by decide), agree3778 p q h, agree3838 p q h]
theorem nonnegative3839 (p : Pattern) : 0 ≤ d3839 p :=
  nonnegative_ite (p 182) (nonnegative3778 p) (nonnegative3838 p)
end NetHack.Sokoban22Refined85
