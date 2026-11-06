/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions99
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub12000 (p : Pattern) : d3755 (change p 247 none) = d6735 p := by
  change (if p 204 then d12 (change p 247 none) else d3754 (change p 247 none)) = d6735 p
  rw [sub11767, sub11999]
  rfl
theorem sub12001 (p : Pattern) : d3756 (change p 247 none) = d6736 p := by
  change (if p 182 then d3755 (change p 247 none) else d3751 (change p 247 none)) = d6736 p
  rw [sub12000, sub11994]
  rfl
theorem sub12002 (p : Pattern) : d3757 (change p 247 none) = d6737 p := by
  change (if p 163 then d3756 (change p 247 none) else d3746 (change p 247 none)) = d6737 p
  rw [sub12001, sub11989]
  rfl
theorem sub12003 (p : Pattern) : d3758 (change p 247 none) = d6738 p := by
  change (if p 162 then d3757 (change p 247 none) else d3747 (change p 247 none)) = d6738 p
  rw [sub12002, sub11990]
  rfl
theorem sub12004 (p : Pattern) : d3759 (change p 247 none) = d6739 p := by
  change (if p 163 then d12 (change p 247 none) else d3636 (change p 247 none)) = d6739 p
  rw [sub11767, sub11871]
  rfl
theorem sub12005 (p : Pattern) : d3760 (change p 247 none) = d6740 p := by
  change (if p 162 then d3759 (change p 247 none) else d3757 (change p 247 none)) = d6740 p
  rw [sub12004, sub12002]
  rfl
theorem sub12006 (p : Pattern) : d3761 (change p 247 none) = d6741 p := by
  change (if p 161 then d3760 (change p 247 none) else d3758 (change p 247 none)) = d6741 p
  rw [sub12005, sub12003]
  rfl
theorem sub12007 (p : Pattern) : d3762 (change p 247 none) = d6742 p := by
  change (if p 246 then d119 (change p 247 none) else d102 (change p 247 none)) = d6742 p
  rw [sub11996, sub11971]
  rfl
theorem sub12008 (p : Pattern) : d3763 (change p 247 none) = d6743 p := by
  change (if p 225 then d3762 (change p 247 none) else d102 (change p 247 none)) = d6743 p
  rw [sub12007, sub11971]
  rfl
theorem sub12009 (p : Pattern) : d1955 (change p 247 none) = d6744 p := by
  change (if p 246 then d57 (change p 247 none) else d102 (change p 247 none)) = d6744 p
  rw [sub11821, sub11971]
  rfl
theorem sub12010 (p : Pattern) : d3764 (change p 247 none) = d6745 p := by
  change (if p 225 then d1955 (change p 247 none) else d3736 (change p 247 none)) = d6745 p
  rw [sub12009, sub11977]
  rfl
theorem sub12011 (p : Pattern) : d3765 (change p 247 none) = d6746 p := by
  change (if p 224 then d3764 (change p 247 none) else d3763 (change p 247 none)) = d6746 p
  rw [sub12010, sub12008]
  rfl
theorem sub12012 (p : Pattern) : d3766 (change p 247 none) = d6747 p := by
  change (if p 204 then d3765 (change p 247 none) else d102 (change p 247 none)) = d6747 p
  rw [sub12011, sub11971]
  rfl
theorem sub12013 (p : Pattern) : d3767 (change p 247 none) = d6748 p := by
  change (if p 246 then d23 (change p 247 none) else d115 (change p 247 none)) = d6748 p
  rw [sub11789, sub11982]
  rfl
theorem sub12014 (p : Pattern) : d3768 (change p 247 none) = d6749 p := by
  change (if p 225 then d3767 (change p 247 none) else d115 (change p 247 none)) = d6749 p
  rw [sub12013, sub11982]
  rfl
theorem sub12015 (p : Pattern) : d3769 (change p 247 none) = d6750 p := by
  change (if p 246 then d119 (change p 247 none) else d115 (change p 247 none)) = d6750 p
  rw [sub11996, sub11982]
  rfl
theorem sub12016 (p : Pattern) : d1896 (change p 247 none) = d3374 p := by
  change (if p 246 then d12 (change p 247 none) else d115 (change p 247 none)) = d3374 p
  rw [sub11767, sub11982]
  rfl
theorem sub12017 (p : Pattern) : d3770 (change p 247 none) = d6751 p := by
  change (if p 225 then d1896 (change p 247 none) else d3769 (change p 247 none)) = d6751 p
  rw [sub12016, sub12015]
  rfl
theorem sub12018 (p : Pattern) : d3771 (change p 247 none) = d6752 p := by
  change (if p 224 then d3770 (change p 247 none) else d3768 (change p 247 none)) = d6752 p
  rw [sub12017, sub12014]
  rfl
theorem sub12019 (p : Pattern) : d3772 (change p 247 none) = d6753 p := by
  change (if p 204 then d12 (change p 247 none) else d3771 (change p 247 none)) = d6753 p
  rw [sub11767, sub12018]
  rfl
theorem sub12020 (p : Pattern) : d3773 (change p 247 none) = d6754 p := by
  change (if p 182 then d3772 (change p 247 none) else d3766 (change p 247 none)) = d6754 p
  rw [sub12019, sub12012]
  rfl
theorem sub12021 (p : Pattern) : d317 (change p 247 none) = d3377 p := by
  change (if p 246 then d12 (change p 247 none) else d119 (change p 247 none)) = d3377 p
  rw [sub11767, sub11996]
  rfl
theorem sub12022 (p : Pattern) : d3774 (change p 247 none) = d6755 p := by
  change (if p 225 then d317 (change p 247 none) else d119 (change p 247 none)) = d6755 p
  rw [sub12021, sub11996]
  rfl
theorem sub12023 (p : Pattern) : d3775 (change p 247 none) = d6756 p := by
  change (if p 246 then d39 (change p 247 none) else d119 (change p 247 none)) = d6756 p
  rw [sub11795, sub11996]
  rfl
theorem sub12024 (p : Pattern) : d3776 (change p 247 none) = d6757 p := by
  change (if p 225 then d317 (change p 247 none) else d3775 (change p 247 none)) = d6757 p
  rw [sub12021, sub12023]
  rfl
theorem sub12025 (p : Pattern) : d3777 (change p 247 none) = d6758 p := by
  change (if p 224 then d3776 (change p 247 none) else d3774 (change p 247 none)) = d6758 p
  rw [sub12024, sub12022]
  rfl
theorem sub12026 (p : Pattern) : d3778 (change p 247 none) = d6759 p := by
  change (if p 204 then d12 (change p 247 none) else d3777 (change p 247 none)) = d6759 p
  rw [sub11767, sub12025]
  rfl
theorem sub12027 (p : Pattern) : d3779 (change p 247 none) = d6760 p := by
  change (if p 182 then d3778 (change p 247 none) else d3766 (change p 247 none)) = d6760 p
  rw [sub12026, sub12012]
  rfl
theorem sub12028 (p : Pattern) : d3780 (change p 247 none) = d6761 p := by
  change (if p 163 then d3779 (change p 247 none) else d3773 (change p 247 none)) = d6761 p
  rw [sub12027, sub12020]
  rfl
theorem sub12029 (p : Pattern) : d3781 (change p 247 none) = d6762 p := by
  change (if p 182 then d12 (change p 247 none) else d3766 (change p 247 none)) = d6762 p
  rw [sub11767, sub12012]
  rfl
theorem sub12030 (p : Pattern) : d3782 (change p 247 none) = d6763 p := by
  change (if p 246 then d39 (change p 247 none) else d106 (change p 247 none)) = d6763 p
  rw [sub11795, sub11976]
  rfl
theorem sub12031 (p : Pattern) : d3783 (change p 247 none) = d6764 p := by
  change (if p 225 then d3782 (change p 247 none) else d106 (change p 247 none)) = d6764 p
  rw [sub12030, sub11976]
  rfl
theorem sub12032 (p : Pattern) : d348 (change p 247 none) = d3366 p := by
  change (if p 246 then d12 (change p 247 none) else d106 (change p 247 none)) = d3366 p
  rw [sub11767, sub11976]
  rfl
theorem sub12033 (p : Pattern) : d3784 (change p 247 none) = d6765 p := by
  change (if p 225 then d348 (change p 247 none) else d3748 (change p 247 none)) = d6765 p
  rw [sub12032, sub11991]
  rfl
theorem sub12034 (p : Pattern) : d3785 (change p 247 none) = d6766 p := by
  change (if p 224 then d3784 (change p 247 none) else d3783 (change p 247 none)) = d6766 p
  rw [sub12033, sub12031]
  rfl
theorem sub12035 (p : Pattern) : d3786 (change p 247 none) = d6767 p := by
  change (if p 204 then d3785 (change p 247 none) else d106 (change p 247 none)) = d6767 p
  rw [sub12034, sub11976]
  rfl
theorem sub12036 (p : Pattern) : d3787 (change p 247 none) = d6768 p := by
  change (if p 182 then d12 (change p 247 none) else d3786 (change p 247 none)) = d6768 p
  rw [sub11767, sub12035]
  rfl
theorem sub12037 (p : Pattern) : d3788 (change p 247 none) = d6769 p := by
  change (if p 163 then d3787 (change p 247 none) else d3781 (change p 247 none)) = d6769 p
  rw [sub12036, sub12029]
  rfl
theorem sub12038 (p : Pattern) : d3789 (change p 247 none) = d6770 p := by
  change (if p 162 then d3788 (change p 247 none) else d3780 (change p 247 none)) = d6770 p
  rw [sub12037, sub12028]
  rfl
theorem sub12039 (p : Pattern) : d3790 (change p 247 none) = d6771 p := by
  change (if p 163 then d12 (change p 247 none) else d3648 (change p 247 none)) = d6771 p
  rw [sub11767, sub11883]
  rfl
theorem sub12040 (p : Pattern) : d3791 (change p 247 none) = d6772 p := by
  change (if p 162 then d3790 (change p 247 none) else d3788 (change p 247 none)) = d6772 p
  rw [sub12039, sub12037]
  rfl
theorem sub12041 (p : Pattern) : d3792 (change p 247 none) = d6773 p := by
  change (if p 161 then d3791 (change p 247 none) else d3789 (change p 247 none)) = d6773 p
  rw [sub12040, sub12038]
  rfl
theorem sub12042 (p : Pattern) : d3793 (change p 247 none) = d6774 p := by
  change (if p 160 then d3792 (change p 247 none) else d3761 (change p 247 none)) = d6774 p
  rw [sub12041, sub12006]
  rfl
theorem sub12043 (p : Pattern) : d3794 (change p 247 none) = d6775 p := by
  change (if p 225 then d3769 (change p 247 none) else d115 (change p 247 none)) = d6775 p
  rw [sub12015, sub11982]
  rfl
theorem sub12044 (p : Pattern) : d3795 (change p 247 none) = d6776 p := by
  change (if p 224 then d3769 (change p 247 none) else d3794 (change p 247 none)) = d6776 p
  rw [sub12015, sub12043]
  rfl
theorem sub12045 (p : Pattern) : d3796 (change p 247 none) = d6777 p := by
  change (if p 204 then d3795 (change p 247 none) else d115 (change p 247 none)) = d6777 p
  rw [sub12044, sub11982]
  rfl
theorem sub12046 (p : Pattern) : d3797 (change p 247 none) = d6778 p := by
  change (if p 246 then d106 (change p 247 none) else d115 (change p 247 none)) = d6778 p
  rw [sub11976, sub11982]
  rfl
theorem sub12047 (p : Pattern) : d3798 (change p 247 none) = d6779 p := by
  change (if p 225 then d3797 (change p 247 none) else d115 (change p 247 none)) = d6779 p
  rw [sub12046, sub11982]
  rfl
theorem sub12048 (p : Pattern) : d3799 (change p 247 none) = d6780 p := by
  change (if p 224 then d3797 (change p 247 none) else d3798 (change p 247 none)) = d6780 p
  rw [sub12046, sub12047]
  rfl
theorem sub12049 (p : Pattern) : d3800 (change p 247 none) = d6781 p := by
  change (if p 204 then d12 (change p 247 none) else d3799 (change p 247 none)) = d6781 p
  rw [sub11767, sub12048]
  rfl
theorem sub12050 (p : Pattern) : d3801 (change p 247 none) = d6782 p := by
  change (if p 182 then d3800 (change p 247 none) else d3796 (change p 247 none)) = d6782 p
  rw [sub12049, sub12045]
  rfl
theorem sub12051 (p : Pattern) : d3802 (change p 247 none) = d6783 p := by
  change (if p 163 then d3801 (change p 247 none) else d3746 (change p 247 none)) = d6783 p
  rw [sub12050, sub11989]
  rfl
theorem sub12052 (p : Pattern) : d3803 (change p 247 none) = d6784 p := by
  change (if p 163 then d3636 (change p 247 none) else d3756 (change p 247 none)) = d6784 p
  rw [sub11871, sub12001]
  rfl
theorem sub12053 (p : Pattern) : d3804 (change p 247 none) = d6785 p := by
  change (if p 162 then d3803 (change p 247 none) else d3802 (change p 247 none)) = d6785 p
  rw [sub12052, sub12051]
  rfl
theorem sub12054 (p : Pattern) : d3805 (change p 247 none) = d6786 p := by
  change (if p 163 then d3639 (change p 247 none) else d3756 (change p 247 none)) = d6786 p
  rw [sub11874, sub12001]
  rfl
theorem sub12055 (p : Pattern) : d3806 (change p 247 none) = d6787 p := by
  change (if p 162 then d12 (change p 247 none) else d3805 (change p 247 none)) = d6787 p
  rw [sub11767, sub12054]
  rfl
theorem sub12056 (p : Pattern) : d3807 (change p 247 none) = d6788 p := by
  change (if p 161 then d3806 (change p 247 none) else d3804 (change p 247 none)) = d6788 p
  rw [sub12055, sub12053]
  rfl
theorem sub12057 (p : Pattern) : d3808 (change p 247 none) = d6789 p := by
  change (if p 204 then d3771 (change p 247 none) else d115 (change p 247 none)) = d6789 p
  rw [sub12018, sub11982]
  rfl
theorem sub12058 (p : Pattern) : d3809 (change p 247 none) = d6790 p := by
  change (if p 182 then d12 (change p 247 none) else d3808 (change p 247 none)) = d6790 p
  rw [sub11767, sub12057]
  rfl
theorem sub12059 (p : Pattern) : d3810 (change p 247 none) = d6791 p := by
  change (if p 163 then d3809 (change p 247 none) else d3779 (change p 247 none)) = d6791 p
  rw [sub12058, sub12027]
  rfl
theorem sub12060 (p : Pattern) : d3811 (change p 247 none) = d6792 p := by
  change (if p 163 then d3648 (change p 247 none) else d3787 (change p 247 none)) = d6792 p
  rw [sub11883, sub12036]
  rfl
theorem sub12061 (p : Pattern) : d3812 (change p 247 none) = d6793 p := by
  change (if p 162 then d3811 (change p 247 none) else d3810 (change p 247 none)) = d6793 p
  rw [sub12060, sub12059]
  rfl
theorem sub12062 (p : Pattern) : d3813 (change p 247 none) = d6794 p := by
  change (if p 163 then d3650 (change p 247 none) else d3787 (change p 247 none)) = d6794 p
  rw [sub11885, sub12036]
  rfl
theorem sub12063 (p : Pattern) : d3814 (change p 247 none) = d6795 p := by
  change (if p 162 then d12 (change p 247 none) else d3813 (change p 247 none)) = d6795 p
  rw [sub11767, sub12062]
  rfl
theorem sub12064 (p : Pattern) : d3815 (change p 247 none) = d6796 p := by
  change (if p 161 then d3814 (change p 247 none) else d3812 (change p 247 none)) = d6796 p
  rw [sub12063, sub12061]
  rfl
theorem sub12065 (p : Pattern) : d3816 (change p 247 none) = d6797 p := by
  change (if p 160 then d3815 (change p 247 none) else d3807 (change p 247 none)) = d6797 p
  rw [sub12064, sub12056]
  rfl
theorem sub12066 (p : Pattern) : d3817 (change p 247 none) = d6798 p := by
  change (if p 141 then d3816 (change p 247 none) else d3793 (change p 247 none)) = d6798 p
  rw [sub12065, sub12042]
  rfl
theorem sub12067 (p : Pattern) : d3818 (change p 247 none) = d6799 p := by
  change (if p 225 then d3762 (change p 247 none) else d3736 (change p 247 none)) = d6799 p
  rw [sub12007, sub11977]
  rfl
theorem sub12068 (p : Pattern) : d3819 (change p 247 none) = d6800 p := by
  change (if p 224 then d3818 (change p 247 none) else d3763 (change p 247 none)) = d6800 p
  rw [sub12067, sub12008]
  rfl
theorem sub12069 (p : Pattern) : d3820 (change p 247 none) = d6801 p := by
  change (if p 204 then d3819 (change p 247 none) else d102 (change p 247 none)) = d6801 p
  rw [sub12068, sub11971]
  rfl
theorem sub12070 (p : Pattern) : d3821 (change p 247 none) = d6802 p := by
  change (if p 204 then d12 (change p 247 none) else d3738 (change p 247 none)) = d6802 p
  rw [sub11767, sub11979]
  rfl
theorem sub12071 (p : Pattern) : d3822 (change p 247 none) = d6803 p := by
  change (if p 182 then d3821 (change p 247 none) else d3820 (change p 247 none)) = d6803 p
  rw [sub12070, sub12069]
  rfl
theorem sub12072 (p : Pattern) : d3823 (change p 247 none) = d6804 p := by
  change (if p 246 then d23 (change p 247 none) else d102 (change p 247 none)) = d6804 p
  rw [sub11789, sub11971]
  rfl
theorem sub12073 (p : Pattern) : d3824 (change p 247 none) = d6805 p := by
  change (if p 225 then d3823 (change p 247 none) else d3736 (change p 247 none)) = d6805 p
  rw [sub12072, sub11977]
  rfl
theorem sub12074 (p : Pattern) : d3825 (change p 247 none) = d6806 p := by
  change (if p 224 then d3824 (change p 247 none) else d3763 (change p 247 none)) = d6806 p
  rw [sub12073, sub12008]
  rfl
theorem sub12075 (p : Pattern) : d3826 (change p 247 none) = d6807 p := by
  change (if p 204 then d12 (change p 247 none) else d3825 (change p 247 none)) = d6807 p
  rw [sub11767, sub12074]
  rfl
theorem sub12076 (p : Pattern) : d3827 (change p 247 none) = d6808 p := by
  change (if p 182 then d3826 (change p 247 none) else d3766 (change p 247 none)) = d6808 p
  rw [sub12075, sub12012]
  rfl
theorem sub12077 (p : Pattern) : d3828 (change p 247 none) = d6809 p := by
  change (if p 163 then d3827 (change p 247 none) else d3822 (change p 247 none)) = d6809 p
  rw [sub12076, sub12071]
  rfl
theorem sub12078 (p : Pattern) : d3829 (change p 247 none) = d6810 p := by
  change (if p 204 then d12 (change p 247 none) else d3765 (change p 247 none)) = d6810 p
  rw [sub11767, sub12011]
  rfl
theorem sub12079 (p : Pattern) : d3830 (change p 247 none) = d6811 p := by
  change (if p 182 then d3829 (change p 247 none) else d3766 (change p 247 none)) = d6811 p
  rw [sub12078, sub12012]
  rfl
theorem sub12080 (p : Pattern) : d3831 (change p 247 none) = d6812 p := by
  change (if p 204 then d12 (change p 247 none) else d3785 (change p 247 none)) = d6812 p
  rw [sub11767, sub12034]
  rfl
theorem sub12081 (p : Pattern) : d3832 (change p 247 none) = d6813 p := by
  change (if p 182 then d3831 (change p 247 none) else d3786 (change p 247 none)) = d6813 p
  rw [sub12080, sub12035]
  rfl
theorem sub12082 (p : Pattern) : d3833 (change p 247 none) = d6814 p := by
  change (if p 163 then d3832 (change p 247 none) else d3830 (change p 247 none)) = d6814 p
  rw [sub12081, sub12079]
  rfl
theorem sub12083 (p : Pattern) : d3834 (change p 247 none) = d6815 p := by
  change (if p 162 then d3833 (change p 247 none) else d3828 (change p 247 none)) = d6815 p
  rw [sub12082, sub12077]
  rfl
theorem sub12084 (p : Pattern) : d3835 (change p 247 none) = d6816 p := by
  change (if p 162 then d3759 (change p 247 none) else d3833 (change p 247 none)) = d6816 p
  rw [sub12004, sub12082]
  rfl
theorem sub12085 (p : Pattern) : d3836 (change p 247 none) = d6817 p := by
  change (if p 161 then d3835 (change p 247 none) else d3834 (change p 247 none)) = d6817 p
  rw [sub12084, sub12083]
  rfl
theorem sub12086 (p : Pattern) : d3837 (change p 247 none) = d6818 p := by
  change (if p 182 then d3772 (change p 247 none) else d3808 (change p 247 none)) = d6818 p
  rw [sub12019, sub12057]
  rfl
theorem sub12087 (p : Pattern) : d3838 (change p 247 none) = d6819 p := by
  change (if p 204 then d3777 (change p 247 none) else d119 (change p 247 none)) = d6819 p
  rw [sub12025, sub11996]
  rfl
theorem sub12088 (p : Pattern) : d3839 (change p 247 none) = d6820 p := by
  change (if p 182 then d3778 (change p 247 none) else d3838 (change p 247 none)) = d6820 p
  rw [sub12026, sub12087]
  rfl
theorem sub12089 (p : Pattern) : d3840 (change p 247 none) = d6821 p := by
  change (if p 163 then d3839 (change p 247 none) else d3837 (change p 247 none)) = d6821 p
  rw [sub12088, sub12086]
  rfl
theorem sub12090 (p : Pattern) : d3841 (change p 247 none) = d6822 p := by
  change (if p 162 then d12 (change p 247 none) else d3840 (change p 247 none)) = d6822 p
  rw [sub11767, sub12089]
  rfl
theorem sub12091 (p : Pattern) : d3842 (change p 247 none) = d6823 p := by
  change (if p 161 then d12 (change p 247 none) else d3841 (change p 247 none)) = d6823 p
  rw [sub11767, sub12090]
  rfl
theorem sub12092 (p : Pattern) : d3843 (change p 247 none) = d6824 p := by
  change (if p 160 then d3842 (change p 247 none) else d3836 (change p 247 none)) = d6824 p
  rw [sub12091, sub12085]
  rfl
theorem sub12093 (p : Pattern) : d3844 (change p 247 none) = d6825 p := by
  change (if p 163 then d3837 (change p 247 none) else d3827 (change p 247 none)) = d6825 p
  rw [sub12086, sub12076]
  rfl
theorem sub12094 (p : Pattern) : d3845 (change p 247 none) = d6826 p := by
  change (if p 163 then d3636 (change p 247 none) else d3832 (change p 247 none)) = d6826 p
  rw [sub11871, sub12081]
  rfl
theorem sub12095 (p : Pattern) : d3846 (change p 247 none) = d6827 p := by
  change (if p 162 then d3845 (change p 247 none) else d3844 (change p 247 none)) = d6827 p
  rw [sub12094, sub12093]
  rfl
theorem sub12096 (p : Pattern) : d3847 (change p 247 none) = d6828 p := by
  change (if p 163 then d3639 (change p 247 none) else d3832 (change p 247 none)) = d6828 p
  rw [sub11874, sub12081]
  rfl
theorem sub12097 (p : Pattern) : d3848 (change p 247 none) = d6829 p := by
  change (if p 162 then d12 (change p 247 none) else d3847 (change p 247 none)) = d6829 p
  rw [sub11767, sub12096]
  rfl
theorem sub12098 (p : Pattern) : d3849 (change p 247 none) = d6830 p := by
  change (if p 161 then d3848 (change p 247 none) else d3846 (change p 247 none)) = d6830 p
  rw [sub12097, sub12095]
  rfl
theorem sub12099 (p : Pattern) : d3850 (change p 247 none) = d6831 p := by
  change (if p 163 then d12 (change p 247 none) else d3839 (change p 247 none)) = d6831 p
  rw [sub11767, sub12088]
  rfl
theorem sub12100 (p : Pattern) : d3851 (change p 247 none) = d6832 p := by
  change (if p 162 then d12 (change p 247 none) else d3850 (change p 247 none)) = d6832 p
  rw [sub11767, sub12099]
  rfl
theorem sub12101 (p : Pattern) : d3852 (change p 247 none) = d6833 p := by
  change (if p 161 then d12 (change p 247 none) else d3851 (change p 247 none)) = d6833 p
  rw [sub11767, sub12100]
  rfl
theorem sub12102 (p : Pattern) : d3853 (change p 247 none) = d6834 p := by
  change (if p 160 then d3852 (change p 247 none) else d3849 (change p 247 none)) = d6834 p
  rw [sub12101, sub12098]
  rfl
theorem sub12103 (p : Pattern) : d3854 (change p 247 none) = d6835 p := by
  change (if p 141 then d3853 (change p 247 none) else d3843 (change p 247 none)) = d6835 p
  rw [sub12102, sub12092]
  rfl
theorem sub12104 (p : Pattern) : d3855 (change p 247 none) = d6836 p := by
  change (if p 138 then d3854 (change p 247 none) else d3817 (change p 247 none)) = d6836 p
  rw [sub12103, sub12066]
  rfl
theorem sub12105 (p : Pattern) : d3856 (change p 247 none) = d6837 p := by
  change (if p 162 then d12 (change p 247 none) else d3759 (change p 247 none)) = d6837 p
  rw [sub11767, sub12004]
  rfl
theorem sub12106 (p : Pattern) : d3857 (change p 247 none) = d6838 p := by
  change (if p 161 then d12 (change p 247 none) else d3856 (change p 247 none)) = d6838 p
  rw [sub11767, sub12105]
  rfl
theorem sub12107 (p : Pattern) : d3858 (change p 247 none) = d6839 p := by
  change (if p 160 then d12 (change p 247 none) else d3857 (change p 247 none)) = d6839 p
  rw [sub11767, sub12106]
  rfl
theorem sub12108 (p : Pattern) : d3859 (change p 247 none) = d6840 p := by
  change (if p 141 then d12 (change p 247 none) else d3858 (change p 247 none)) = d6840 p
  rw [sub11767, sub12107]
  rfl
theorem sub12109 (p : Pattern) : d3860 (change p 247 none) = d6841 p := by
  change (if p 138 then d3859 (change p 247 none) else d3854 (change p 247 none)) = d6841 p
  rw [sub12108, sub12103]
  rfl
theorem sub12110 (p : Pattern) : d3861 (change p 247 none) = d6842 p := by
  change (if p 116 then d3860 (change p 247 none) else d3855 (change p 247 none)) = d6842 p
  rw [sub12109, sub12104]
  rfl
theorem sub12111 (p : Pattern) : d3862 (change p 247 none) = d6738 p := by
  change (if p 162 then d3757 (change p 247 none) else d3746 (change p 247 none)) = d6738 p
  rw [sub12002, sub11989]
  rfl
theorem sub12112 (p : Pattern) : d3863 (change p 247 none) = d6741 p := by
  change (if p 161 then d3760 (change p 247 none) else d3862 (change p 247 none)) = d6741 p
  rw [sub12005, sub12111]
  rfl
theorem sub12113 (p : Pattern) : d3864 (change p 247 none) = d6774 p := by
  change (if p 160 then d3792 (change p 247 none) else d3863 (change p 247 none)) = d6774 p
  rw [sub12041, sub12112]
  rfl
theorem sub12114 (p : Pattern) : d3865 (change p 247 none) = d6798 p := by
  change (if p 141 then d3816 (change p 247 none) else d3864 (change p 247 none)) = d6798 p
  rw [sub12065, sub12113]
  rfl
theorem sub12115 (p : Pattern) : d3866 (change p 247 none) = d6836 p := by
  change (if p 138 then d3854 (change p 247 none) else d3865 (change p 247 none)) = d6836 p
  rw [sub12103, sub12114]
  rfl
theorem sub12116 (p : Pattern) : d3867 (change p 247 none) = d6843 p := by
  change (if p 138 then d12 (change p 247 none) else d3854 (change p 247 none)) = d6843 p
  rw [sub11767, sub12103]
  rfl
theorem sub12117 (p : Pattern) : d3868 (change p 247 none) = d6844 p := by
  change (if p 116 then d3867 (change p 247 none) else d3866 (change p 247 none)) = d6844 p
  rw [sub12116, sub12115]
  rfl
theorem sub12118 (p : Pattern) : d3869 (change p 247 none) = d6845 p := by
  change (if p 115 then d3868 (change p 247 none) else d3861 (change p 247 none)) = d6845 p
  rw [sub12117, sub12110]
  rfl
theorem sub12119 (p : Pattern) : d3870 (change p 247 none) = d6846 p := by
  change (if p 71 then d3869 (change p 247 none) else d3718 (change p 247 none)) = d6846 p
  rw [sub12118, sub11953]
  rfl
end NetHack.Sokoban22Refined85
