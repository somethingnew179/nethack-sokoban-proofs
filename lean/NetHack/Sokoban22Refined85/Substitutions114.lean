/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions113
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub13680 (p : Pattern) : d6 (change p 10000 (some 247)) = d6 p := by
  rfl
theorem sub13681 (p : Pattern) : d1693 (change p 10000 (some 247)) = d6 p := by
  change d6 (change p 10000 (some 247)) = d6 p
  exact sub13680 p
theorem sub13682 (p : Pattern) : d34 (change p 10000 (some 247)) = d12 p := by
  change d12 (change p 10000 (some 247)) = d12 p
  exact sub13654 p
theorem sub13683 (p : Pattern) : d1694 (change p 10000 (some 247)) = d3253 p := by
  change (if p 246 then d34 (change p 10000 (some 247)) else d1693 (change p 10000 (some 247))) = d3253 p
  rw [sub13682, sub13681]
  rfl
theorem sub13684 (p : Pattern) : d1695 (change p 10000 (some 247)) = d7672 p := by
  change (if p 225 then d1694 (change p 10000 (some 247)) else d18 (change p 10000 (some 247))) = d7672 p
  rw [sub13683, sub13672]
  rfl
theorem sub13685 (p : Pattern) : d1696 (change p 10000 (some 247)) = d7673 p := by
  change (if p 224 then d1694 (change p 10000 (some 247)) else d1695 (change p 10000 (some 247))) = d7673 p
  rw [sub13683, sub13684]
  rfl
theorem sub13686 (p : Pattern) : d1697 (change p 10000 (some 247)) = d7674 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1696 (change p 10000 (some 247))) = d7674 p
  rw [sub13654, sub13685]
  rfl
theorem sub13687 (p : Pattern) : d2898 (change p 10000 (some 247)) = d7675 p := by
  change (if p 182 then d1697 (change p 10000 (some 247)) else d2897 (change p 10000 (some 247))) = d7675 p
  rw [sub13686, sub13679]
  rfl
theorem sub13688 (p : Pattern) : d2899 (change p 10000 (some 247)) = d7676 p := by
  change (if p 163 then d2898 (change p 10000 (some 247)) else d2896 (change p 10000 (some 247))) = d7676 p
  rw [sub13687, sub13671]
  rfl
theorem sub13689 (p : Pattern) : d2900 (change p 10000 (some 247)) = d7677 p := by
  change (if p 162 then d2899 (change p 10000 (some 247)) else d2896 (change p 10000 (some 247))) = d7677 p
  rw [sub13688, sub13671]
  rfl
theorem sub13690 (p : Pattern) : d9 (change p 10000 (some 247)) = d9 p := by
  rfl
theorem sub13691 (p : Pattern) : d23 (change p 10000 (some 247)) = d12 p := by
  change d12 (change p 10000 (some 247)) = d12 p
  exact sub13654 p
theorem sub13692 (p : Pattern) : d24 (change p 10000 (some 247)) = d3244 p := by
  change (if p 246 then d23 (change p 10000 (some 247)) else d9 (change p 10000 (some 247))) = d3244 p
  rw [sub13691, sub13690]
  rfl
theorem sub13693 (p : Pattern) : d356 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d12 (change p 10000 (some 247)) else d23 (change p 10000 (some 247))) = d12 p
  rw [sub13654, sub13691]
  simp only [ite_self]
theorem sub13694 (p : Pattern) : d1802 (change p 10000 (some 247)) = d7678 p := by
  change (if p 225 then d356 (change p 10000 (some 247)) else d24 (change p 10000 (some 247))) = d7678 p
  rw [sub13693, sub13692]
  rfl
theorem sub13695 (p : Pattern) : d1803 (change p 10000 (some 247)) = d7679 p := by
  change (if p 224 then d356 (change p 10000 (some 247)) else d1802 (change p 10000 (some 247))) = d7679 p
  rw [sub13693, sub13694]
  rfl
theorem sub13696 (p : Pattern) : d2901 (change p 10000 (some 247)) = d7680 p := by
  change (if p 204 then d1803 (change p 10000 (some 247)) else d24 (change p 10000 (some 247))) = d7680 p
  rw [sub13695, sub13692]
  rfl
theorem sub13697 (p : Pattern) : d11 (change p 10000 (some 247)) = d11 p := by
  rfl
theorem sub13698 (p : Pattern) : d1701 (change p 10000 (some 247)) = d11 p := by
  change d11 (change p 10000 (some 247)) = d11 p
  exact sub13697 p
theorem sub13699 (p : Pattern) : d39 (change p 10000 (some 247)) = d12 p := by
  change d12 (change p 10000 (some 247)) = d12 p
  exact sub13654 p
theorem sub13700 (p : Pattern) : d1702 (change p 10000 (some 247)) = d3257 p := by
  change (if p 246 then d39 (change p 10000 (some 247)) else d1701 (change p 10000 (some 247))) = d3257 p
  rw [sub13699, sub13698]
  rfl
theorem sub13701 (p : Pattern) : d1703 (change p 10000 (some 247)) = d7681 p := by
  change (if p 225 then d1702 (change p 10000 (some 247)) else d24 (change p 10000 (some 247))) = d7681 p
  rw [sub13700, sub13692]
  rfl
theorem sub13702 (p : Pattern) : d1704 (change p 10000 (some 247)) = d7682 p := by
  change (if p 224 then d1702 (change p 10000 (some 247)) else d1703 (change p 10000 (some 247))) = d7682 p
  rw [sub13700, sub13701]
  rfl
theorem sub13703 (p : Pattern) : d1705 (change p 10000 (some 247)) = d7683 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1704 (change p 10000 (some 247))) = d7683 p
  rw [sub13654, sub13702]
  rfl
theorem sub13704 (p : Pattern) : d2902 (change p 10000 (some 247)) = d7684 p := by
  change (if p 182 then d1705 (change p 10000 (some 247)) else d2901 (change p 10000 (some 247))) = d7684 p
  rw [sub13703, sub13696]
  rfl
theorem sub13705 (p : Pattern) : d2903 (change p 10000 (some 247)) = d7685 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d2902 (change p 10000 (some 247))) = d7685 p
  rw [sub13654, sub13704]
  rfl
theorem sub13706 (p : Pattern) : d2904 (change p 10000 (some 247)) = d7686 p := by
  change (if p 162 then d2903 (change p 10000 (some 247)) else d2899 (change p 10000 (some 247))) = d7686 p
  rw [sub13705, sub13688]
  rfl
theorem sub13707 (p : Pattern) : d2905 (change p 10000 (some 247)) = d7687 p := by
  change (if p 161 then d2904 (change p 10000 (some 247)) else d2900 (change p 10000 (some 247))) = d7687 p
  rw [sub13706, sub13689]
  rfl
theorem sub13708 (p : Pattern) : d1775 (change p 10000 (some 247)) = d6 p := by
  change d6 (change p 10000 (some 247)) = d6 p
  exact sub13680 p
theorem sub13709 (p : Pattern) : d1776 (change p 10000 (some 247)) = d3253 p := by
  change (if p 246 then d34 (change p 10000 (some 247)) else d1775 (change p 10000 (some 247))) = d3253 p
  rw [sub13682, sub13708]
  rfl
theorem sub13710 (p : Pattern) : d1777 (change p 10000 (some 247)) = d7688 p := by
  change (if p 225 then d1776 (change p 10000 (some 247)) else d14 (change p 10000 (some 247))) = d7688 p
  rw [sub13709, sub13656]
  rfl
theorem sub13711 (p : Pattern) : d1785 (change p 10000 (some 247)) = d11 p := by
  change d11 (change p 10000 (some 247)) = d11 p
  exact sub13697 p
theorem sub13712 (p : Pattern) : d1786 (change p 10000 (some 247)) = d3257 p := by
  change (if p 246 then d23 (change p 10000 (some 247)) else d1785 (change p 10000 (some 247))) = d3257 p
  rw [sub13691, sub13711]
  rfl
theorem sub13713 (p : Pattern) : d1787 (change p 10000 (some 247)) = d7689 p := by
  change (if p 225 then d1786 (change p 10000 (some 247)) else d1770 (change p 10000 (some 247))) = d7689 p
  rw [sub13712, sub13660]
  rfl
theorem sub13714 (p : Pattern) : d1788 (change p 10000 (some 247)) = d7690 p := by
  change (if p 224 then d1787 (change p 10000 (some 247)) else d1777 (change p 10000 (some 247))) = d7690 p
  rw [sub13713, sub13710]
  rfl
theorem sub13715 (p : Pattern) : d2906 (change p 10000 (some 247)) = d7691 p := by
  change (if p 204 then d1788 (change p 10000 (some 247)) else d14 (change p 10000 (some 247))) = d7691 p
  rw [sub13714, sub13656]
  rfl
theorem sub13716 (p : Pattern) : d31 (change p 10000 (some 247)) = d3250 p := by
  change (if p 246 then d30 (change p 10000 (some 247)) else d2 (change p 10000 (some 247))) = d3250 p
  rw [sub13666, sub13664]
  rfl
theorem sub13717 (p : Pattern) : d1710 (change p 10000 (some 247)) = d8 p := by
  change d8 (change p 10000 (some 247)) = d8 p
  exact sub13673 p
theorem sub13718 (p : Pattern) : d1711 (change p 10000 (some 247)) = d3461 p := by
  change (if p 246 then d190 (change p 10000 (some 247)) else d1710 (change p 10000 (some 247))) = d3461 p
  rw [sub13675, sub13717]
  rfl
theorem sub13719 (p : Pattern) : d1712 (change p 10000 (some 247)) = d7692 p := by
  change (if p 225 then d1711 (change p 10000 (some 247)) else d31 (change p 10000 (some 247))) = d7692 p
  rw [sub13718, sub13716]
  rfl
theorem sub13720 (p : Pattern) : d1713 (change p 10000 (some 247)) = d6 p := by
  change d6 (change p 10000 (some 247)) = d6 p
  exact sub13680 p
theorem sub13721 (p : Pattern) : d1714 (change p 10000 (some 247)) = d3253 p := by
  change (if p 246 then d34 (change p 10000 (some 247)) else d1713 (change p 10000 (some 247))) = d3253 p
  rw [sub13682, sub13720]
  rfl
theorem sub13722 (p : Pattern) : d1715 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d39 (change p 10000 (some 247)) else d30 (change p 10000 (some 247))) = d12 p
  rw [sub13699, sub13666]
  simp only [ite_self]
theorem sub13723 (p : Pattern) : d1716 (change p 10000 (some 247)) = d7693 p := by
  change (if p 225 then d1715 (change p 10000 (some 247)) else d1714 (change p 10000 (some 247))) = d7693 p
  rw [sub13722, sub13721]
  rfl
theorem sub13724 (p : Pattern) : d1717 (change p 10000 (some 247)) = d7694 p := by
  change (if p 224 then d1716 (change p 10000 (some 247)) else d1712 (change p 10000 (some 247))) = d7694 p
  rw [sub13723, sub13719]
  rfl
theorem sub13725 (p : Pattern) : d1718 (change p 10000 (some 247)) = d7695 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1717 (change p 10000 (some 247))) = d7695 p
  rw [sub13654, sub13724]
  rfl
theorem sub13726 (p : Pattern) : d2907 (change p 10000 (some 247)) = d7696 p := by
  change (if p 182 then d1718 (change p 10000 (some 247)) else d2906 (change p 10000 (some 247))) = d7696 p
  rw [sub13725, sub13715]
  rfl
theorem sub13727 (p : Pattern) : d35 (change p 10000 (some 247)) = d3253 p := by
  change (if p 246 then d34 (change p 10000 (some 247)) else d6 (change p 10000 (some 247))) = d3253 p
  rw [sub13682, sub13680]
  rfl
theorem sub13728 (p : Pattern) : d364 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d12 (change p 10000 (some 247)) else d34 (change p 10000 (some 247))) = d12 p
  rw [sub13654, sub13682]
  simp only [ite_self]
theorem sub13729 (p : Pattern) : d1720 (change p 10000 (some 247)) = d7693 p := by
  change (if p 225 then d364 (change p 10000 (some 247)) else d35 (change p 10000 (some 247))) = d7693 p
  rw [sub13728, sub13727]
  rfl
theorem sub13730 (p : Pattern) : d10 (change p 10000 (some 247)) = d10 p := by
  rfl
theorem sub13731 (p : Pattern) : d1721 (change p 10000 (some 247)) = d10 p := by
  change d10 (change p 10000 (some 247)) = d10 p
  exact sub13730 p
theorem sub13732 (p : Pattern) : d57 (change p 10000 (some 247)) = d12 p := by
  change d12 (change p 10000 (some 247)) = d12 p
  exact sub13654 p
theorem sub13733 (p : Pattern) : d1722 (change p 10000 (some 247)) = d3279 p := by
  change (if p 246 then d57 (change p 10000 (some 247)) else d1721 (change p 10000 (some 247))) = d3279 p
  rw [sub13732, sub13731]
  rfl
theorem sub13734 (p : Pattern) : d1723 (change p 10000 (some 247)) = d7697 p := by
  change (if p 225 then d364 (change p 10000 (some 247)) else d1722 (change p 10000 (some 247))) = d7697 p
  rw [sub13728, sub13733]
  rfl
theorem sub13735 (p : Pattern) : d1724 (change p 10000 (some 247)) = d7698 p := by
  change (if p 224 then d1723 (change p 10000 (some 247)) else d1720 (change p 10000 (some 247))) = d7698 p
  rw [sub13734, sub13729]
  rfl
theorem sub13736 (p : Pattern) : d1725 (change p 10000 (some 247)) = d7699 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1724 (change p 10000 (some 247))) = d7699 p
  rw [sub13654, sub13735]
  rfl
theorem sub13737 (p : Pattern) : d2908 (change p 10000 (some 247)) = d7700 p := by
  change (if p 182 then d1725 (change p 10000 (some 247)) else d2906 (change p 10000 (some 247))) = d7700 p
  rw [sub13736, sub13715]
  rfl
theorem sub13738 (p : Pattern) : d2909 (change p 10000 (some 247)) = d7701 p := by
  change (if p 163 then d2908 (change p 10000 (some 247)) else d2907 (change p 10000 (some 247))) = d7701 p
  rw [sub13737, sub13726]
  rfl
theorem sub13739 (p : Pattern) : d40 (change p 10000 (some 247)) = d3257 p := by
  change (if p 246 then d39 (change p 10000 (some 247)) else d11 (change p 10000 (some 247))) = d3257 p
  rw [sub13699, sub13697]
  rfl
theorem sub13740 (p : Pattern) : d327 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d12 (change p 10000 (some 247)) else d39 (change p 10000 (some 247))) = d12 p
  rw [sub13654, sub13699]
  simp only [ite_self]
theorem sub13741 (p : Pattern) : d1728 (change p 10000 (some 247)) = d7702 p := by
  change (if p 225 then d327 (change p 10000 (some 247)) else d40 (change p 10000 (some 247))) = d7702 p
  rw [sub13740, sub13739]
  rfl
theorem sub13742 (p : Pattern) : d1729 (change p 10000 (some 247)) = d7703 p := by
  change (if p 224 then d327 (change p 10000 (some 247)) else d1728 (change p 10000 (some 247))) = d7703 p
  rw [sub13740, sub13741]
  rfl
theorem sub13743 (p : Pattern) : d1730 (change p 10000 (some 247)) = d7704 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1729 (change p 10000 (some 247))) = d7704 p
  rw [sub13654, sub13742]
  rfl
theorem sub13744 (p : Pattern) : d2910 (change p 10000 (some 247)) = d7705 p := by
  change (if p 182 then d1730 (change p 10000 (some 247)) else d2906 (change p 10000 (some 247))) = d7705 p
  rw [sub13743, sub13715]
  rfl
theorem sub13745 (p : Pattern) : d1791 (change p 10000 (some 247)) = d10 p := by
  change d10 (change p 10000 (some 247)) = d10 p
  exact sub13730 p
theorem sub13746 (p : Pattern) : d1792 (change p 10000 (some 247)) = d3279 p := by
  change (if p 246 then d57 (change p 10000 (some 247)) else d1791 (change p 10000 (some 247))) = d3279 p
  rw [sub13732, sub13745]
  rfl
theorem sub13747 (p : Pattern) : d1793 (change p 10000 (some 247)) = d7706 p := by
  change (if p 225 then d1792 (change p 10000 (some 247)) else d18 (change p 10000 (some 247))) = d7706 p
  rw [sub13746, sub13672]
  rfl
theorem sub13748 (p : Pattern) : d339 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d12 (change p 10000 (some 247)) else d17 (change p 10000 (some 247))) = d12 p
  rw [sub13654, sub13659]
  simp only [ite_self]
theorem sub13749 (p : Pattern) : d1796 (change p 10000 (some 247)) = d7707 p := by
  change (if p 225 then d339 (change p 10000 (some 247)) else d1795 (change p 10000 (some 247))) = d7707 p
  rw [sub13748, sub13676]
  rfl
theorem sub13750 (p : Pattern) : d1797 (change p 10000 (some 247)) = d7708 p := by
  change (if p 224 then d1796 (change p 10000 (some 247)) else d1793 (change p 10000 (some 247))) = d7708 p
  rw [sub13749, sub13747]
  rfl
theorem sub13751 (p : Pattern) : d2911 (change p 10000 (some 247)) = d7709 p := by
  change (if p 204 then d1797 (change p 10000 (some 247)) else d18 (change p 10000 (some 247))) = d7709 p
  rw [sub13750, sub13672]
  rfl
theorem sub13752 (p : Pattern) : d2912 (change p 10000 (some 247)) = d7710 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d2911 (change p 10000 (some 247))) = d7710 p
  rw [sub13654, sub13751]
  rfl
theorem sub13753 (p : Pattern) : d2913 (change p 10000 (some 247)) = d7711 p := by
  change (if p 163 then d2912 (change p 10000 (some 247)) else d2910 (change p 10000 (some 247))) = d7711 p
  rw [sub13752, sub13744]
  rfl
theorem sub13754 (p : Pattern) : d2914 (change p 10000 (some 247)) = d7712 p := by
  change (if p 162 then d2913 (change p 10000 (some 247)) else d2909 (change p 10000 (some 247))) = d7712 p
  rw [sub13753, sub13738]
  rfl
theorem sub13755 (p : Pattern) : d2915 (change p 10000 (some 247)) = d7713 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d2906 (change p 10000 (some 247))) = d7713 p
  rw [sub13654, sub13715]
  rfl
theorem sub13756 (p : Pattern) : d2916 (change p 10000 (some 247)) = d7714 p := by
  change (if p 163 then d2912 (change p 10000 (some 247)) else d2915 (change p 10000 (some 247))) = d7714 p
  rw [sub13752, sub13755]
  rfl
theorem sub13757 (p : Pattern) : d2917 (change p 10000 (some 247)) = d7715 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d2901 (change p 10000 (some 247))) = d7715 p
  rw [sub13654, sub13696]
  rfl
theorem sub13758 (p : Pattern) : d2918 (change p 10000 (some 247)) = d7716 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d2917 (change p 10000 (some 247))) = d7716 p
  rw [sub13654, sub13757]
  rfl
theorem sub13759 (p : Pattern) : d2919 (change p 10000 (some 247)) = d7717 p := by
  change (if p 162 then d2918 (change p 10000 (some 247)) else d2916 (change p 10000 (some 247))) = d7717 p
  rw [sub13758, sub13756]
  rfl
theorem sub13760 (p : Pattern) : d2920 (change p 10000 (some 247)) = d7718 p := by
  change (if p 161 then d2919 (change p 10000 (some 247)) else d2914 (change p 10000 (some 247))) = d7718 p
  rw [sub13759, sub13754]
  rfl
theorem sub13761 (p : Pattern) : d2921 (change p 10000 (some 247)) = d7719 p := by
  change (if p 160 then d2920 (change p 10000 (some 247)) else d2905 (change p 10000 (some 247))) = d7719 p
  rw [sub13760, sub13707]
  rfl
theorem sub13762 (p : Pattern) : d2029 (change p 10000 (some 247)) = d7720 p := by
  change (if p 225 then d1714 (change p 10000 (some 247)) else d31 (change p 10000 (some 247))) = d7720 p
  rw [sub13721, sub13716]
  rfl
theorem sub13763 (p : Pattern) : d2030 (change p 10000 (some 247)) = d7721 p := by
  change (if p 224 then d1714 (change p 10000 (some 247)) else d2029 (change p 10000 (some 247))) = d7721 p
  rw [sub13721, sub13762]
  rfl
theorem sub13764 (p : Pattern) : d2922 (change p 10000 (some 247)) = d7722 p := by
  change (if p 204 then d2030 (change p 10000 (some 247)) else d31 (change p 10000 (some 247))) = d7722 p
  rw [sub13763, sub13716]
  rfl
theorem sub13765 (p : Pattern) : d1742 (change p 10000 (some 247)) = d4 p := by
  change d4 (change p 10000 (some 247)) = d4 p
  exact sub13657 p
theorem sub13766 (p : Pattern) : d1743 (change p 10000 (some 247)) = d3239 p := by
  change (if p 246 then d17 (change p 10000 (some 247)) else d1742 (change p 10000 (some 247))) = d3239 p
  rw [sub13659, sub13765]
  rfl
theorem sub13767 (p : Pattern) : d1744 (change p 10000 (some 247)) = d7723 p := by
  change (if p 225 then d1743 (change p 10000 (some 247)) else d31 (change p 10000 (some 247))) = d7723 p
  rw [sub13766, sub13716]
  rfl
theorem sub13768 (p : Pattern) : d1745 (change p 10000 (some 247)) = d7724 p := by
  change (if p 224 then d1743 (change p 10000 (some 247)) else d1744 (change p 10000 (some 247))) = d7724 p
  rw [sub13766, sub13767]
  rfl
theorem sub13769 (p : Pattern) : d1746 (change p 10000 (some 247)) = d7725 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1745 (change p 10000 (some 247))) = d7725 p
  rw [sub13654, sub13768]
  rfl
theorem sub13770 (p : Pattern) : d2923 (change p 10000 (some 247)) = d7726 p := by
  change (if p 182 then d1746 (change p 10000 (some 247)) else d2922 (change p 10000 (some 247))) = d7726 p
  rw [sub13769, sub13764]
  rfl
theorem sub13771 (p : Pattern) : d2924 (change p 10000 (some 247)) = d7727 p := by
  change (if p 163 then d2923 (change p 10000 (some 247)) else d2896 (change p 10000 (some 247))) = d7727 p
  rw [sub13770, sub13671]
  rfl
theorem sub13772 (p : Pattern) : d2925 (change p 10000 (some 247)) = d7728 p := by
  change (if p 163 then d2902 (change p 10000 (some 247)) else d2898 (change p 10000 (some 247))) = d7728 p
  rw [sub13704, sub13687]
  rfl
theorem sub13773 (p : Pattern) : d2926 (change p 10000 (some 247)) = d7729 p := by
  change (if p 162 then d2925 (change p 10000 (some 247)) else d2924 (change p 10000 (some 247))) = d7729 p
  rw [sub13772, sub13771]
  rfl
theorem sub13774 (p : Pattern) : d58 (change p 10000 (some 247)) = d3279 p := by
  change (if p 246 then d57 (change p 10000 (some 247)) else d10 (change p 10000 (some 247))) = d3279 p
  rw [sub13732, sub13730]
  rfl
theorem sub13775 (p : Pattern) : d329 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d12 (change p 10000 (some 247)) else d57 (change p 10000 (some 247))) = d12 p
  rw [sub13654, sub13732]
  simp only [ite_self]
theorem sub13776 (p : Pattern) : d1751 (change p 10000 (some 247)) = d7697 p := by
  change (if p 225 then d329 (change p 10000 (some 247)) else d58 (change p 10000 (some 247))) = d7697 p
  rw [sub13775, sub13774]
  rfl
theorem sub13777 (p : Pattern) : d1752 (change p 10000 (some 247)) = d7730 p := by
  change (if p 224 then d329 (change p 10000 (some 247)) else d1751 (change p 10000 (some 247))) = d7730 p
  rw [sub13775, sub13776]
  rfl
theorem sub13778 (p : Pattern) : d2927 (change p 10000 (some 247)) = d7731 p := by
  change (if p 204 then d1752 (change p 10000 (some 247)) else d58 (change p 10000 (some 247))) = d7731 p
  rw [sub13777, sub13774]
  rfl
theorem sub13779 (p : Pattern) : d1753 (change p 10000 (some 247)) = d7732 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1752 (change p 10000 (some 247))) = d7732 p
  rw [sub13654, sub13777]
  rfl
theorem sub13780 (p : Pattern) : d2928 (change p 10000 (some 247)) = d7733 p := by
  change (if p 182 then d1753 (change p 10000 (some 247)) else d2927 (change p 10000 (some 247))) = d7733 p
  rw [sub13779, sub13778]
  rfl
theorem sub13781 (p : Pattern) : d2929 (change p 10000 (some 247)) = d7734 p := by
  change (if p 163 then d2928 (change p 10000 (some 247)) else d2898 (change p 10000 (some 247))) = d7734 p
  rw [sub13780, sub13687]
  rfl
theorem sub13782 (p : Pattern) : d2930 (change p 10000 (some 247)) = d7735 p := by
  change (if p 204 then d1729 (change p 10000 (some 247)) else d40 (change p 10000 (some 247))) = d7735 p
  rw [sub13742, sub13739]
  rfl
theorem sub13783 (p : Pattern) : d2931 (change p 10000 (some 247)) = d7736 p := by
  change (if p 182 then d1730 (change p 10000 (some 247)) else d2930 (change p 10000 (some 247))) = d7736 p
  rw [sub13743, sub13782]
  rfl
theorem sub13784 (p : Pattern) : d2932 (change p 10000 (some 247)) = d7737 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d2931 (change p 10000 (some 247))) = d7737 p
  rw [sub13654, sub13783]
  rfl
theorem sub13785 (p : Pattern) : d2933 (change p 10000 (some 247)) = d7738 p := by
  change (if p 162 then d2932 (change p 10000 (some 247)) else d2929 (change p 10000 (some 247))) = d7738 p
  rw [sub13784, sub13781]
  rfl
theorem sub13786 (p : Pattern) : d2934 (change p 10000 (some 247)) = d7739 p := by
  change (if p 161 then d2933 (change p 10000 (some 247)) else d2926 (change p 10000 (some 247))) = d7739 p
  rw [sub13785, sub13773]
  rfl
theorem sub13787 (p : Pattern) : d2935 (change p 10000 (some 247)) = d7740 p := by
  change (if p 204 then d1717 (change p 10000 (some 247)) else d31 (change p 10000 (some 247))) = d7740 p
  rw [sub13724, sub13716]
  rfl
theorem sub13788 (p : Pattern) : d2936 (change p 10000 (some 247)) = d7741 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d2935 (change p 10000 (some 247))) = d7741 p
  rw [sub13654, sub13787]
  rfl
theorem sub13789 (p : Pattern) : d2937 (change p 10000 (some 247)) = d7742 p := by
  change (if p 163 then d2936 (change p 10000 (some 247)) else d2908 (change p 10000 (some 247))) = d7742 p
  rw [sub13788, sub13737]
  rfl
theorem sub13790 (p : Pattern) : d2938 (change p 10000 (some 247)) = d7743 p := by
  change (if p 163 then d2917 (change p 10000 (some 247)) else d2912 (change p 10000 (some 247))) = d7743 p
  rw [sub13757, sub13752]
  rfl
theorem sub13791 (p : Pattern) : d2939 (change p 10000 (some 247)) = d7744 p := by
  change (if p 162 then d2938 (change p 10000 (some 247)) else d2937 (change p 10000 (some 247))) = d7744 p
  rw [sub13790, sub13789]
  rfl
theorem sub13792 (p : Pattern) : d2940 (change p 10000 (some 247)) = d7745 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d2927 (change p 10000 (some 247))) = d7745 p
  rw [sub13654, sub13778]
  rfl
theorem sub13793 (p : Pattern) : d2941 (change p 10000 (some 247)) = d7746 p := by
  change (if p 163 then d2940 (change p 10000 (some 247)) else d2912 (change p 10000 (some 247))) = d7746 p
  rw [sub13792, sub13752]
  rfl
theorem sub13794 (p : Pattern) : d2942 (change p 10000 (some 247)) = d7747 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d2930 (change p 10000 (some 247))) = d7747 p
  rw [sub13654, sub13782]
  rfl
theorem sub13795 (p : Pattern) : d2943 (change p 10000 (some 247)) = d7748 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d2942 (change p 10000 (some 247))) = d7748 p
  rw [sub13654, sub13794]
  rfl
theorem sub13796 (p : Pattern) : d2944 (change p 10000 (some 247)) = d7749 p := by
  change (if p 162 then d2943 (change p 10000 (some 247)) else d2941 (change p 10000 (some 247))) = d7749 p
  rw [sub13795, sub13793]
  rfl
theorem sub13797 (p : Pattern) : d2945 (change p 10000 (some 247)) = d7750 p := by
  change (if p 161 then d2944 (change p 10000 (some 247)) else d2939 (change p 10000 (some 247))) = d7750 p
  rw [sub13796, sub13791]
  rfl
theorem sub13798 (p : Pattern) : d2946 (change p 10000 (some 247)) = d7751 p := by
  change (if p 160 then d2945 (change p 10000 (some 247)) else d2934 (change p 10000 (some 247))) = d7751 p
  rw [sub13797, sub13786]
  rfl
theorem sub13799 (p : Pattern) : d2947 (change p 10000 (some 247)) = d7752 p := by
  change (if p 141 then d2946 (change p 10000 (some 247)) else d2921 (change p 10000 (some 247))) = d7752 p
  rw [sub13798, sub13761]
  rfl
end NetHack.Sokoban22Refined85
