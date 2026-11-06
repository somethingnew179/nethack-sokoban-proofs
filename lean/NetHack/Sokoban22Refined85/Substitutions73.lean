/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions72
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub8760 (p : Pattern) : d1803 (change p 10000 none) = d1803 p := by
  change (if p 224 then d356 (change p 10000 none) else d1802 (change p 10000 none)) = d1803 p
  rw [sub7830, sub8759]
  rfl
theorem sub8761 (p : Pattern) : d2901 (change p 10000 none) = d2901 p := by
  change (if p 204 then d1803 (change p 10000 none) else d24 (change p 10000 none)) = d2901 p
  rw [sub8760, sub15]
  rfl
theorem sub8762 (p : Pattern) : d1701 (change p 10000 none) = d1701 p := by
  change (if p 247 then d11 (change p 10000 none) else d9 (change p 10000 none)) = d1701 p
  rw [sub32, sub13]
  rfl
theorem sub8763 (p : Pattern) : d1702 (change p 10000 none) = d1702 p := by
  change (if p 246 then d39 (change p 10000 none) else d1701 (change p 10000 none)) = d1702 p
  rw [sub33, sub8762]
  rfl
theorem sub8764 (p : Pattern) : d1703 (change p 10000 none) = d1703 p := by
  change (if p 225 then d1702 (change p 10000 none) else d24 (change p 10000 none)) = d1703 p
  rw [sub8763, sub15]
  rfl
theorem sub8765 (p : Pattern) : d1704 (change p 10000 none) = d1704 p := by
  change (if p 224 then d1702 (change p 10000 none) else d1703 (change p 10000 none)) = d1704 p
  rw [sub8763, sub8764]
  rfl
theorem sub8766 (p : Pattern) : d1705 (change p 10000 none) = d1705 p := by
  change (if p 204 then d12 (change p 10000 none) else d1704 (change p 10000 none)) = d1705 p
  rw [sub1, sub8765]
  rfl
theorem sub8767 (p : Pattern) : d2902 (change p 10000 none) = d2902 p := by
  change (if p 182 then d1705 (change p 10000 none) else d2901 (change p 10000 none)) = d2902 p
  rw [sub8766, sub8761]
  rfl
theorem sub8768 (p : Pattern) : d2903 (change p 10000 none) = d2903 p := by
  change (if p 163 then d12 (change p 10000 none) else d2902 (change p 10000 none)) = d2903 p
  rw [sub1, sub8767]
  rfl
theorem sub8769 (p : Pattern) : d2904 (change p 10000 none) = d2904 p := by
  change (if p 162 then d2903 (change p 10000 none) else d2899 (change p 10000 none)) = d2904 p
  rw [sub8768, sub8757]
  rfl
theorem sub8770 (p : Pattern) : d2905 (change p 10000 none) = d2905 p := by
  change (if p 161 then d2904 (change p 10000 none) else d2900 (change p 10000 none)) = d2905 p
  rw [sub8769, sub8758]
  rfl
theorem sub8771 (p : Pattern) : d1775 (change p 10000 none) = d1775 p := by
  change (if p 247 then d6 (change p 10000 none) else d0 (change p 10000 none)) = d1775 p
  rw [sub26, sub0]
  rfl
theorem sub8772 (p : Pattern) : d1776 (change p 10000 none) = d1776 p := by
  change (if p 246 then d34 (change p 10000 none) else d1775 (change p 10000 none)) = d1776 p
  rw [sub27, sub8771]
  rfl
theorem sub8773 (p : Pattern) : d1777 (change p 10000 none) = d1777 p := by
  change (if p 225 then d1776 (change p 10000 none) else d14 (change p 10000 none)) = d1777 p
  rw [sub8772, sub3]
  rfl
theorem sub8774 (p : Pattern) : d1785 (change p 10000 none) = d1785 p := by
  change (if p 247 then d11 (change p 10000 none) else d0 (change p 10000 none)) = d1785 p
  rw [sub32, sub0]
  rfl
theorem sub8775 (p : Pattern) : d1786 (change p 10000 none) = d1786 p := by
  change (if p 246 then d23 (change p 10000 none) else d1785 (change p 10000 none)) = d1786 p
  rw [sub14, sub8774]
  rfl
theorem sub8776 (p : Pattern) : d1787 (change p 10000 none) = d1787 p := by
  change (if p 225 then d1786 (change p 10000 none) else d1770 (change p 10000 none)) = d1787 p
  rw [sub8775, sub8736]
  rfl
theorem sub8777 (p : Pattern) : d1788 (change p 10000 none) = d1788 p := by
  change (if p 224 then d1787 (change p 10000 none) else d1777 (change p 10000 none)) = d1788 p
  rw [sub8776, sub8773]
  rfl
theorem sub8778 (p : Pattern) : d2906 (change p 10000 none) = d2906 p := by
  change (if p 204 then d1788 (change p 10000 none) else d14 (change p 10000 none)) = d2906 p
  rw [sub8777, sub3]
  rfl
theorem sub8779 (p : Pattern) : d1710 (change p 10000 none) = d1710 p := by
  change (if p 247 then d8 (change p 10000 none) else d2 (change p 10000 none)) = d1710 p
  rw [sub189, sub21]
  rfl
theorem sub8780 (p : Pattern) : d1711 (change p 10000 none) = d1711 p := by
  change (if p 246 then d190 (change p 10000 none) else d1710 (change p 10000 none)) = d1711 p
  rw [sub190, sub8779]
  rfl
theorem sub8781 (p : Pattern) : d1712 (change p 10000 none) = d1712 p := by
  change (if p 225 then d1711 (change p 10000 none) else d31 (change p 10000 none)) = d1712 p
  rw [sub8780, sub23]
  rfl
theorem sub8782 (p : Pattern) : d1713 (change p 10000 none) = d1713 p := by
  change (if p 247 then d6 (change p 10000 none) else d2 (change p 10000 none)) = d1713 p
  rw [sub26, sub21]
  rfl
theorem sub8783 (p : Pattern) : d1714 (change p 10000 none) = d1714 p := by
  change (if p 246 then d34 (change p 10000 none) else d1713 (change p 10000 none)) = d1714 p
  rw [sub27, sub8782]
  rfl
theorem sub8784 (p : Pattern) : d1715 (change p 10000 none) = d1715 p := by
  change (if p 246 then d39 (change p 10000 none) else d30 (change p 10000 none)) = d1715 p
  rw [sub33, sub22]
  rfl
theorem sub8785 (p : Pattern) : d1716 (change p 10000 none) = d1716 p := by
  change (if p 225 then d1715 (change p 10000 none) else d1714 (change p 10000 none)) = d1716 p
  rw [sub8784, sub8783]
  rfl
theorem sub8786 (p : Pattern) : d1717 (change p 10000 none) = d1717 p := by
  change (if p 224 then d1716 (change p 10000 none) else d1712 (change p 10000 none)) = d1717 p
  rw [sub8785, sub8781]
  rfl
theorem sub8787 (p : Pattern) : d1718 (change p 10000 none) = d1718 p := by
  change (if p 204 then d12 (change p 10000 none) else d1717 (change p 10000 none)) = d1718 p
  rw [sub1, sub8786]
  rfl
theorem sub8788 (p : Pattern) : d2907 (change p 10000 none) = d2907 p := by
  change (if p 182 then d1718 (change p 10000 none) else d2906 (change p 10000 none)) = d2907 p
  rw [sub8787, sub8778]
  rfl
theorem sub8789 (p : Pattern) : d364 (change p 10000 none) = d364 p := by
  change (if p 246 then d12 (change p 10000 none) else d34 (change p 10000 none)) = d364 p
  rw [sub1, sub27]
  rfl
theorem sub8790 (p : Pattern) : d1720 (change p 10000 none) = d1720 p := by
  change (if p 225 then d364 (change p 10000 none) else d35 (change p 10000 none)) = d1720 p
  rw [sub8789, sub28]
  rfl
theorem sub8791 (p : Pattern) : d1721 (change p 10000 none) = d1721 p := by
  change (if p 247 then d10 (change p 10000 none) else d6 (change p 10000 none)) = d1721 p
  rw [sub51, sub26]
  rfl
theorem sub8792 (p : Pattern) : d1722 (change p 10000 none) = d1722 p := by
  change (if p 246 then d57 (change p 10000 none) else d1721 (change p 10000 none)) = d1722 p
  rw [sub52, sub8791]
  rfl
theorem sub8793 (p : Pattern) : d1723 (change p 10000 none) = d1723 p := by
  change (if p 225 then d364 (change p 10000 none) else d1722 (change p 10000 none)) = d1723 p
  rw [sub8789, sub8792]
  rfl
theorem sub8794 (p : Pattern) : d1724 (change p 10000 none) = d1724 p := by
  change (if p 224 then d1723 (change p 10000 none) else d1720 (change p 10000 none)) = d1724 p
  rw [sub8793, sub8790]
  rfl
theorem sub8795 (p : Pattern) : d1725 (change p 10000 none) = d1725 p := by
  change (if p 204 then d12 (change p 10000 none) else d1724 (change p 10000 none)) = d1725 p
  rw [sub1, sub8794]
  rfl
theorem sub8796 (p : Pattern) : d2908 (change p 10000 none) = d2908 p := by
  change (if p 182 then d1725 (change p 10000 none) else d2906 (change p 10000 none)) = d2908 p
  rw [sub8795, sub8778]
  rfl
theorem sub8797 (p : Pattern) : d2909 (change p 10000 none) = d2909 p := by
  change (if p 163 then d2908 (change p 10000 none) else d2907 (change p 10000 none)) = d2909 p
  rw [sub8796, sub8788]
  rfl
theorem sub8798 (p : Pattern) : d327 (change p 10000 none) = d327 p := by
  change (if p 246 then d12 (change p 10000 none) else d39 (change p 10000 none)) = d327 p
  rw [sub1, sub33]
  rfl
theorem sub8799 (p : Pattern) : d1728 (change p 10000 none) = d1728 p := by
  change (if p 225 then d327 (change p 10000 none) else d40 (change p 10000 none)) = d1728 p
  rw [sub8798, sub34]
  rfl
theorem sub8800 (p : Pattern) : d1729 (change p 10000 none) = d1729 p := by
  change (if p 224 then d327 (change p 10000 none) else d1728 (change p 10000 none)) = d1729 p
  rw [sub8798, sub8799]
  rfl
theorem sub8801 (p : Pattern) : d1730 (change p 10000 none) = d1730 p := by
  change (if p 204 then d12 (change p 10000 none) else d1729 (change p 10000 none)) = d1730 p
  rw [sub1, sub8800]
  rfl
theorem sub8802 (p : Pattern) : d2910 (change p 10000 none) = d2910 p := by
  change (if p 182 then d1730 (change p 10000 none) else d2906 (change p 10000 none)) = d2910 p
  rw [sub8801, sub8778]
  rfl
theorem sub8803 (p : Pattern) : d1791 (change p 10000 none) = d1791 p := by
  change (if p 247 then d10 (change p 10000 none) else d4 (change p 10000 none)) = d1791 p
  rw [sub51, sub6]
  rfl
theorem sub8804 (p : Pattern) : d1792 (change p 10000 none) = d1792 p := by
  change (if p 246 then d57 (change p 10000 none) else d1791 (change p 10000 none)) = d1792 p
  rw [sub52, sub8803]
  rfl
theorem sub8805 (p : Pattern) : d1793 (change p 10000 none) = d1793 p := by
  change (if p 225 then d1792 (change p 10000 none) else d18 (change p 10000 none)) = d1793 p
  rw [sub8804, sub8]
  rfl
theorem sub8806 (p : Pattern) : d339 (change p 10000 none) = d339 p := by
  change (if p 246 then d12 (change p 10000 none) else d17 (change p 10000 none)) = d339 p
  rw [sub1, sub7]
  rfl
theorem sub8807 (p : Pattern) : d1796 (change p 10000 none) = d1796 p := by
  change (if p 225 then d339 (change p 10000 none) else d1795 (change p 10000 none)) = d1796 p
  rw [sub8806, sub8747]
  rfl
theorem sub8808 (p : Pattern) : d1797 (change p 10000 none) = d1797 p := by
  change (if p 224 then d1796 (change p 10000 none) else d1793 (change p 10000 none)) = d1797 p
  rw [sub8807, sub8805]
  rfl
theorem sub8809 (p : Pattern) : d2911 (change p 10000 none) = d2911 p := by
  change (if p 204 then d1797 (change p 10000 none) else d18 (change p 10000 none)) = d2911 p
  rw [sub8808, sub8]
  rfl
theorem sub8810 (p : Pattern) : d2912 (change p 10000 none) = d2912 p := by
  change (if p 182 then d12 (change p 10000 none) else d2911 (change p 10000 none)) = d2912 p
  rw [sub1, sub8809]
  rfl
theorem sub8811 (p : Pattern) : d2913 (change p 10000 none) = d2913 p := by
  change (if p 163 then d2912 (change p 10000 none) else d2910 (change p 10000 none)) = d2913 p
  rw [sub8810, sub8802]
  rfl
theorem sub8812 (p : Pattern) : d2914 (change p 10000 none) = d2914 p := by
  change (if p 162 then d2913 (change p 10000 none) else d2909 (change p 10000 none)) = d2914 p
  rw [sub8811, sub8797]
  rfl
theorem sub8813 (p : Pattern) : d2915 (change p 10000 none) = d2915 p := by
  change (if p 182 then d12 (change p 10000 none) else d2906 (change p 10000 none)) = d2915 p
  rw [sub1, sub8778]
  rfl
theorem sub8814 (p : Pattern) : d2916 (change p 10000 none) = d2916 p := by
  change (if p 163 then d2912 (change p 10000 none) else d2915 (change p 10000 none)) = d2916 p
  rw [sub8810, sub8813]
  rfl
theorem sub8815 (p : Pattern) : d2917 (change p 10000 none) = d2917 p := by
  change (if p 182 then d12 (change p 10000 none) else d2901 (change p 10000 none)) = d2917 p
  rw [sub1, sub8761]
  rfl
theorem sub8816 (p : Pattern) : d2918 (change p 10000 none) = d2918 p := by
  change (if p 163 then d12 (change p 10000 none) else d2917 (change p 10000 none)) = d2918 p
  rw [sub1, sub8815]
  rfl
theorem sub8817 (p : Pattern) : d2919 (change p 10000 none) = d2919 p := by
  change (if p 162 then d2918 (change p 10000 none) else d2916 (change p 10000 none)) = d2919 p
  rw [sub8816, sub8814]
  rfl
theorem sub8818 (p : Pattern) : d2920 (change p 10000 none) = d2920 p := by
  change (if p 161 then d2919 (change p 10000 none) else d2914 (change p 10000 none)) = d2920 p
  rw [sub8817, sub8812]
  rfl
theorem sub8819 (p : Pattern) : d2921 (change p 10000 none) = d2921 p := by
  change (if p 160 then d2920 (change p 10000 none) else d2905 (change p 10000 none)) = d2921 p
  rw [sub8818, sub8770]
  rfl
theorem sub8820 (p : Pattern) : d2029 (change p 10000 none) = d2029 p := by
  change (if p 225 then d1714 (change p 10000 none) else d31 (change p 10000 none)) = d2029 p
  rw [sub8783, sub23]
  rfl
theorem sub8821 (p : Pattern) : d2030 (change p 10000 none) = d2030 p := by
  change (if p 224 then d1714 (change p 10000 none) else d2029 (change p 10000 none)) = d2030 p
  rw [sub8783, sub8820]
  rfl
theorem sub8822 (p : Pattern) : d2922 (change p 10000 none) = d2922 p := by
  change (if p 204 then d2030 (change p 10000 none) else d31 (change p 10000 none)) = d2922 p
  rw [sub8821, sub23]
  rfl
theorem sub8823 (p : Pattern) : d1742 (change p 10000 none) = d1742 p := by
  change (if p 247 then d4 (change p 10000 none) else d2 (change p 10000 none)) = d1742 p
  rw [sub6, sub21]
  rfl
theorem sub8824 (p : Pattern) : d1743 (change p 10000 none) = d1743 p := by
  change (if p 246 then d17 (change p 10000 none) else d1742 (change p 10000 none)) = d1743 p
  rw [sub7, sub8823]
  rfl
theorem sub8825 (p : Pattern) : d1744 (change p 10000 none) = d1744 p := by
  change (if p 225 then d1743 (change p 10000 none) else d31 (change p 10000 none)) = d1744 p
  rw [sub8824, sub23]
  rfl
theorem sub8826 (p : Pattern) : d1745 (change p 10000 none) = d1745 p := by
  change (if p 224 then d1743 (change p 10000 none) else d1744 (change p 10000 none)) = d1745 p
  rw [sub8824, sub8825]
  rfl
theorem sub8827 (p : Pattern) : d1746 (change p 10000 none) = d1746 p := by
  change (if p 204 then d12 (change p 10000 none) else d1745 (change p 10000 none)) = d1746 p
  rw [sub1, sub8826]
  rfl
theorem sub8828 (p : Pattern) : d2923 (change p 10000 none) = d2923 p := by
  change (if p 182 then d1746 (change p 10000 none) else d2922 (change p 10000 none)) = d2923 p
  rw [sub8827, sub8822]
  rfl
theorem sub8829 (p : Pattern) : d2924 (change p 10000 none) = d2924 p := by
  change (if p 163 then d2923 (change p 10000 none) else d2896 (change p 10000 none)) = d2924 p
  rw [sub8828, sub8745]
  rfl
theorem sub8830 (p : Pattern) : d2925 (change p 10000 none) = d2925 p := by
  change (if p 163 then d2902 (change p 10000 none) else d2898 (change p 10000 none)) = d2925 p
  rw [sub8767, sub8756]
  rfl
theorem sub8831 (p : Pattern) : d2926 (change p 10000 none) = d2926 p := by
  change (if p 162 then d2925 (change p 10000 none) else d2924 (change p 10000 none)) = d2926 p
  rw [sub8830, sub8829]
  rfl
theorem sub8832 (p : Pattern) : d1751 (change p 10000 none) = d1751 p := by
  change (if p 225 then d329 (change p 10000 none) else d58 (change p 10000 none)) = d1751 p
  rw [sub7870, sub53]
  rfl
theorem sub8833 (p : Pattern) : d1752 (change p 10000 none) = d1752 p := by
  change (if p 224 then d329 (change p 10000 none) else d1751 (change p 10000 none)) = d1752 p
  rw [sub7870, sub8832]
  rfl
theorem sub8834 (p : Pattern) : d2927 (change p 10000 none) = d2927 p := by
  change (if p 204 then d1752 (change p 10000 none) else d58 (change p 10000 none)) = d2927 p
  rw [sub8833, sub53]
  rfl
theorem sub8835 (p : Pattern) : d1753 (change p 10000 none) = d1753 p := by
  change (if p 204 then d12 (change p 10000 none) else d1752 (change p 10000 none)) = d1753 p
  rw [sub1, sub8833]
  rfl
theorem sub8836 (p : Pattern) : d2928 (change p 10000 none) = d2928 p := by
  change (if p 182 then d1753 (change p 10000 none) else d2927 (change p 10000 none)) = d2928 p
  rw [sub8835, sub8834]
  rfl
theorem sub8837 (p : Pattern) : d2929 (change p 10000 none) = d2929 p := by
  change (if p 163 then d2928 (change p 10000 none) else d2898 (change p 10000 none)) = d2929 p
  rw [sub8836, sub8756]
  rfl
theorem sub8838 (p : Pattern) : d2930 (change p 10000 none) = d2930 p := by
  change (if p 204 then d1729 (change p 10000 none) else d40 (change p 10000 none)) = d2930 p
  rw [sub8800, sub34]
  rfl
theorem sub8839 (p : Pattern) : d2931 (change p 10000 none) = d2931 p := by
  change (if p 182 then d1730 (change p 10000 none) else d2930 (change p 10000 none)) = d2931 p
  rw [sub8801, sub8838]
  rfl
theorem sub8840 (p : Pattern) : d2932 (change p 10000 none) = d2932 p := by
  change (if p 163 then d12 (change p 10000 none) else d2931 (change p 10000 none)) = d2932 p
  rw [sub1, sub8839]
  rfl
theorem sub8841 (p : Pattern) : d2933 (change p 10000 none) = d2933 p := by
  change (if p 162 then d2932 (change p 10000 none) else d2929 (change p 10000 none)) = d2933 p
  rw [sub8840, sub8837]
  rfl
theorem sub8842 (p : Pattern) : d2934 (change p 10000 none) = d2934 p := by
  change (if p 161 then d2933 (change p 10000 none) else d2926 (change p 10000 none)) = d2934 p
  rw [sub8841, sub8831]
  rfl
theorem sub8843 (p : Pattern) : d2935 (change p 10000 none) = d2935 p := by
  change (if p 204 then d1717 (change p 10000 none) else d31 (change p 10000 none)) = d2935 p
  rw [sub8786, sub23]
  rfl
theorem sub8844 (p : Pattern) : d2936 (change p 10000 none) = d2936 p := by
  change (if p 182 then d12 (change p 10000 none) else d2935 (change p 10000 none)) = d2936 p
  rw [sub1, sub8843]
  rfl
theorem sub8845 (p : Pattern) : d2937 (change p 10000 none) = d2937 p := by
  change (if p 163 then d2936 (change p 10000 none) else d2908 (change p 10000 none)) = d2937 p
  rw [sub8844, sub8796]
  rfl
theorem sub8846 (p : Pattern) : d2938 (change p 10000 none) = d2938 p := by
  change (if p 163 then d2917 (change p 10000 none) else d2912 (change p 10000 none)) = d2938 p
  rw [sub8815, sub8810]
  rfl
theorem sub8847 (p : Pattern) : d2939 (change p 10000 none) = d2939 p := by
  change (if p 162 then d2938 (change p 10000 none) else d2937 (change p 10000 none)) = d2939 p
  rw [sub8846, sub8845]
  rfl
theorem sub8848 (p : Pattern) : d2940 (change p 10000 none) = d2940 p := by
  change (if p 182 then d12 (change p 10000 none) else d2927 (change p 10000 none)) = d2940 p
  rw [sub1, sub8834]
  rfl
theorem sub8849 (p : Pattern) : d2941 (change p 10000 none) = d2941 p := by
  change (if p 163 then d2940 (change p 10000 none) else d2912 (change p 10000 none)) = d2941 p
  rw [sub8848, sub8810]
  rfl
theorem sub8850 (p : Pattern) : d2942 (change p 10000 none) = d2942 p := by
  change (if p 182 then d12 (change p 10000 none) else d2930 (change p 10000 none)) = d2942 p
  rw [sub1, sub8838]
  rfl
theorem sub8851 (p : Pattern) : d2943 (change p 10000 none) = d2943 p := by
  change (if p 163 then d12 (change p 10000 none) else d2942 (change p 10000 none)) = d2943 p
  rw [sub1, sub8850]
  rfl
theorem sub8852 (p : Pattern) : d2944 (change p 10000 none) = d2944 p := by
  change (if p 162 then d2943 (change p 10000 none) else d2941 (change p 10000 none)) = d2944 p
  rw [sub8851, sub8849]
  rfl
theorem sub8853 (p : Pattern) : d2945 (change p 10000 none) = d2945 p := by
  change (if p 161 then d2944 (change p 10000 none) else d2939 (change p 10000 none)) = d2945 p
  rw [sub8852, sub8847]
  rfl
theorem sub8854 (p : Pattern) : d2946 (change p 10000 none) = d2946 p := by
  change (if p 160 then d2945 (change p 10000 none) else d2934 (change p 10000 none)) = d2946 p
  rw [sub8853, sub8842]
  rfl
theorem sub8855 (p : Pattern) : d2947 (change p 10000 none) = d2947 p := by
  change (if p 141 then d2946 (change p 10000 none) else d2921 (change p 10000 none)) = d2947 p
  rw [sub8854, sub8819]
  rfl
theorem sub8856 (p : Pattern) : d2047 (change p 10000 none) = d2047 p := by
  change (if p 225 then d1776 (change p 10000 none) else d1770 (change p 10000 none)) = d2047 p
  rw [sub8772, sub8736]
  rfl
theorem sub8857 (p : Pattern) : d2048 (change p 10000 none) = d2048 p := by
  change (if p 224 then d2047 (change p 10000 none) else d1777 (change p 10000 none)) = d2048 p
  rw [sub8856, sub8773]
  rfl
theorem sub8858 (p : Pattern) : d2948 (change p 10000 none) = d2948 p := by
  change (if p 204 then d2048 (change p 10000 none) else d14 (change p 10000 none)) = d2948 p
  rw [sub8857, sub3]
  rfl
theorem sub8859 (p : Pattern) : d1773 (change p 10000 none) = d1773 p := by
  change (if p 204 then d12 (change p 10000 none) else d1772 (change p 10000 none)) = d1773 p
  rw [sub1, sub8738]
  rfl
theorem sub8860 (p : Pattern) : d2949 (change p 10000 none) = d2949 p := by
  change (if p 182 then d1773 (change p 10000 none) else d2948 (change p 10000 none)) = d2949 p
  rw [sub8859, sub8858]
  rfl
theorem sub8861 (p : Pattern) : d2051 (change p 10000 none) = d2051 p := by
  change (if p 247 then d10 (change p 10000 none) else d0 (change p 10000 none)) = d2051 p
  rw [sub51, sub0]
  rfl
theorem sub8862 (p : Pattern) : d2052 (change p 10000 none) = d2052 p := by
  change (if p 246 then d23 (change p 10000 none) else d2051 (change p 10000 none)) = d2052 p
  rw [sub14, sub8861]
  rfl
theorem sub8863 (p : Pattern) : d2053 (change p 10000 none) = d2053 p := by
  change (if p 225 then d2052 (change p 10000 none) else d1770 (change p 10000 none)) = d2053 p
  rw [sub8862, sub8736]
  rfl
theorem sub8864 (p : Pattern) : d2054 (change p 10000 none) = d2054 p := by
  change (if p 224 then d2053 (change p 10000 none) else d1777 (change p 10000 none)) = d2054 p
  rw [sub8863, sub8773]
  rfl
theorem sub8865 (p : Pattern) : d2950 (change p 10000 none) = d2950 p := by
  change (if p 204 then d2054 (change p 10000 none) else d14 (change p 10000 none)) = d2950 p
  rw [sub8864, sub3]
  rfl
theorem sub8866 (p : Pattern) : d1778 (change p 10000 none) = d1778 p := by
  change (if p 247 then d8 (change p 10000 none) else d0 (change p 10000 none)) = d1778 p
  rw [sub189, sub0]
  rfl
theorem sub8867 (p : Pattern) : d1779 (change p 10000 none) = d1779 p := by
  change (if p 246 then d190 (change p 10000 none) else d1778 (change p 10000 none)) = d1779 p
  rw [sub190, sub8866]
  rfl
theorem sub8868 (p : Pattern) : d1780 (change p 10000 none) = d1780 p := by
  change (if p 225 then d1779 (change p 10000 none) else d1770 (change p 10000 none)) = d1780 p
  rw [sub8867, sub8736]
  rfl
theorem sub8869 (p : Pattern) : d1781 (change p 10000 none) = d1781 p := by
  change (if p 224 then d1780 (change p 10000 none) else d1777 (change p 10000 none)) = d1781 p
  rw [sub8868, sub8773]
  rfl
theorem sub8870 (p : Pattern) : d1782 (change p 10000 none) = d1782 p := by
  change (if p 204 then d12 (change p 10000 none) else d1781 (change p 10000 none)) = d1782 p
  rw [sub1, sub8869]
  rfl
theorem sub8871 (p : Pattern) : d2951 (change p 10000 none) = d2951 p := by
  change (if p 182 then d1782 (change p 10000 none) else d2950 (change p 10000 none)) = d2951 p
  rw [sub8870, sub8865]
  rfl
theorem sub8872 (p : Pattern) : d2952 (change p 10000 none) = d2952 p := by
  change (if p 163 then d2951 (change p 10000 none) else d2949 (change p 10000 none)) = d2952 p
  rw [sub8871, sub8860]
  rfl
theorem sub8873 (p : Pattern) : d1789 (change p 10000 none) = d1789 p := by
  change (if p 204 then d12 (change p 10000 none) else d1788 (change p 10000 none)) = d1789 p
  rw [sub1, sub8777]
  rfl
theorem sub8874 (p : Pattern) : d2953 (change p 10000 none) = d2953 p := by
  change (if p 182 then d1789 (change p 10000 none) else d2906 (change p 10000 none)) = d2953 p
  rw [sub8873, sub8778]
  rfl
theorem sub8875 (p : Pattern) : d1798 (change p 10000 none) = d1798 p := by
  change (if p 204 then d12 (change p 10000 none) else d1797 (change p 10000 none)) = d1798 p
  rw [sub1, sub8808]
  rfl
theorem sub8876 (p : Pattern) : d2954 (change p 10000 none) = d2954 p := by
  change (if p 182 then d1798 (change p 10000 none) else d2911 (change p 10000 none)) = d2954 p
  rw [sub8875, sub8809]
  rfl
theorem sub8877 (p : Pattern) : d2955 (change p 10000 none) = d2955 p := by
  change (if p 163 then d2954 (change p 10000 none) else d2953 (change p 10000 none)) = d2955 p
  rw [sub8876, sub8874]
  rfl
theorem sub8878 (p : Pattern) : d2956 (change p 10000 none) = d2956 p := by
  change (if p 162 then d2955 (change p 10000 none) else d2952 (change p 10000 none)) = d2956 p
  rw [sub8877, sub8872]
  rfl
theorem sub8879 (p : Pattern) : d1804 (change p 10000 none) = d1804 p := by
  change (if p 204 then d12 (change p 10000 none) else d1803 (change p 10000 none)) = d1804 p
  rw [sub1, sub8760]
  rfl
end NetHack.Sokoban22Refined85
