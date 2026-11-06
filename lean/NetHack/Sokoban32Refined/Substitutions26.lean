/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions25
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3120 (p : Pattern) : d820 (change p 161 none) = d1766 p := by
  change (if p 113 then d783 (change p 161 none) else d778 (change p 161 none)) = d1766 p
  rw [sub3083, sub3078]
  rfl
theorem sub3121 (p : Pattern) : d821 (change p 161 none) = d1767 p := by
  change (if p 113 then d2 (change p 161 none) else d809 (change p 161 none)) = d1767 p
  rw [sub3036, sub3109]
  rfl
theorem sub3122 (p : Pattern) : d822 (change p 161 none) = d1768 p := by
  change (if p 112 then d821 (change p 161 none) else d820 (change p 161 none)) = d1768 p
  rw [sub3121, sub3120]
  rfl
theorem sub3123 (p : Pattern) : d823 (change p 161 none) = d1769 p := by
  change (if p 106 then d822 (change p 161 none) else d819 (change p 161 none)) = d1769 p
  rw [sub3122, sub3119]
  rfl
theorem sub3124 (p : Pattern) : d824 (change p 161 none) = d1770 p := by
  change (if p 86 then d823 (change p 161 none) else d815 (change p 161 none)) = d1770 p
  rw [sub3123, sub3115]
  rfl
theorem sub3125 (p : Pattern) : d825 (change p 161 none) = d1771 p := by
  change (if p 80 then d824 (change p 161 none) else d813 (change p 161 none)) = d1771 p
  rw [sub3124, sub3113]
  rfl
theorem sub3126 (p : Pattern) : d0 (change p 159 (some 158)) = d0 p := by
  rfl
theorem sub3127 (p : Pattern) : d2 (change p 159 (some 158)) = d2 p := by
  rfl
theorem sub3128 (p : Pattern) : d3 (change p 159 (some 158)) = d3 p := by
  change (if p 161 then d2 (change p 159 (some 158)) else d0 (change p 159 (some 158))) = d3 p
  rw [sub3127, sub3126]
  rfl
theorem sub3129 (p : Pattern) : d4 (change p 159 (some 158)) = d4 p := by
  change (if p 160 then d3 (change p 159 (some 158)) else d0 (change p 159 (some 158))) = d4 p
  rw [sub3128, sub3126]
  rfl
theorem sub3130 (p : Pattern) : d7 (change p 159 (some 158)) = d4 p := by
  change d4 (change p 159 (some 158)) = d4 p
  exact sub3129 p
theorem sub3131 (p : Pattern) : d1 (change p 159 (some 158)) = d1 p := by
  rfl
theorem sub3132 (p : Pattern) : d9 (change p 159 (some 158)) = d9 p := by
  change (if p 161 then d2 (change p 159 (some 158)) else d1 (change p 159 (some 158))) = d9 p
  rw [sub3127, sub3131]
  rfl
theorem sub3133 (p : Pattern) : d10 (change p 159 (some 158)) = d10 p := by
  change (if p 160 then d9 (change p 159 (some 158)) else d1 (change p 159 (some 158))) = d10 p
  rw [sub3132, sub3131]
  rfl
theorem sub3134 (p : Pattern) : d13 (change p 159 (some 158)) = d10 p := by
  change d10 (change p 159 (some 158)) = d10 p
  exact sub3133 p
theorem sub3135 (p : Pattern) : d653 (change p 159 (some 158)) = d1772 p := by
  change (if p 139 then d13 (change p 159 (some 158)) else d7 (change p 159 (some 158))) = d1772 p
  rw [sub3134, sub3130]
  rfl
theorem sub3136 (p : Pattern) : d654 (change p 159 (some 158)) = d1773 p := by
  change (if p 138 then d653 (change p 159 (some 158)) else d7 (change p 159 (some 158))) = d1773 p
  rw [sub3135, sub3130]
  rfl
theorem sub3137 (p : Pattern) : d655 (change p 159 (some 158)) = d1774 p := by
  change (if p 139 then d2 (change p 159 (some 158)) else d7 (change p 159 (some 158))) = d1774 p
  rw [sub3127, sub3130]
  rfl
theorem sub3138 (p : Pattern) : d656 (change p 159 (some 158)) = d1775 p := by
  change (if p 138 then d655 (change p 159 (some 158)) else d653 (change p 159 (some 158))) = d1775 p
  rw [sub3137, sub3135]
  rfl
theorem sub3139 (p : Pattern) : d657 (change p 159 (some 158)) = d1776 p := by
  change (if p 113 then d656 (change p 159 (some 158)) else d653 (change p 159 (some 158))) = d1776 p
  rw [sub3138, sub3135]
  rfl
theorem sub3140 (p : Pattern) : d658 (change p 159 (some 158)) = d1777 p := by
  change (if p 112 then d657 (change p 159 (some 158)) else d654 (change p 159 (some 158))) = d1777 p
  rw [sub3139, sub3136]
  rfl
theorem sub3141 (p : Pattern) : d659 (change p 159 (some 158)) = d1778 p := by
  change (if p 139 then d2 (change p 159 (some 158)) else d13 (change p 159 (some 158))) = d1778 p
  rw [sub3127, sub3134]
  rfl
theorem sub3142 (p : Pattern) : d660 (change p 159 (some 158)) = d1779 p := by
  change (if p 138 then d659 (change p 159 (some 158)) else d13 (change p 159 (some 158))) = d1779 p
  rw [sub3141, sub3134]
  rfl
theorem sub3143 (p : Pattern) : d661 (change p 159 (some 158)) = d1780 p := by
  change (if p 133 then d660 (change p 159 (some 158)) else d654 (change p 159 (some 158))) = d1780 p
  rw [sub3142, sub3136]
  rfl
theorem sub3144 (p : Pattern) : d662 (change p 159 (some 158)) = d1781 p := by
  change (if p 132 then d661 (change p 159 (some 158)) else d654 (change p 159 (some 158))) = d1781 p
  rw [sub3143, sub3136]
  rfl
theorem sub3145 (p : Pattern) : d663 (change p 159 (some 158)) = d1782 p := by
  change (if p 133 then d659 (change p 159 (some 158)) else d654 (change p 159 (some 158))) = d1782 p
  rw [sub3141, sub3136]
  rfl
theorem sub3146 (p : Pattern) : d664 (change p 159 (some 158)) = d1783 p := by
  change (if p 132 then d663 (change p 159 (some 158)) else d654 (change p 159 (some 158))) = d1783 p
  rw [sub3145, sub3136]
  rfl
theorem sub3147 (p : Pattern) : d665 (change p 159 (some 158)) = d1784 p := by
  change (if p 113 then d664 (change p 159 (some 158)) else d662 (change p 159 (some 158))) = d1784 p
  rw [sub3146, sub3144]
  rfl
theorem sub3148 (p : Pattern) : d666 (change p 159 (some 158)) = d1785 p := by
  change (if p 133 then d659 (change p 159 (some 158)) else d653 (change p 159 (some 158))) = d1785 p
  rw [sub3141, sub3135]
  rfl
theorem sub3149 (p : Pattern) : d667 (change p 159 (some 158)) = d1786 p := by
  change (if p 132 then d666 (change p 159 (some 158)) else d653 (change p 159 (some 158))) = d1786 p
  rw [sub3148, sub3135]
  rfl
theorem sub3150 (p : Pattern) : d668 (change p 159 (some 158)) = d1787 p := by
  change (if p 133 then d659 (change p 159 (some 158)) else d656 (change p 159 (some 158))) = d1787 p
  rw [sub3141, sub3138]
  rfl
theorem sub3151 (p : Pattern) : d669 (change p 159 (some 158)) = d1788 p := by
  change (if p 132 then d668 (change p 159 (some 158)) else d656 (change p 159 (some 158))) = d1788 p
  rw [sub3150, sub3138]
  rfl
theorem sub3152 (p : Pattern) : d670 (change p 159 (some 158)) = d1789 p := by
  change (if p 113 then d669 (change p 159 (some 158)) else d667 (change p 159 (some 158))) = d1789 p
  rw [sub3151, sub3149]
  rfl
theorem sub3153 (p : Pattern) : d671 (change p 159 (some 158)) = d1790 p := by
  change (if p 112 then d670 (change p 159 (some 158)) else d665 (change p 159 (some 158))) = d1790 p
  rw [sub3152, sub3147]
  rfl
theorem sub3154 (p : Pattern) : d672 (change p 159 (some 158)) = d1791 p := by
  change (if p 106 then d671 (change p 159 (some 158)) else d658 (change p 159 (some 158))) = d1791 p
  rw [sub3153, sub3140]
  rfl
theorem sub3155 (p : Pattern) : d673 (change p 159 (some 158)) = d1792 p := by
  change (if p 138 then d655 (change p 159 (some 158)) else d7 (change p 159 (some 158))) = d1792 p
  rw [sub3137, sub3130]
  rfl
theorem sub3156 (p : Pattern) : d674 (change p 159 (some 158)) = d1793 p := by
  change (if p 113 then d673 (change p 159 (some 158)) else d654 (change p 159 (some 158))) = d1793 p
  rw [sub3155, sub3136]
  rfl
theorem sub3157 (p : Pattern) : d675 (change p 159 (some 158)) = d1794 p := by
  change (if p 112 then d660 (change p 159 (some 158)) else d674 (change p 159 (some 158))) = d1794 p
  rw [sub3142, sub3156]
  rfl
theorem sub3158 (p : Pattern) : d676 (change p 159 (some 158)) = d1795 p := by
  change (if p 133 then d659 (change p 159 (some 158)) else d673 (change p 159 (some 158))) = d1795 p
  rw [sub3141, sub3155]
  rfl
theorem sub3159 (p : Pattern) : d677 (change p 159 (some 158)) = d1796 p := by
  change (if p 132 then d676 (change p 159 (some 158)) else d673 (change p 159 (some 158))) = d1796 p
  rw [sub3158, sub3155]
  rfl
theorem sub3160 (p : Pattern) : d678 (change p 159 (some 158)) = d1797 p := by
  change (if p 113 then d677 (change p 159 (some 158)) else d664 (change p 159 (some 158))) = d1797 p
  rw [sub3159, sub3146]
  rfl
theorem sub3161 (p : Pattern) : d679 (change p 159 (some 158)) = d1798 p := by
  change (if p 133 then d2 (change p 159 (some 158)) else d660 (change p 159 (some 158))) = d1798 p
  rw [sub3127, sub3142]
  rfl
theorem sub3162 (p : Pattern) : d680 (change p 159 (some 158)) = d1799 p := by
  change (if p 132 then d679 (change p 159 (some 158)) else d660 (change p 159 (some 158))) = d1799 p
  rw [sub3161, sub3142]
  rfl
theorem sub3163 (p : Pattern) : d681 (change p 159 (some 158)) = d1800 p := by
  change (if p 133 then d2 (change p 159 (some 158)) else d659 (change p 159 (some 158))) = d1800 p
  rw [sub3127, sub3141]
  rfl
theorem sub3164 (p : Pattern) : d682 (change p 159 (some 158)) = d1801 p := by
  change (if p 132 then d681 (change p 159 (some 158)) else d659 (change p 159 (some 158))) = d1801 p
  rw [sub3163, sub3141]
  rfl
theorem sub3165 (p : Pattern) : d683 (change p 159 (some 158)) = d1802 p := by
  change (if p 113 then d682 (change p 159 (some 158)) else d680 (change p 159 (some 158))) = d1802 p
  rw [sub3164, sub3162]
  rfl
theorem sub3166 (p : Pattern) : d684 (change p 159 (some 158)) = d1803 p := by
  change (if p 112 then d683 (change p 159 (some 158)) else d678 (change p 159 (some 158))) = d1803 p
  rw [sub3165, sub3160]
  rfl
theorem sub3167 (p : Pattern) : d685 (change p 159 (some 158)) = d1804 p := by
  change (if p 106 then d684 (change p 159 (some 158)) else d675 (change p 159 (some 158))) = d1804 p
  rw [sub3166, sub3157]
  rfl
theorem sub3168 (p : Pattern) : d686 (change p 159 (some 158)) = d1805 p := by
  change (if p 86 then d685 (change p 159 (some 158)) else d672 (change p 159 (some 158))) = d1805 p
  rw [sub3167, sub3154]
  rfl
theorem sub3169 (p : Pattern) : d687 (change p 159 (some 158)) = d1806 p := by
  change (if p 112 then d670 (change p 159 (some 158)) else d664 (change p 159 (some 158))) = d1806 p
  rw [sub3152, sub3146]
  rfl
theorem sub3170 (p : Pattern) : d688 (change p 159 (some 158)) = d1807 p := by
  change (if p 106 then d687 (change p 159 (some 158)) else d658 (change p 159 (some 158))) = d1807 p
  rw [sub3169, sub3140]
  rfl
theorem sub3171 (p : Pattern) : d689 (change p 159 (some 158)) = d1808 p := by
  change (if p 113 then d659 (change p 159 (some 158)) else d660 (change p 159 (some 158))) = d1808 p
  rw [sub3141, sub3142]
  rfl
theorem sub3172 (p : Pattern) : d690 (change p 159 (some 158)) = d1809 p := by
  change (if p 112 then d689 (change p 159 (some 158)) else d674 (change p 159 (some 158))) = d1809 p
  rw [sub3171, sub3156]
  rfl
theorem sub3173 (p : Pattern) : d691 (change p 159 (some 158)) = d1810 p := by
  change (if p 113 then d669 (change p 159 (some 158)) else d664 (change p 159 (some 158))) = d1810 p
  rw [sub3151, sub3146]
  rfl
theorem sub3174 (p : Pattern) : d692 (change p 159 (some 158)) = d1811 p := by
  change (if p 113 then d2 (change p 159 (some 158)) else d682 (change p 159 (some 158))) = d1811 p
  rw [sub3127, sub3164]
  rfl
theorem sub3175 (p : Pattern) : d693 (change p 159 (some 158)) = d1812 p := by
  change (if p 112 then d692 (change p 159 (some 158)) else d691 (change p 159 (some 158))) = d1812 p
  rw [sub3174, sub3173]
  rfl
theorem sub3176 (p : Pattern) : d694 (change p 159 (some 158)) = d1813 p := by
  change (if p 106 then d693 (change p 159 (some 158)) else d690 (change p 159 (some 158))) = d1813 p
  rw [sub3175, sub3172]
  rfl
theorem sub3177 (p : Pattern) : d695 (change p 159 (some 158)) = d1814 p := by
  change (if p 86 then d694 (change p 159 (some 158)) else d688 (change p 159 (some 158))) = d1814 p
  rw [sub3176, sub3170]
  rfl
theorem sub3178 (p : Pattern) : d696 (change p 159 (some 158)) = d1815 p := by
  change (if p 80 then d695 (change p 159 (some 158)) else d686 (change p 159 (some 158))) = d1815 p
  rw [sub3177, sub3168]
  rfl
theorem sub3179 (p : Pattern) : d0 (change p 160 (some 159)) = d0 p := by
  rfl
theorem sub3180 (p : Pattern) : d5 (change p 160 (some 159)) = d0 p := by
  change d0 (change p 160 (some 159)) = d0 p
  exact sub3179 p
theorem sub3181 (p : Pattern) : d2 (change p 160 (some 159)) = d2 p := by
  rfl
theorem sub3182 (p : Pattern) : d37 (change p 160 (some 159)) = d2 p := by
  change d2 (change p 160 (some 159)) = d2 p
  exact sub3181 p
theorem sub3183 (p : Pattern) : d697 (change p 160 (some 159)) = d1816 p := by
  change (if p 158 then d37 (change p 160 (some 159)) else d5 (change p 160 (some 159))) = d1816 p
  rw [sub3182, sub3180]
  rfl
theorem sub3184 (p : Pattern) : d1 (change p 160 (some 159)) = d1 p := by
  rfl
theorem sub3185 (p : Pattern) : d11 (change p 160 (some 159)) = d1 p := by
  change d1 (change p 160 (some 159)) = d1 p
  exact sub3184 p
theorem sub3186 (p : Pattern) : d39 (change p 160 (some 159)) = d2 p := by
  change d2 (change p 160 (some 159)) = d2 p
  exact sub3181 p
theorem sub3187 (p : Pattern) : d698 (change p 160 (some 159)) = d1817 p := by
  change (if p 158 then d39 (change p 160 (some 159)) else d11 (change p 160 (some 159))) = d1817 p
  rw [sub3186, sub3185]
  rfl
theorem sub3188 (p : Pattern) : d699 (change p 160 (some 159)) = d1818 p := by
  change (if p 139 then d698 (change p 160 (some 159)) else d697 (change p 160 (some 159))) = d1818 p
  rw [sub3187, sub3183]
  rfl
theorem sub3189 (p : Pattern) : d700 (change p 160 (some 159)) = d1819 p := by
  change (if p 138 then d699 (change p 160 (some 159)) else d697 (change p 160 (some 159))) = d1819 p
  rw [sub3188, sub3183]
  rfl
theorem sub3190 (p : Pattern) : d701 (change p 160 (some 159)) = d1820 p := by
  change (if p 139 then d2 (change p 160 (some 159)) else d697 (change p 160 (some 159))) = d1820 p
  rw [sub3181, sub3183]
  rfl
theorem sub3191 (p : Pattern) : d702 (change p 160 (some 159)) = d1821 p := by
  change (if p 138 then d701 (change p 160 (some 159)) else d699 (change p 160 (some 159))) = d1821 p
  rw [sub3190, sub3188]
  rfl
theorem sub3192 (p : Pattern) : d703 (change p 160 (some 159)) = d1822 p := by
  change (if p 113 then d702 (change p 160 (some 159)) else d699 (change p 160 (some 159))) = d1822 p
  rw [sub3191, sub3188]
  rfl
theorem sub3193 (p : Pattern) : d704 (change p 160 (some 159)) = d1823 p := by
  change (if p 112 then d703 (change p 160 (some 159)) else d700 (change p 160 (some 159))) = d1823 p
  rw [sub3192, sub3189]
  rfl
theorem sub3194 (p : Pattern) : d705 (change p 160 (some 159)) = d1824 p := by
  change (if p 139 then d2 (change p 160 (some 159)) else d698 (change p 160 (some 159))) = d1824 p
  rw [sub3181, sub3187]
  rfl
theorem sub3195 (p : Pattern) : d706 (change p 160 (some 159)) = d1825 p := by
  change (if p 138 then d705 (change p 160 (some 159)) else d698 (change p 160 (some 159))) = d1825 p
  rw [sub3194, sub3187]
  rfl
theorem sub3196 (p : Pattern) : d707 (change p 160 (some 159)) = d1826 p := by
  change (if p 133 then d706 (change p 160 (some 159)) else d700 (change p 160 (some 159))) = d1826 p
  rw [sub3195, sub3189]
  rfl
theorem sub3197 (p : Pattern) : d708 (change p 160 (some 159)) = d1827 p := by
  change (if p 132 then d707 (change p 160 (some 159)) else d700 (change p 160 (some 159))) = d1827 p
  rw [sub3196, sub3189]
  rfl
theorem sub3198 (p : Pattern) : d709 (change p 160 (some 159)) = d1828 p := by
  change (if p 133 then d705 (change p 160 (some 159)) else d700 (change p 160 (some 159))) = d1828 p
  rw [sub3194, sub3189]
  rfl
theorem sub3199 (p : Pattern) : d710 (change p 160 (some 159)) = d1829 p := by
  change (if p 132 then d709 (change p 160 (some 159)) else d700 (change p 160 (some 159))) = d1829 p
  rw [sub3198, sub3189]
  rfl
theorem sub3200 (p : Pattern) : d711 (change p 160 (some 159)) = d1830 p := by
  change (if p 113 then d710 (change p 160 (some 159)) else d708 (change p 160 (some 159))) = d1830 p
  rw [sub3199, sub3197]
  rfl
theorem sub3201 (p : Pattern) : d712 (change p 160 (some 159)) = d1831 p := by
  change (if p 133 then d705 (change p 160 (some 159)) else d699 (change p 160 (some 159))) = d1831 p
  rw [sub3194, sub3188]
  rfl
theorem sub3202 (p : Pattern) : d713 (change p 160 (some 159)) = d1832 p := by
  change (if p 132 then d712 (change p 160 (some 159)) else d699 (change p 160 (some 159))) = d1832 p
  rw [sub3201, sub3188]
  rfl
theorem sub3203 (p : Pattern) : d714 (change p 160 (some 159)) = d1833 p := by
  change (if p 133 then d705 (change p 160 (some 159)) else d702 (change p 160 (some 159))) = d1833 p
  rw [sub3194, sub3191]
  rfl
theorem sub3204 (p : Pattern) : d715 (change p 160 (some 159)) = d1834 p := by
  change (if p 132 then d714 (change p 160 (some 159)) else d702 (change p 160 (some 159))) = d1834 p
  rw [sub3203, sub3191]
  rfl
theorem sub3205 (p : Pattern) : d716 (change p 160 (some 159)) = d1835 p := by
  change (if p 113 then d715 (change p 160 (some 159)) else d713 (change p 160 (some 159))) = d1835 p
  rw [sub3204, sub3202]
  rfl
theorem sub3206 (p : Pattern) : d717 (change p 160 (some 159)) = d1836 p := by
  change (if p 112 then d716 (change p 160 (some 159)) else d711 (change p 160 (some 159))) = d1836 p
  rw [sub3205, sub3200]
  rfl
theorem sub3207 (p : Pattern) : d718 (change p 160 (some 159)) = d1837 p := by
  change (if p 106 then d717 (change p 160 (some 159)) else d704 (change p 160 (some 159))) = d1837 p
  rw [sub3206, sub3193]
  rfl
theorem sub3208 (p : Pattern) : d719 (change p 160 (some 159)) = d1838 p := by
  change (if p 138 then d701 (change p 160 (some 159)) else d697 (change p 160 (some 159))) = d1838 p
  rw [sub3190, sub3183]
  rfl
theorem sub3209 (p : Pattern) : d720 (change p 160 (some 159)) = d1839 p := by
  change (if p 113 then d719 (change p 160 (some 159)) else d700 (change p 160 (some 159))) = d1839 p
  rw [sub3208, sub3189]
  rfl
theorem sub3210 (p : Pattern) : d721 (change p 160 (some 159)) = d1840 p := by
  change (if p 112 then d706 (change p 160 (some 159)) else d720 (change p 160 (some 159))) = d1840 p
  rw [sub3195, sub3209]
  rfl
theorem sub3211 (p : Pattern) : d722 (change p 160 (some 159)) = d1841 p := by
  change (if p 133 then d705 (change p 160 (some 159)) else d719 (change p 160 (some 159))) = d1841 p
  rw [sub3194, sub3208]
  rfl
theorem sub3212 (p : Pattern) : d723 (change p 160 (some 159)) = d1842 p := by
  change (if p 132 then d722 (change p 160 (some 159)) else d719 (change p 160 (some 159))) = d1842 p
  rw [sub3211, sub3208]
  rfl
theorem sub3213 (p : Pattern) : d724 (change p 160 (some 159)) = d1843 p := by
  change (if p 113 then d723 (change p 160 (some 159)) else d710 (change p 160 (some 159))) = d1843 p
  rw [sub3212, sub3199]
  rfl
theorem sub3214 (p : Pattern) : d725 (change p 160 (some 159)) = d1844 p := by
  change (if p 133 then d2 (change p 160 (some 159)) else d706 (change p 160 (some 159))) = d1844 p
  rw [sub3181, sub3195]
  rfl
theorem sub3215 (p : Pattern) : d726 (change p 160 (some 159)) = d1845 p := by
  change (if p 132 then d725 (change p 160 (some 159)) else d706 (change p 160 (some 159))) = d1845 p
  rw [sub3214, sub3195]
  rfl
theorem sub3216 (p : Pattern) : d727 (change p 160 (some 159)) = d1846 p := by
  change (if p 133 then d2 (change p 160 (some 159)) else d705 (change p 160 (some 159))) = d1846 p
  rw [sub3181, sub3194]
  rfl
theorem sub3217 (p : Pattern) : d728 (change p 160 (some 159)) = d1847 p := by
  change (if p 132 then d727 (change p 160 (some 159)) else d705 (change p 160 (some 159))) = d1847 p
  rw [sub3216, sub3194]
  rfl
theorem sub3218 (p : Pattern) : d729 (change p 160 (some 159)) = d1848 p := by
  change (if p 113 then d728 (change p 160 (some 159)) else d726 (change p 160 (some 159))) = d1848 p
  rw [sub3217, sub3215]
  rfl
theorem sub3219 (p : Pattern) : d730 (change p 160 (some 159)) = d1849 p := by
  change (if p 112 then d729 (change p 160 (some 159)) else d724 (change p 160 (some 159))) = d1849 p
  rw [sub3218, sub3213]
  rfl
theorem sub3220 (p : Pattern) : d731 (change p 160 (some 159)) = d1850 p := by
  change (if p 106 then d730 (change p 160 (some 159)) else d721 (change p 160 (some 159))) = d1850 p
  rw [sub3219, sub3210]
  rfl
theorem sub3221 (p : Pattern) : d732 (change p 160 (some 159)) = d1851 p := by
  change (if p 86 then d731 (change p 160 (some 159)) else d718 (change p 160 (some 159))) = d1851 p
  rw [sub3220, sub3207]
  rfl
theorem sub3222 (p : Pattern) : d733 (change p 160 (some 159)) = d1852 p := by
  change (if p 112 then d716 (change p 160 (some 159)) else d710 (change p 160 (some 159))) = d1852 p
  rw [sub3205, sub3199]
  rfl
theorem sub3223 (p : Pattern) : d734 (change p 160 (some 159)) = d1853 p := by
  change (if p 106 then d733 (change p 160 (some 159)) else d704 (change p 160 (some 159))) = d1853 p
  rw [sub3222, sub3193]
  rfl
theorem sub3224 (p : Pattern) : d735 (change p 160 (some 159)) = d1854 p := by
  change (if p 113 then d705 (change p 160 (some 159)) else d706 (change p 160 (some 159))) = d1854 p
  rw [sub3194, sub3195]
  rfl
theorem sub3225 (p : Pattern) : d736 (change p 160 (some 159)) = d1855 p := by
  change (if p 112 then d735 (change p 160 (some 159)) else d720 (change p 160 (some 159))) = d1855 p
  rw [sub3224, sub3209]
  rfl
theorem sub3226 (p : Pattern) : d737 (change p 160 (some 159)) = d1856 p := by
  change (if p 113 then d715 (change p 160 (some 159)) else d710 (change p 160 (some 159))) = d1856 p
  rw [sub3204, sub3199]
  rfl
theorem sub3227 (p : Pattern) : d738 (change p 160 (some 159)) = d1857 p := by
  change (if p 113 then d2 (change p 160 (some 159)) else d728 (change p 160 (some 159))) = d1857 p
  rw [sub3181, sub3217]
  rfl
theorem sub3228 (p : Pattern) : d739 (change p 160 (some 159)) = d1858 p := by
  change (if p 112 then d738 (change p 160 (some 159)) else d737 (change p 160 (some 159))) = d1858 p
  rw [sub3227, sub3226]
  rfl
theorem sub3229 (p : Pattern) : d740 (change p 160 (some 159)) = d1859 p := by
  change (if p 106 then d739 (change p 160 (some 159)) else d736 (change p 160 (some 159))) = d1859 p
  rw [sub3228, sub3225]
  rfl
theorem sub3230 (p : Pattern) : d741 (change p 160 (some 159)) = d1860 p := by
  change (if p 86 then d740 (change p 160 (some 159)) else d734 (change p 160 (some 159))) = d1860 p
  rw [sub3229, sub3223]
  rfl
theorem sub3231 (p : Pattern) : d742 (change p 160 (some 159)) = d1861 p := by
  change (if p 80 then d741 (change p 160 (some 159)) else d732 (change p 160 (some 159))) = d1861 p
  rw [sub3230, sub3221]
  rfl
theorem sub3232 (p : Pattern) : d0 (change p 161 (some 160)) = d0 p := by
  rfl
theorem sub3233 (p : Pattern) : d3 (change p 161 (some 160)) = d0 p := by
  change d0 (change p 161 (some 160)) = d0 p
  exact sub3232 p
theorem sub3234 (p : Pattern) : d2 (change p 161 (some 160)) = d2 p := by
  rfl
theorem sub3235 (p : Pattern) : d17 (change p 161 (some 160)) = d2 p := by
  change d2 (change p 161 (some 160)) = d2 p
  exact sub3234 p
theorem sub3236 (p : Pattern) : d743 (change p 161 (some 160)) = d1554 p := by
  change (if p 159 then d17 (change p 161 (some 160)) else d3 (change p 161 (some 160))) = d1554 p
  rw [sub3235, sub3233]
  rfl
theorem sub3237 (p : Pattern) : d744 (change p 161 (some 160)) = d1554 p := by
  change (if p 159 then d2 (change p 161 (some 160)) else d3 (change p 161 (some 160))) = d1554 p
  rw [sub3234, sub3233]
  rfl
theorem sub3238 (p : Pattern) : d745 (change p 161 (some 160)) = d1554 p := by
  change (if p 158 then d744 (change p 161 (some 160)) else d743 (change p 161 (some 160))) = d1554 p
  rw [sub3237, sub3236]
  simp only [ite_self]
theorem sub3239 (p : Pattern) : d1 (change p 161 (some 160)) = d1 p := by
  rfl
end NetHack.Sokoban32Refined
