/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3000 (p : Pattern) : d619 (change p 158 none) = d1666 p := by
  change (if p 133 then d586 (change p 158 none) else d576 (change p 158 none)) = d1666 p
  rw [sub2967, sub2957]
  rfl
theorem sub3001 (p : Pattern) : d620 (change p 158 none) = d1667 p := by
  change (if p 133 then d2 (change p 158 none) else d586 (change p 158 none)) = d1667 p
  rw [sub2902, sub2967]
  rfl
theorem sub3002 (p : Pattern) : d621 (change p 158 none) = d1668 p := by
  change (if p 132 then d620 (change p 158 none) else d619 (change p 158 none)) = d1668 p
  rw [sub3001, sub3000]
  rfl
theorem sub3003 (p : Pattern) : d622 (change p 158 none) = d1669 p := by
  change (if p 113 then d621 (change p 158 none) else d618 (change p 158 none)) = d1669 p
  rw [sub3002, sub2999]
  rfl
theorem sub3004 (p : Pattern) : d623 (change p 158 none) = d1670 p := by
  change (if p 112 then d622 (change p 158 none) else d616 (change p 158 none)) = d1670 p
  rw [sub3003, sub2997]
  rfl
theorem sub3005 (p : Pattern) : d624 (change p 158 none) = d1671 p := by
  change (if p 106 then d623 (change p 158 none) else d611 (change p 158 none)) = d1671 p
  rw [sub3004, sub2992]
  rfl
theorem sub3006 (p : Pattern) : d625 (change p 158 none) = d1672 p := by
  change (if p 86 then d624 (change p 158 none) else d596 (change p 158 none)) = d1672 p
  rw [sub3005, sub2977]
  rfl
theorem sub3007 (p : Pattern) : d626 (change p 158 none) = d1610 p := by
  change (if p 134 then d553 (change p 158 none) else d584 (change p 158 none)) = d1610 p
  rw [sub2934, sub2965]
  rfl
theorem sub3008 (p : Pattern) : d627 (change p 158 none) = d1611 p := by
  change (if p 133 then d549 (change p 158 none) else d626 (change p 158 none)) = d1611 p
  rw [sub2927, sub3007]
  rfl
theorem sub3009 (p : Pattern) : d628 (change p 158 none) = d1612 p := by
  change (if p 132 then d627 (change p 158 none) else d550 (change p 158 none)) = d1612 p
  rw [sub3008, sub2928]
  rfl
theorem sub3010 (p : Pattern) : d629 (change p 158 none) = d1612 p := by
  change (if p 113 then d628 (change p 158 none) else d556 (change p 158 none)) = d1612 p
  rw [sub3009, sub2937]
  simp only [ite_self]
theorem sub3011 (p : Pattern) : d630 (change p 158 none) = d1630 p := by
  change (if p 112 then d573 (change p 158 none) else d629 (change p 158 none)) = d1630 p
  rw [sub2954, sub3010]
  rfl
theorem sub3012 (p : Pattern) : d631 (change p 158 none) = d1603 p := by
  change (if p 134 then d543 (change p 158 none) else d584 (change p 158 none)) = d1603 p
  rw [sub2917, sub2965]
  simp only [ite_self]
theorem sub3013 (p : Pattern) : d632 (change p 158 none) = d1607 p := by
  change (if p 133 then d549 (change p 158 none) else d631 (change p 158 none)) = d1607 p
  rw [sub2927, sub3012]
  rfl
theorem sub3014 (p : Pattern) : d633 (change p 158 none) = d1639 p := by
  change (if p 133 then d586 (change p 158 none) else d549 (change p 158 none)) = d1639 p
  rw [sub2967, sub2927]
  rfl
theorem sub3015 (p : Pattern) : d634 (change p 158 none) = d1640 p := by
  change (if p 132 then d633 (change p 158 none) else d632 (change p 158 none)) = d1640 p
  rw [sub3014, sub3013]
  rfl
theorem sub3016 (p : Pattern) : d635 (change p 158 none) = d1640 p := by
  change (if p 113 then d634 (change p 158 none) else d588 (change p 158 none)) = d1640 p
  rw [sub3015, sub2969]
  simp only [ite_self]
theorem sub3017 (p : Pattern) : d636 (change p 158 none) = d1673 p := by
  change (if p 112 then d594 (change p 158 none) else d635 (change p 158 none)) = d1673 p
  rw [sub2975, sub3016]
  rfl
theorem sub3018 (p : Pattern) : d637 (change p 158 none) = d1674 p := by
  change (if p 106 then d636 (change p 158 none) else d630 (change p 158 none)) = d1674 p
  rw [sub3017, sub3011]
  rfl
theorem sub3019 (p : Pattern) : d638 (change p 158 none) = d1675 p := by
  change (if p 139 then d545 (change p 158 none) else d551 (change p 158 none)) = d1675 p
  rw [sub2921, sub2932]
  rfl
theorem sub3020 (p : Pattern) : d639 (change p 158 none) = d1676 p := by
  change (if p 138 then d568 (change p 158 none) else d638 (change p 158 none)) = d1676 p
  rw [sub2949, sub3019]
  rfl
theorem sub3021 (p : Pattern) : d640 (change p 158 none) = d1677 p := by
  change (if p 134 then d639 (change p 158 none) else d598 (change p 158 none)) = d1677 p
  rw [sub3020, sub2979]
  rfl
theorem sub3022 (p : Pattern) : d641 (change p 158 none) = d1678 p := by
  change (if p 133 then d601 (change p 158 none) else d640 (change p 158 none)) = d1678 p
  rw [sub2982, sub3021]
  rfl
theorem sub3023 (p : Pattern) : d642 (change p 158 none) = d1679 p := by
  change (if p 132 then d641 (change p 158 none) else d613 (change p 158 none)) = d1679 p
  rw [sub3022, sub2994]
  rfl
theorem sub3024 (p : Pattern) : d643 (change p 158 none) = d1680 p := by
  change (if p 113 then d642 (change p 158 none) else d628 (change p 158 none)) = d1680 p
  rw [sub3023, sub3009]
  rfl
theorem sub3025 (p : Pattern) : d644 (change p 158 none) = d1681 p := by
  change (if p 132 then d586 (change p 158 none) else d619 (change p 158 none)) = d1681 p
  rw [sub2967, sub3000]
  rfl
theorem sub3026 (p : Pattern) : d645 (change p 158 none) = d1682 p := by
  change (if p 113 then d644 (change p 158 none) else d610 (change p 158 none)) = d1682 p
  rw [sub3025, sub2991]
  rfl
theorem sub3027 (p : Pattern) : d646 (change p 158 none) = d1683 p := by
  change (if p 112 then d645 (change p 158 none) else d643 (change p 158 none)) = d1683 p
  rw [sub3026, sub3024]
  rfl
theorem sub3028 (p : Pattern) : d647 (change p 158 none) = d1684 p := by
  change (if p 113 then d593 (change p 158 none) else d634 (change p 158 none)) = d1684 p
  rw [sub2974, sub3015]
  rfl
theorem sub3029 (p : Pattern) : d648 (change p 158 none) = d1685 p := by
  change (if p 113 then d2 (change p 158 none) else d621 (change p 158 none)) = d1685 p
  rw [sub2902, sub3002]
  rfl
theorem sub3030 (p : Pattern) : d649 (change p 158 none) = d1686 p := by
  change (if p 112 then d648 (change p 158 none) else d647 (change p 158 none)) = d1686 p
  rw [sub3029, sub3028]
  rfl
theorem sub3031 (p : Pattern) : d650 (change p 158 none) = d1687 p := by
  change (if p 106 then d649 (change p 158 none) else d646 (change p 158 none)) = d1687 p
  rw [sub3030, sub3027]
  rfl
theorem sub3032 (p : Pattern) : d651 (change p 158 none) = d1688 p := by
  change (if p 86 then d650 (change p 158 none) else d637 (change p 158 none)) = d1688 p
  rw [sub3031, sub3018]
  rfl
theorem sub3033 (p : Pattern) : d652 (change p 158 none) = d1689 p := by
  change (if p 80 then d651 (change p 158 none) else d625 (change p 158 none)) = d1689 p
  rw [sub3032, sub3006]
  rfl
theorem sub3034 (p : Pattern) : d0 (change p 161 none) = d0 p := by
  rfl
theorem sub3035 (p : Pattern) : d3 (change p 161 none) = d0 p := by
  change d0 (change p 161 none) = d0 p
  exact sub3034 p
theorem sub3036 (p : Pattern) : d2 (change p 161 none) = d2 p := by
  rfl
theorem sub3037 (p : Pattern) : d17 (change p 161 none) = d5 p := by
  change (if p 160 then d2 (change p 161 none) else d3 (change p 161 none)) = d5 p
  rw [sub3036, sub3035]
  rfl
theorem sub3038 (p : Pattern) : d743 (change p 161 none) = d1691 p := by
  change (if p 159 then d17 (change p 161 none) else d3 (change p 161 none)) = d1691 p
  rw [sub3037, sub3035]
  rfl
theorem sub3039 (p : Pattern) : d744 (change p 161 none) = d1554 p := by
  change (if p 159 then d2 (change p 161 none) else d3 (change p 161 none)) = d1554 p
  rw [sub3036, sub3035]
  rfl
theorem sub3040 (p : Pattern) : d745 (change p 161 none) = d1692 p := by
  change (if p 158 then d744 (change p 161 none) else d743 (change p 161 none)) = d1692 p
  rw [sub3039, sub3038]
  rfl
theorem sub3041 (p : Pattern) : d1 (change p 161 none) = d1 p := by
  rfl
theorem sub3042 (p : Pattern) : d9 (change p 161 none) = d1 p := by
  change d1 (change p 161 none) = d1 p
  exact sub3041 p
theorem sub3043 (p : Pattern) : d21 (change p 161 none) = d11 p := by
  change (if p 160 then d2 (change p 161 none) else d9 (change p 161 none)) = d11 p
  rw [sub3036, sub3042]
  rfl
theorem sub3044 (p : Pattern) : d746 (change p 161 none) = d1693 p := by
  change (if p 159 then d21 (change p 161 none) else d9 (change p 161 none)) = d1693 p
  rw [sub3043, sub3042]
  rfl
theorem sub3045 (p : Pattern) : d747 (change p 161 none) = d1556 p := by
  change (if p 159 then d2 (change p 161 none) else d9 (change p 161 none)) = d1556 p
  rw [sub3036, sub3042]
  rfl
theorem sub3046 (p : Pattern) : d748 (change p 161 none) = d1694 p := by
  change (if p 158 then d747 (change p 161 none) else d746 (change p 161 none)) = d1694 p
  rw [sub3045, sub3044]
  rfl
theorem sub3047 (p : Pattern) : d749 (change p 161 none) = d1695 p := by
  change (if p 139 then d748 (change p 161 none) else d745 (change p 161 none)) = d1695 p
  rw [sub3046, sub3040]
  rfl
theorem sub3048 (p : Pattern) : d750 (change p 161 none) = d1696 p := by
  change (if p 138 then d749 (change p 161 none) else d745 (change p 161 none)) = d1696 p
  rw [sub3047, sub3040]
  rfl
theorem sub3049 (p : Pattern) : d19 (change p 161 none) = d37 p := by
  change (if p 159 then d2 (change p 161 none) else d17 (change p 161 none)) = d37 p
  rw [sub3036, sub3037]
  rfl
theorem sub3050 (p : Pattern) : d751 (change p 161 none) = d1697 p := by
  change (if p 158 then d19 (change p 161 none) else d743 (change p 161 none)) = d1697 p
  rw [sub3049, sub3038]
  rfl
theorem sub3051 (p : Pattern) : d23 (change p 161 none) = d39 p := by
  change (if p 159 then d2 (change p 161 none) else d21 (change p 161 none)) = d39 p
  rw [sub3036, sub3043]
  rfl
theorem sub3052 (p : Pattern) : d752 (change p 161 none) = d1698 p := by
  change (if p 158 then d23 (change p 161 none) else d746 (change p 161 none)) = d1698 p
  rw [sub3051, sub3044]
  rfl
theorem sub3053 (p : Pattern) : d753 (change p 161 none) = d1699 p := by
  change (if p 139 then d752 (change p 161 none) else d751 (change p 161 none)) = d1699 p
  rw [sub3052, sub3050]
  rfl
theorem sub3054 (p : Pattern) : d754 (change p 161 none) = d1700 p := by
  change (if p 138 then d753 (change p 161 none) else d751 (change p 161 none)) = d1700 p
  rw [sub3053, sub3050]
  rfl
theorem sub3055 (p : Pattern) : d755 (change p 161 none) = d1701 p := by
  change (if p 134 then d754 (change p 161 none) else d750 (change p 161 none)) = d1701 p
  rw [sub3054, sub3048]
  rfl
theorem sub3056 (p : Pattern) : d756 (change p 161 none) = d1702 p := by
  change (if p 133 then d755 (change p 161 none) else d750 (change p 161 none)) = d1702 p
  rw [sub3055, sub3048]
  rfl
theorem sub3057 (p : Pattern) : d757 (change p 161 none) = d1703 p := by
  change (if p 133 then d754 (change p 161 none) else d755 (change p 161 none)) = d1703 p
  rw [sub3054, sub3055]
  rfl
theorem sub3058 (p : Pattern) : d758 (change p 161 none) = d1704 p := by
  change (if p 132 then d757 (change p 161 none) else d756 (change p 161 none)) = d1704 p
  rw [sub3057, sub3056]
  rfl
theorem sub3059 (p : Pattern) : d759 (change p 161 none) = d1705 p := by
  change (if p 134 then d753 (change p 161 none) else d749 (change p 161 none)) = d1705 p
  rw [sub3053, sub3047]
  rfl
theorem sub3060 (p : Pattern) : d760 (change p 161 none) = d1706 p := by
  change (if p 133 then d759 (change p 161 none) else d749 (change p 161 none)) = d1706 p
  rw [sub3059, sub3047]
  rfl
theorem sub3061 (p : Pattern) : d761 (change p 161 none) = d1707 p := by
  change (if p 133 then d753 (change p 161 none) else d759 (change p 161 none)) = d1707 p
  rw [sub3053, sub3059]
  rfl
theorem sub3062 (p : Pattern) : d762 (change p 161 none) = d1708 p := by
  change (if p 132 then d761 (change p 161 none) else d760 (change p 161 none)) = d1708 p
  rw [sub3061, sub3060]
  rfl
theorem sub3063 (p : Pattern) : d763 (change p 161 none) = d1709 p := by
  change (if p 139 then d2 (change p 161 none) else d745 (change p 161 none)) = d1709 p
  rw [sub3036, sub3040]
  rfl
theorem sub3064 (p : Pattern) : d764 (change p 161 none) = d1710 p := by
  change (if p 138 then d763 (change p 161 none) else d749 (change p 161 none)) = d1710 p
  rw [sub3063, sub3047]
  rfl
theorem sub3065 (p : Pattern) : d765 (change p 161 none) = d1711 p := by
  change (if p 139 then d2 (change p 161 none) else d751 (change p 161 none)) = d1711 p
  rw [sub3036, sub3050]
  rfl
theorem sub3066 (p : Pattern) : d766 (change p 161 none) = d1712 p := by
  change (if p 138 then d765 (change p 161 none) else d753 (change p 161 none)) = d1712 p
  rw [sub3065, sub3053]
  rfl
theorem sub3067 (p : Pattern) : d767 (change p 161 none) = d1713 p := by
  change (if p 134 then d766 (change p 161 none) else d764 (change p 161 none)) = d1713 p
  rw [sub3066, sub3064]
  rfl
theorem sub3068 (p : Pattern) : d768 (change p 161 none) = d1714 p := by
  change (if p 133 then d767 (change p 161 none) else d764 (change p 161 none)) = d1714 p
  rw [sub3067, sub3064]
  rfl
theorem sub3069 (p : Pattern) : d769 (change p 161 none) = d1715 p := by
  change (if p 133 then d766 (change p 161 none) else d767 (change p 161 none)) = d1715 p
  rw [sub3066, sub3067]
  rfl
theorem sub3070 (p : Pattern) : d770 (change p 161 none) = d1716 p := by
  change (if p 132 then d769 (change p 161 none) else d768 (change p 161 none)) = d1716 p
  rw [sub3069, sub3068]
  rfl
theorem sub3071 (p : Pattern) : d771 (change p 161 none) = d1717 p := by
  change (if p 113 then d770 (change p 161 none) else d762 (change p 161 none)) = d1717 p
  rw [sub3070, sub3062]
  rfl
theorem sub3072 (p : Pattern) : d772 (change p 161 none) = d1718 p := by
  change (if p 112 then d771 (change p 161 none) else d758 (change p 161 none)) = d1718 p
  rw [sub3071, sub3058]
  rfl
theorem sub3073 (p : Pattern) : d773 (change p 161 none) = d1719 p := by
  change (if p 139 then d2 (change p 161 none) else d752 (change p 161 none)) = d1719 p
  rw [sub3036, sub3052]
  rfl
theorem sub3074 (p : Pattern) : d774 (change p 161 none) = d1720 p := by
  change (if p 138 then d773 (change p 161 none) else d752 (change p 161 none)) = d1720 p
  rw [sub3073, sub3052]
  rfl
theorem sub3075 (p : Pattern) : d775 (change p 161 none) = d1721 p := by
  change (if p 133 then d774 (change p 161 none) else d755 (change p 161 none)) = d1721 p
  rw [sub3074, sub3055]
  rfl
theorem sub3076 (p : Pattern) : d776 (change p 161 none) = d1722 p := by
  change (if p 132 then d775 (change p 161 none) else d756 (change p 161 none)) = d1722 p
  rw [sub3075, sub3056]
  rfl
theorem sub3077 (p : Pattern) : d777 (change p 161 none) = d1723 p := by
  change (if p 133 then d773 (change p 161 none) else d755 (change p 161 none)) = d1723 p
  rw [sub3073, sub3055]
  rfl
theorem sub3078 (p : Pattern) : d778 (change p 161 none) = d1724 p := by
  change (if p 132 then d777 (change p 161 none) else d756 (change p 161 none)) = d1724 p
  rw [sub3077, sub3056]
  rfl
theorem sub3079 (p : Pattern) : d779 (change p 161 none) = d1725 p := by
  change (if p 113 then d778 (change p 161 none) else d776 (change p 161 none)) = d1725 p
  rw [sub3078, sub3076]
  rfl
theorem sub3080 (p : Pattern) : d780 (change p 161 none) = d1726 p := by
  change (if p 133 then d773 (change p 161 none) else d759 (change p 161 none)) = d1726 p
  rw [sub3073, sub3059]
  rfl
theorem sub3081 (p : Pattern) : d781 (change p 161 none) = d1727 p := by
  change (if p 132 then d780 (change p 161 none) else d760 (change p 161 none)) = d1727 p
  rw [sub3080, sub3060]
  rfl
theorem sub3082 (p : Pattern) : d782 (change p 161 none) = d1728 p := by
  change (if p 133 then d773 (change p 161 none) else d767 (change p 161 none)) = d1728 p
  rw [sub3073, sub3067]
  rfl
theorem sub3083 (p : Pattern) : d783 (change p 161 none) = d1729 p := by
  change (if p 132 then d782 (change p 161 none) else d768 (change p 161 none)) = d1729 p
  rw [sub3082, sub3068]
  rfl
theorem sub3084 (p : Pattern) : d784 (change p 161 none) = d1730 p := by
  change (if p 113 then d783 (change p 161 none) else d781 (change p 161 none)) = d1730 p
  rw [sub3083, sub3081]
  rfl
theorem sub3085 (p : Pattern) : d785 (change p 161 none) = d1731 p := by
  change (if p 112 then d784 (change p 161 none) else d779 (change p 161 none)) = d1731 p
  rw [sub3084, sub3079]
  rfl
theorem sub3086 (p : Pattern) : d786 (change p 161 none) = d1732 p := by
  change (if p 106 then d785 (change p 161 none) else d772 (change p 161 none)) = d1732 p
  rw [sub3085, sub3072]
  rfl
theorem sub3087 (p : Pattern) : d787 (change p 161 none) = d1733 p := by
  change (if p 138 then d763 (change p 161 none) else d745 (change p 161 none)) = d1733 p
  rw [sub3063, sub3040]
  rfl
theorem sub3088 (p : Pattern) : d788 (change p 161 none) = d1734 p := by
  change (if p 138 then d765 (change p 161 none) else d751 (change p 161 none)) = d1734 p
  rw [sub3065, sub3050]
  rfl
theorem sub3089 (p : Pattern) : d789 (change p 161 none) = d1735 p := by
  change (if p 134 then d788 (change p 161 none) else d787 (change p 161 none)) = d1735 p
  rw [sub3088, sub3087]
  rfl
theorem sub3090 (p : Pattern) : d790 (change p 161 none) = d1736 p := by
  change (if p 133 then d789 (change p 161 none) else d787 (change p 161 none)) = d1736 p
  rw [sub3089, sub3087]
  rfl
theorem sub3091 (p : Pattern) : d791 (change p 161 none) = d1737 p := by
  change (if p 133 then d788 (change p 161 none) else d789 (change p 161 none)) = d1737 p
  rw [sub3088, sub3089]
  rfl
theorem sub3092 (p : Pattern) : d792 (change p 161 none) = d1738 p := by
  change (if p 132 then d791 (change p 161 none) else d790 (change p 161 none)) = d1738 p
  rw [sub3091, sub3090]
  rfl
theorem sub3093 (p : Pattern) : d793 (change p 161 none) = d1739 p := by
  change (if p 113 then d792 (change p 161 none) else d758 (change p 161 none)) = d1739 p
  rw [sub3092, sub3058]
  rfl
theorem sub3094 (p : Pattern) : d794 (change p 161 none) = d1740 p := by
  change (if p 139 then d2 (change p 161 none) else d748 (change p 161 none)) = d1740 p
  rw [sub3036, sub3046]
  rfl
theorem sub3095 (p : Pattern) : d795 (change p 161 none) = d1741 p := by
  change (if p 138 then d794 (change p 161 none) else d748 (change p 161 none)) = d1741 p
  rw [sub3094, sub3046]
  rfl
theorem sub3096 (p : Pattern) : d796 (change p 161 none) = d1742 p := by
  change (if p 134 then d774 (change p 161 none) else d795 (change p 161 none)) = d1742 p
  rw [sub3074, sub3095]
  rfl
theorem sub3097 (p : Pattern) : d797 (change p 161 none) = d1743 p := by
  change (if p 133 then d796 (change p 161 none) else d795 (change p 161 none)) = d1743 p
  rw [sub3096, sub3095]
  rfl
theorem sub3098 (p : Pattern) : d798 (change p 161 none) = d1744 p := by
  change (if p 133 then d774 (change p 161 none) else d796 (change p 161 none)) = d1744 p
  rw [sub3074, sub3096]
  rfl
theorem sub3099 (p : Pattern) : d799 (change p 161 none) = d1745 p := by
  change (if p 132 then d798 (change p 161 none) else d797 (change p 161 none)) = d1745 p
  rw [sub3098, sub3097]
  rfl
theorem sub3100 (p : Pattern) : d800 (change p 161 none) = d1746 p := by
  change (if p 112 then d799 (change p 161 none) else d793 (change p 161 none)) = d1746 p
  rw [sub3099, sub3093]
  rfl
theorem sub3101 (p : Pattern) : d801 (change p 161 none) = d1747 p := by
  change (if p 133 then d773 (change p 161 none) else d789 (change p 161 none)) = d1747 p
  rw [sub3073, sub3089]
  rfl
theorem sub3102 (p : Pattern) : d802 (change p 161 none) = d1748 p := by
  change (if p 132 then d801 (change p 161 none) else d790 (change p 161 none)) = d1748 p
  rw [sub3101, sub3090]
  rfl
theorem sub3103 (p : Pattern) : d803 (change p 161 none) = d1749 p := by
  change (if p 113 then d802 (change p 161 none) else d778 (change p 161 none)) = d1749 p
  rw [sub3102, sub3078]
  rfl
theorem sub3104 (p : Pattern) : d804 (change p 161 none) = d1750 p := by
  change (if p 133 then d2 (change p 161 none) else d796 (change p 161 none)) = d1750 p
  rw [sub3036, sub3096]
  rfl
theorem sub3105 (p : Pattern) : d805 (change p 161 none) = d1751 p := by
  change (if p 132 then d804 (change p 161 none) else d797 (change p 161 none)) = d1751 p
  rw [sub3104, sub3097]
  rfl
theorem sub3106 (p : Pattern) : d806 (change p 161 none) = d1752 p := by
  change (if p 134 then d773 (change p 161 none) else d794 (change p 161 none)) = d1752 p
  rw [sub3073, sub3094]
  rfl
theorem sub3107 (p : Pattern) : d807 (change p 161 none) = d1753 p := by
  change (if p 133 then d806 (change p 161 none) else d794 (change p 161 none)) = d1753 p
  rw [sub3106, sub3094]
  rfl
theorem sub3108 (p : Pattern) : d808 (change p 161 none) = d1754 p := by
  change (if p 133 then d2 (change p 161 none) else d806 (change p 161 none)) = d1754 p
  rw [sub3036, sub3106]
  rfl
theorem sub3109 (p : Pattern) : d809 (change p 161 none) = d1755 p := by
  change (if p 132 then d808 (change p 161 none) else d807 (change p 161 none)) = d1755 p
  rw [sub3108, sub3107]
  rfl
theorem sub3110 (p : Pattern) : d810 (change p 161 none) = d1756 p := by
  change (if p 113 then d809 (change p 161 none) else d805 (change p 161 none)) = d1756 p
  rw [sub3109, sub3105]
  rfl
theorem sub3111 (p : Pattern) : d811 (change p 161 none) = d1757 p := by
  change (if p 112 then d810 (change p 161 none) else d803 (change p 161 none)) = d1757 p
  rw [sub3110, sub3103]
  rfl
theorem sub3112 (p : Pattern) : d812 (change p 161 none) = d1758 p := by
  change (if p 106 then d811 (change p 161 none) else d800 (change p 161 none)) = d1758 p
  rw [sub3111, sub3100]
  rfl
theorem sub3113 (p : Pattern) : d813 (change p 161 none) = d1759 p := by
  change (if p 86 then d812 (change p 161 none) else d786 (change p 161 none)) = d1759 p
  rw [sub3112, sub3086]
  rfl
theorem sub3114 (p : Pattern) : d814 (change p 161 none) = d1760 p := by
  change (if p 112 then d784 (change p 161 none) else d778 (change p 161 none)) = d1760 p
  rw [sub3084, sub3078]
  rfl
theorem sub3115 (p : Pattern) : d815 (change p 161 none) = d1761 p := by
  change (if p 106 then d814 (change p 161 none) else d772 (change p 161 none)) = d1761 p
  rw [sub3114, sub3072]
  rfl
theorem sub3116 (p : Pattern) : d816 (change p 161 none) = d1762 p := by
  change (if p 133 then d773 (change p 161 none) else d806 (change p 161 none)) = d1762 p
  rw [sub3073, sub3106]
  rfl
theorem sub3117 (p : Pattern) : d817 (change p 161 none) = d1763 p := by
  change (if p 132 then d816 (change p 161 none) else d807 (change p 161 none)) = d1763 p
  rw [sub3116, sub3107]
  rfl
theorem sub3118 (p : Pattern) : d818 (change p 161 none) = d1764 p := by
  change (if p 113 then d817 (change p 161 none) else d799 (change p 161 none)) = d1764 p
  rw [sub3117, sub3099]
  rfl
theorem sub3119 (p : Pattern) : d819 (change p 161 none) = d1765 p := by
  change (if p 112 then d818 (change p 161 none) else d793 (change p 161 none)) = d1765 p
  rw [sub3118, sub3093]
  rfl
end NetHack.Sokoban32Refined
