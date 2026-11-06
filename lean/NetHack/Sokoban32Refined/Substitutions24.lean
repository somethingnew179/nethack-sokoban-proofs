/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2880 (p : Pattern) : d722 (change p 160 (some 161)) = d1581 p := by
  change (if p 133 then d705 (change p 160 (some 161)) else d719 (change p 160 (some 161))) = d1581 p
  rw [sub2863, sub2877]
  rfl
theorem sub2881 (p : Pattern) : d723 (change p 160 (some 161)) = d1582 p := by
  change (if p 132 then d722 (change p 160 (some 161)) else d719 (change p 160 (some 161))) = d1582 p
  rw [sub2880, sub2877]
  rfl
theorem sub2882 (p : Pattern) : d724 (change p 160 (some 161)) = d1583 p := by
  change (if p 113 then d723 (change p 160 (some 161)) else d710 (change p 160 (some 161))) = d1583 p
  rw [sub2881, sub2868]
  rfl
theorem sub2883 (p : Pattern) : d725 (change p 160 (some 161)) = d1584 p := by
  change (if p 133 then d2 (change p 160 (some 161)) else d706 (change p 160 (some 161))) = d1584 p
  rw [sub2850, sub2864]
  rfl
theorem sub2884 (p : Pattern) : d726 (change p 160 (some 161)) = d1585 p := by
  change (if p 132 then d725 (change p 160 (some 161)) else d706 (change p 160 (some 161))) = d1585 p
  rw [sub2883, sub2864]
  rfl
theorem sub2885 (p : Pattern) : d727 (change p 160 (some 161)) = d1586 p := by
  change (if p 133 then d2 (change p 160 (some 161)) else d705 (change p 160 (some 161))) = d1586 p
  rw [sub2850, sub2863]
  rfl
theorem sub2886 (p : Pattern) : d728 (change p 160 (some 161)) = d1587 p := by
  change (if p 132 then d727 (change p 160 (some 161)) else d705 (change p 160 (some 161))) = d1587 p
  rw [sub2885, sub2863]
  rfl
theorem sub2887 (p : Pattern) : d729 (change p 160 (some 161)) = d1588 p := by
  change (if p 113 then d728 (change p 160 (some 161)) else d726 (change p 160 (some 161))) = d1588 p
  rw [sub2886, sub2884]
  rfl
theorem sub2888 (p : Pattern) : d730 (change p 160 (some 161)) = d1589 p := by
  change (if p 112 then d729 (change p 160 (some 161)) else d724 (change p 160 (some 161))) = d1589 p
  rw [sub2887, sub2882]
  rfl
theorem sub2889 (p : Pattern) : d731 (change p 160 (some 161)) = d1590 p := by
  change (if p 106 then d730 (change p 160 (some 161)) else d721 (change p 160 (some 161))) = d1590 p
  rw [sub2888, sub2879]
  rfl
theorem sub2890 (p : Pattern) : d732 (change p 160 (some 161)) = d1591 p := by
  change (if p 86 then d731 (change p 160 (some 161)) else d718 (change p 160 (some 161))) = d1591 p
  rw [sub2889, sub2876]
  rfl
theorem sub2891 (p : Pattern) : d733 (change p 160 (some 161)) = d1592 p := by
  change (if p 112 then d716 (change p 160 (some 161)) else d710 (change p 160 (some 161))) = d1592 p
  rw [sub2874, sub2868]
  rfl
theorem sub2892 (p : Pattern) : d734 (change p 160 (some 161)) = d1593 p := by
  change (if p 106 then d733 (change p 160 (some 161)) else d704 (change p 160 (some 161))) = d1593 p
  rw [sub2891, sub2862]
  rfl
theorem sub2893 (p : Pattern) : d735 (change p 160 (some 161)) = d1594 p := by
  change (if p 113 then d705 (change p 160 (some 161)) else d706 (change p 160 (some 161))) = d1594 p
  rw [sub2863, sub2864]
  rfl
theorem sub2894 (p : Pattern) : d736 (change p 160 (some 161)) = d1595 p := by
  change (if p 112 then d735 (change p 160 (some 161)) else d720 (change p 160 (some 161))) = d1595 p
  rw [sub2893, sub2878]
  rfl
theorem sub2895 (p : Pattern) : d737 (change p 160 (some 161)) = d1596 p := by
  change (if p 113 then d715 (change p 160 (some 161)) else d710 (change p 160 (some 161))) = d1596 p
  rw [sub2873, sub2868]
  rfl
theorem sub2896 (p : Pattern) : d738 (change p 160 (some 161)) = d1597 p := by
  change (if p 113 then d2 (change p 160 (some 161)) else d728 (change p 160 (some 161))) = d1597 p
  rw [sub2850, sub2886]
  rfl
theorem sub2897 (p : Pattern) : d739 (change p 160 (some 161)) = d1598 p := by
  change (if p 112 then d738 (change p 160 (some 161)) else d737 (change p 160 (some 161))) = d1598 p
  rw [sub2896, sub2895]
  rfl
theorem sub2898 (p : Pattern) : d740 (change p 160 (some 161)) = d1599 p := by
  change (if p 106 then d739 (change p 160 (some 161)) else d736 (change p 160 (some 161))) = d1599 p
  rw [sub2897, sub2894]
  rfl
theorem sub2899 (p : Pattern) : d741 (change p 160 (some 161)) = d1600 p := by
  change (if p 86 then d740 (change p 160 (some 161)) else d734 (change p 160 (some 161))) = d1600 p
  rw [sub2898, sub2892]
  rfl
theorem sub2900 (p : Pattern) : d742 (change p 160 (some 161)) = d1601 p := by
  change (if p 80 then d741 (change p 160 (some 161)) else d732 (change p 160 (some 161))) = d1601 p
  rw [sub2899, sub2890]
  rfl
theorem sub2901 (p : Pattern) : d0 (change p 158 none) = d0 p := by
  rfl
theorem sub2902 (p : Pattern) : d2 (change p 158 none) = d2 p := by
  rfl
theorem sub2903 (p : Pattern) : d3 (change p 158 none) = d3 p := by
  change (if p 161 then d2 (change p 158 none) else d0 (change p 158 none)) = d3 p
  rw [sub2902, sub2901]
  rfl
theorem sub2904 (p : Pattern) : d4 (change p 158 none) = d4 p := by
  change (if p 160 then d3 (change p 158 none) else d0 (change p 158 none)) = d4 p
  rw [sub2903, sub2901]
  rfl
theorem sub2905 (p : Pattern) : d5 (change p 158 none) = d5 p := by
  change (if p 160 then d2 (change p 158 none) else d0 (change p 158 none)) = d5 p
  rw [sub2902, sub2901]
  rfl
theorem sub2906 (p : Pattern) : d6 (change p 158 none) = d6 p := by
  change (if p 159 then d5 (change p 158 none) else d4 (change p 158 none)) = d6 p
  rw [sub2905, sub2904]
  rfl
theorem sub2907 (p : Pattern) : d538 (change p 158 none) = d6 p := by
  change d6 (change p 158 none) = d6 p
  exact sub2906 p
theorem sub2908 (p : Pattern) : d539 (change p 158 none) = d6 p := by
  change d6 (change p 158 none) = d6 p
  exact sub2906 p
theorem sub2909 (p : Pattern) : d1 (change p 158 none) = d1 p := by
  rfl
theorem sub2910 (p : Pattern) : d9 (change p 158 none) = d9 p := by
  change (if p 161 then d2 (change p 158 none) else d1 (change p 158 none)) = d9 p
  rw [sub2902, sub2909]
  rfl
theorem sub2911 (p : Pattern) : d10 (change p 158 none) = d10 p := by
  change (if p 160 then d9 (change p 158 none) else d1 (change p 158 none)) = d10 p
  rw [sub2910, sub2909]
  rfl
theorem sub2912 (p : Pattern) : d11 (change p 158 none) = d11 p := by
  change (if p 160 then d2 (change p 158 none) else d1 (change p 158 none)) = d11 p
  rw [sub2902, sub2909]
  rfl
theorem sub2913 (p : Pattern) : d12 (change p 158 none) = d12 p := by
  change (if p 159 then d11 (change p 158 none) else d10 (change p 158 none)) = d12 p
  rw [sub2912, sub2911]
  rfl
theorem sub2914 (p : Pattern) : d540 (change p 158 none) = d12 p := by
  change d12 (change p 158 none) = d12 p
  exact sub2913 p
theorem sub2915 (p : Pattern) : d541 (change p 158 none) = d1602 p := by
  change (if p 139 then d540 (change p 158 none) else d539 (change p 158 none)) = d1602 p
  rw [sub2914, sub2908]
  rfl
theorem sub2916 (p : Pattern) : d542 (change p 158 none) = d1603 p := by
  change (if p 138 then d541 (change p 158 none) else d538 (change p 158 none)) = d1603 p
  rw [sub2915, sub2907]
  rfl
theorem sub2917 (p : Pattern) : d543 (change p 158 none) = d1603 p := by
  change (if p 138 then d541 (change p 158 none) else d539 (change p 158 none)) = d1603 p
  rw [sub2915, sub2908]
  rfl
theorem sub2918 (p : Pattern) : d544 (change p 158 none) = d1603 p := by
  change (if p 134 then d543 (change p 158 none) else d542 (change p 158 none)) = d1603 p
  rw [sub2917, sub2916]
  simp only [ite_self]
theorem sub2919 (p : Pattern) : d17 (change p 158 none) = d17 p := by
  change (if p 160 then d2 (change p 158 none) else d3 (change p 158 none)) = d17 p
  rw [sub2902, sub2903]
  rfl
theorem sub2920 (p : Pattern) : d18 (change p 158 none) = d18 p := by
  change (if p 159 then d17 (change p 158 none) else d4 (change p 158 none)) = d18 p
  rw [sub2919, sub2904]
  rfl
theorem sub2921 (p : Pattern) : d545 (change p 158 none) = d18 p := by
  change d18 (change p 158 none) = d18 p
  exact sub2920 p
theorem sub2922 (p : Pattern) : d21 (change p 158 none) = d21 p := by
  change (if p 160 then d2 (change p 158 none) else d9 (change p 158 none)) = d21 p
  rw [sub2902, sub2910]
  rfl
theorem sub2923 (p : Pattern) : d22 (change p 158 none) = d22 p := by
  change (if p 159 then d21 (change p 158 none) else d10 (change p 158 none)) = d22 p
  rw [sub2922, sub2911]
  rfl
theorem sub2924 (p : Pattern) : d546 (change p 158 none) = d22 p := by
  change d22 (change p 158 none) = d22 p
  exact sub2923 p
theorem sub2925 (p : Pattern) : d547 (change p 158 none) = d1604 p := by
  change (if p 139 then d546 (change p 158 none) else d545 (change p 158 none)) = d1604 p
  rw [sub2924, sub2921]
  rfl
theorem sub2926 (p : Pattern) : d548 (change p 158 none) = d1605 p := by
  change (if p 138 then d547 (change p 158 none) else d545 (change p 158 none)) = d1605 p
  rw [sub2925, sub2921]
  rfl
theorem sub2927 (p : Pattern) : d549 (change p 158 none) = d1606 p := by
  change (if p 134 then d548 (change p 158 none) else d543 (change p 158 none)) = d1606 p
  rw [sub2926, sub2917]
  rfl
theorem sub2928 (p : Pattern) : d550 (change p 158 none) = d1607 p := by
  change (if p 133 then d549 (change p 158 none) else d544 (change p 158 none)) = d1607 p
  rw [sub2927, sub2918]
  rfl
theorem sub2929 (p : Pattern) : d29 (change p 158 none) = d29 p := by
  change (if p 161 then d1 (change p 158 none) else d0 (change p 158 none)) = d29 p
  rw [sub2909, sub2901]
  rfl
theorem sub2930 (p : Pattern) : d30 (change p 158 none) = d30 p := by
  change (if p 160 then d2 (change p 158 none) else d29 (change p 158 none)) = d30 p
  rw [sub2902, sub2929]
  rfl
theorem sub2931 (p : Pattern) : d31 (change p 158 none) = d31 p := by
  change (if p 159 then d30 (change p 158 none) else d4 (change p 158 none)) = d31 p
  rw [sub2930, sub2904]
  rfl
theorem sub2932 (p : Pattern) : d551 (change p 158 none) = d31 p := by
  change d31 (change p 158 none) = d31 p
  exact sub2931 p
theorem sub2933 (p : Pattern) : d552 (change p 158 none) = d1608 p := by
  change (if p 139 then d546 (change p 158 none) else d551 (change p 158 none)) = d1608 p
  rw [sub2924, sub2932]
  rfl
theorem sub2934 (p : Pattern) : d553 (change p 158 none) = d1609 p := by
  change (if p 138 then d552 (change p 158 none) else d551 (change p 158 none)) = d1609 p
  rw [sub2933, sub2932]
  rfl
theorem sub2935 (p : Pattern) : d554 (change p 158 none) = d1610 p := by
  change (if p 134 then d553 (change p 158 none) else d542 (change p 158 none)) = d1610 p
  rw [sub2934, sub2916]
  rfl
theorem sub2936 (p : Pattern) : d555 (change p 158 none) = d1611 p := by
  change (if p 133 then d549 (change p 158 none) else d554 (change p 158 none)) = d1611 p
  rw [sub2927, sub2935]
  rfl
theorem sub2937 (p : Pattern) : d556 (change p 158 none) = d1612 p := by
  change (if p 132 then d555 (change p 158 none) else d550 (change p 158 none)) = d1612 p
  rw [sub2936, sub2928]
  rfl
theorem sub2938 (p : Pattern) : d557 (change p 158 none) = d1613 p := by
  change (if p 134 then d547 (change p 158 none) else d541 (change p 158 none)) = d1613 p
  rw [sub2925, sub2915]
  rfl
theorem sub2939 (p : Pattern) : d558 (change p 158 none) = d1614 p := by
  change (if p 133 then d557 (change p 158 none) else d541 (change p 158 none)) = d1614 p
  rw [sub2938, sub2915]
  rfl
theorem sub2940 (p : Pattern) : d559 (change p 158 none) = d1615 p := by
  change (if p 134 then d552 (change p 158 none) else d541 (change p 158 none)) = d1615 p
  rw [sub2933, sub2915]
  rfl
theorem sub2941 (p : Pattern) : d560 (change p 158 none) = d1616 p := by
  change (if p 133 then d557 (change p 158 none) else d559 (change p 158 none)) = d1616 p
  rw [sub2938, sub2940]
  rfl
theorem sub2942 (p : Pattern) : d561 (change p 158 none) = d1617 p := by
  change (if p 132 then d560 (change p 158 none) else d558 (change p 158 none)) = d1617 p
  rw [sub2941, sub2939]
  rfl
theorem sub2943 (p : Pattern) : d562 (change p 158 none) = d1618 p := by
  change (if p 139 then d2 (change p 158 none) else d539 (change p 158 none)) = d1618 p
  rw [sub2902, sub2908]
  rfl
theorem sub2944 (p : Pattern) : d563 (change p 158 none) = d1619 p := by
  change (if p 138 then d562 (change p 158 none) else d541 (change p 158 none)) = d1619 p
  rw [sub2943, sub2915]
  rfl
theorem sub2945 (p : Pattern) : d564 (change p 158 none) = d1620 p := by
  change (if p 139 then d2 (change p 158 none) else d545 (change p 158 none)) = d1620 p
  rw [sub2902, sub2921]
  rfl
theorem sub2946 (p : Pattern) : d565 (change p 158 none) = d1621 p := by
  change (if p 138 then d564 (change p 158 none) else d547 (change p 158 none)) = d1621 p
  rw [sub2945, sub2925]
  rfl
theorem sub2947 (p : Pattern) : d566 (change p 158 none) = d1622 p := by
  change (if p 134 then d565 (change p 158 none) else d563 (change p 158 none)) = d1622 p
  rw [sub2946, sub2944]
  rfl
theorem sub2948 (p : Pattern) : d567 (change p 158 none) = d1623 p := by
  change (if p 133 then d566 (change p 158 none) else d563 (change p 158 none)) = d1623 p
  rw [sub2947, sub2944]
  rfl
theorem sub2949 (p : Pattern) : d568 (change p 158 none) = d1624 p := by
  change (if p 139 then d2 (change p 158 none) else d551 (change p 158 none)) = d1624 p
  rw [sub2902, sub2932]
  rfl
theorem sub2950 (p : Pattern) : d569 (change p 158 none) = d1625 p := by
  change (if p 138 then d568 (change p 158 none) else d552 (change p 158 none)) = d1625 p
  rw [sub2949, sub2933]
  rfl
theorem sub2951 (p : Pattern) : d570 (change p 158 none) = d1626 p := by
  change (if p 134 then d569 (change p 158 none) else d563 (change p 158 none)) = d1626 p
  rw [sub2950, sub2944]
  rfl
theorem sub2952 (p : Pattern) : d571 (change p 158 none) = d1627 p := by
  change (if p 133 then d566 (change p 158 none) else d570 (change p 158 none)) = d1627 p
  rw [sub2947, sub2951]
  rfl
theorem sub2953 (p : Pattern) : d572 (change p 158 none) = d1628 p := by
  change (if p 132 then d571 (change p 158 none) else d567 (change p 158 none)) = d1628 p
  rw [sub2952, sub2948]
  rfl
theorem sub2954 (p : Pattern) : d573 (change p 158 none) = d1629 p := by
  change (if p 113 then d572 (change p 158 none) else d561 (change p 158 none)) = d1629 p
  rw [sub2953, sub2942]
  rfl
theorem sub2955 (p : Pattern) : d574 (change p 158 none) = d1630 p := by
  change (if p 112 then d573 (change p 158 none) else d556 (change p 158 none)) = d1630 p
  rw [sub2954, sub2937]
  rfl
theorem sub2956 (p : Pattern) : d575 (change p 158 none) = d1606 p := by
  change (if p 134 then d548 (change p 158 none) else d542 (change p 158 none)) = d1606 p
  rw [sub2926, sub2916]
  rfl
theorem sub2957 (p : Pattern) : d576 (change p 158 none) = d1631 p := by
  change (if p 139 then d2 (change p 158 none) else d540 (change p 158 none)) = d1631 p
  rw [sub2902, sub2914]
  rfl
theorem sub2958 (p : Pattern) : d577 (change p 158 none) = d1632 p := by
  change (if p 138 then d576 (change p 158 none) else d540 (change p 158 none)) = d1632 p
  rw [sub2957, sub2914]
  rfl
theorem sub2959 (p : Pattern) : d578 (change p 158 none) = d1633 p := by
  change (if p 139 then d2 (change p 158 none) else d546 (change p 158 none)) = d1633 p
  rw [sub2902, sub2924]
  rfl
theorem sub2960 (p : Pattern) : d579 (change p 158 none) = d1634 p := by
  change (if p 138 then d578 (change p 158 none) else d546 (change p 158 none)) = d1634 p
  rw [sub2959, sub2924]
  rfl
theorem sub2961 (p : Pattern) : d580 (change p 158 none) = d1635 p := by
  change (if p 134 then d579 (change p 158 none) else d577 (change p 158 none)) = d1635 p
  rw [sub2960, sub2958]
  rfl
theorem sub2962 (p : Pattern) : d581 (change p 158 none) = d1636 p := by
  change (if p 133 then d580 (change p 158 none) else d575 (change p 158 none)) = d1636 p
  rw [sub2961, sub2956]
  rfl
theorem sub2963 (p : Pattern) : d582 (change p 158 none) = d1637 p := by
  change (if p 132 then d581 (change p 158 none) else d550 (change p 158 none)) = d1637 p
  rw [sub2962, sub2928]
  rfl
theorem sub2964 (p : Pattern) : d583 (change p 158 none) = d6 p := by
  change (if p 139 then d539 (change p 158 none) else d538 (change p 158 none)) = d6 p
  rw [sub2908, sub2907]
  simp only [ite_self]
theorem sub2965 (p : Pattern) : d584 (change p 158 none) = d1603 p := by
  change (if p 138 then d541 (change p 158 none) else d583 (change p 158 none)) = d1603 p
  rw [sub2915, sub2964]
  rfl
theorem sub2966 (p : Pattern) : d585 (change p 158 none) = d1606 p := by
  change (if p 134 then d548 (change p 158 none) else d584 (change p 158 none)) = d1606 p
  rw [sub2926, sub2965]
  rfl
theorem sub2967 (p : Pattern) : d586 (change p 158 none) = d1638 p := by
  change (if p 134 then d578 (change p 158 none) else d576 (change p 158 none)) = d1638 p
  rw [sub2959, sub2957]
  rfl
theorem sub2968 (p : Pattern) : d587 (change p 158 none) = d1639 p := by
  change (if p 133 then d586 (change p 158 none) else d585 (change p 158 none)) = d1639 p
  rw [sub2967, sub2966]
  rfl
theorem sub2969 (p : Pattern) : d588 (change p 158 none) = d1640 p := by
  change (if p 132 then d587 (change p 158 none) else d550 (change p 158 none)) = d1640 p
  rw [sub2968, sub2928]
  rfl
theorem sub2970 (p : Pattern) : d589 (change p 158 none) = d1641 p := by
  change (if p 113 then d588 (change p 158 none) else d582 (change p 158 none)) = d1641 p
  rw [sub2969, sub2963]
  rfl
theorem sub2971 (p : Pattern) : d590 (change p 158 none) = d1642 p := by
  change (if p 133 then d586 (change p 158 none) else d557 (change p 158 none)) = d1642 p
  rw [sub2967, sub2938]
  rfl
theorem sub2972 (p : Pattern) : d591 (change p 158 none) = d1643 p := by
  change (if p 132 then d590 (change p 158 none) else d558 (change p 158 none)) = d1643 p
  rw [sub2971, sub2939]
  rfl
theorem sub2973 (p : Pattern) : d592 (change p 158 none) = d1644 p := by
  change (if p 133 then d586 (change p 158 none) else d566 (change p 158 none)) = d1644 p
  rw [sub2967, sub2947]
  rfl
theorem sub2974 (p : Pattern) : d593 (change p 158 none) = d1645 p := by
  change (if p 132 then d592 (change p 158 none) else d567 (change p 158 none)) = d1645 p
  rw [sub2973, sub2948]
  rfl
theorem sub2975 (p : Pattern) : d594 (change p 158 none) = d1646 p := by
  change (if p 113 then d593 (change p 158 none) else d591 (change p 158 none)) = d1646 p
  rw [sub2974, sub2972]
  rfl
theorem sub2976 (p : Pattern) : d595 (change p 158 none) = d1647 p := by
  change (if p 112 then d594 (change p 158 none) else d589 (change p 158 none)) = d1647 p
  rw [sub2975, sub2970]
  rfl
theorem sub2977 (p : Pattern) : d596 (change p 158 none) = d1648 p := by
  change (if p 106 then d595 (change p 158 none) else d574 (change p 158 none)) = d1648 p
  rw [sub2976, sub2955]
  rfl
theorem sub2978 (p : Pattern) : d597 (change p 158 none) = d1649 p := by
  change (if p 138 then d562 (change p 158 none) else d538 (change p 158 none)) = d1649 p
  rw [sub2943, sub2907]
  rfl
theorem sub2979 (p : Pattern) : d598 (change p 158 none) = d1649 p := by
  change (if p 138 then d562 (change p 158 none) else d539 (change p 158 none)) = d1649 p
  rw [sub2943, sub2908]
  rfl
theorem sub2980 (p : Pattern) : d599 (change p 158 none) = d1649 p := by
  change (if p 134 then d598 (change p 158 none) else d597 (change p 158 none)) = d1649 p
  rw [sub2979, sub2978]
  simp only [ite_self]
theorem sub2981 (p : Pattern) : d600 (change p 158 none) = d1650 p := by
  change (if p 138 then d564 (change p 158 none) else d545 (change p 158 none)) = d1650 p
  rw [sub2945, sub2921]
  rfl
theorem sub2982 (p : Pattern) : d601 (change p 158 none) = d1651 p := by
  change (if p 134 then d600 (change p 158 none) else d598 (change p 158 none)) = d1651 p
  rw [sub2981, sub2979]
  rfl
theorem sub2983 (p : Pattern) : d602 (change p 158 none) = d1652 p := by
  change (if p 133 then d601 (change p 158 none) else d599 (change p 158 none)) = d1652 p
  rw [sub2982, sub2980]
  rfl
theorem sub2984 (p : Pattern) : d603 (change p 158 none) = d1649 p := by
  change (if p 138 then d562 (change p 158 none) else d583 (change p 158 none)) = d1649 p
  rw [sub2943, sub2964]
  rfl
theorem sub2985 (p : Pattern) : d604 (change p 158 none) = d1653 p := by
  change (if p 138 then d568 (change p 158 none) else d551 (change p 158 none)) = d1653 p
  rw [sub2949, sub2932]
  rfl
theorem sub2986 (p : Pattern) : d605 (change p 158 none) = d1654 p := by
  change (if p 134 then d604 (change p 158 none) else d603 (change p 158 none)) = d1654 p
  rw [sub2985, sub2984]
  rfl
theorem sub2987 (p : Pattern) : d606 (change p 158 none) = d1655 p := by
  change (if p 133 then d601 (change p 158 none) else d605 (change p 158 none)) = d1655 p
  rw [sub2982, sub2986]
  rfl
theorem sub2988 (p : Pattern) : d607 (change p 158 none) = d1656 p := by
  change (if p 132 then d606 (change p 158 none) else d602 (change p 158 none)) = d1656 p
  rw [sub2987, sub2983]
  rfl
theorem sub2989 (p : Pattern) : d608 (change p 158 none) = d1657 p := by
  change (if p 113 then d607 (change p 158 none) else d556 (change p 158 none)) = d1657 p
  rw [sub2988, sub2937]
  rfl
theorem sub2990 (p : Pattern) : d609 (change p 158 none) = d1658 p := by
  change (if p 133 then d580 (change p 158 none) else d577 (change p 158 none)) = d1658 p
  rw [sub2961, sub2958]
  rfl
theorem sub2991 (p : Pattern) : d610 (change p 158 none) = d1659 p := by
  change (if p 132 then d580 (change p 158 none) else d609 (change p 158 none)) = d1659 p
  rw [sub2961, sub2990]
  rfl
theorem sub2992 (p : Pattern) : d611 (change p 158 none) = d1660 p := by
  change (if p 112 then d610 (change p 158 none) else d608 (change p 158 none)) = d1660 p
  rw [sub2991, sub2989]
  rfl
theorem sub2993 (p : Pattern) : d612 (change p 158 none) = d1649 p := by
  change (if p 134 then d598 (change p 158 none) else d603 (change p 158 none)) = d1649 p
  rw [sub2979, sub2984]
  simp only [ite_self]
theorem sub2994 (p : Pattern) : d613 (change p 158 none) = d1652 p := by
  change (if p 133 then d601 (change p 158 none) else d612 (change p 158 none)) = d1652 p
  rw [sub2982, sub2993]
  rfl
theorem sub2995 (p : Pattern) : d614 (change p 158 none) = d1661 p := by
  change (if p 133 then d586 (change p 158 none) else d601 (change p 158 none)) = d1661 p
  rw [sub2967, sub2982]
  rfl
theorem sub2996 (p : Pattern) : d615 (change p 158 none) = d1662 p := by
  change (if p 132 then d614 (change p 158 none) else d613 (change p 158 none)) = d1662 p
  rw [sub2995, sub2994]
  rfl
theorem sub2997 (p : Pattern) : d616 (change p 158 none) = d1663 p := by
  change (if p 113 then d615 (change p 158 none) else d588 (change p 158 none)) = d1663 p
  rw [sub2996, sub2969]
  rfl
theorem sub2998 (p : Pattern) : d617 (change p 158 none) = d1664 p := by
  change (if p 133 then d2 (change p 158 none) else d580 (change p 158 none)) = d1664 p
  rw [sub2902, sub2961]
  rfl
theorem sub2999 (p : Pattern) : d618 (change p 158 none) = d1665 p := by
  change (if p 132 then d617 (change p 158 none) else d609 (change p 158 none)) = d1665 p
  rw [sub2998, sub2990]
  rfl
end NetHack.Sokoban32Refined
