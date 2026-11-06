/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions25
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s3900 (pattern : Twelve) : d1107 (change pattern 10 12) = d117 pattern := by
  change d117 (change pattern 10 12) = d117 pattern
  exact s3899 pattern
theorem s3901 (pattern : Twelve) : d1117 (change pattern 10 12) = d2116 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d1107 (change pattern 10 12)) = d2116 pattern
  rw [s3682, s3900]
  rfl
theorem s3902 (pattern : Twelve) : d1130 (change pattern 10 12) = d2117 pattern := by
  change (if pattern.h then d1117 (change pattern 10 12) else d530 (change pattern 10 12)) = d2117 pattern
  rw [s3901, s3820]
  rfl
theorem s3903 (pattern : Twelve) : d1150 (change pattern 10 12) = d2118 pattern := by
  change (if pattern.f then d1130 (change pattern 10 12) else d549 (change pattern 10 12)) = d2118 pattern
  rw [s3902, s3753]
  rfl
theorem s3904 (pattern : Twelve) : d1131 (change pattern 10 12) = d2674 pattern := by
  change (if pattern.h then d6 (change pattern 10 12) else d522 (change pattern 10 12)) = d2674 pattern
  rw [s3682, s3757]
  rfl
theorem s3905 (pattern : Twelve) : d1151 (change pattern 10 12) = d2675 pattern := by
  change (if pattern.f then d1131 (change pattern 10 12) else d559 (change pattern 10 12)) = d2675 pattern
  rw [s3904, s3818]
  rfl
theorem s3906 (pattern : Twelve) : d1163 (change pattern 10 12) = d2676 pattern := by
  change (if pattern.e then d1151 (change pattern 10 12) else d1150 (change pattern 10 12)) = d2676 pattern
  rw [s3905, s3903]
  rfl
theorem s3907 (pattern : Twelve) : d1171 (change pattern 10 12) = d2677 pattern := by
  change (if pattern.j then d1163 (change pattern 10 12) else d1162 (change pattern 10 12)) = d2677 pattern
  rw [s3906, s3898]
  rfl
theorem s3908 (pattern : Twelve) : d1172 (change pattern 10 12) = d2678 pattern := by
  change (if pattern.j then d6 (change pattern 10 12) else d1161 (change pattern 10 12)) = d2678 pattern
  rw [s3682, s3892]
  rfl
theorem s3909 (pattern : Twelve) : d1176 (change pattern 10 12) = d2679 pattern := by
  change (if pattern.d then d1172 (change pattern 10 12) else d1171 (change pattern 10 12)) = d2679 pattern
  rw [s3908, s3907]
  rfl
theorem s3910 (pattern : Twelve) : d1179 (change pattern 10 12) = d2680 pattern := by
  change (if pattern.c then d1176 (change pattern 10 12) else d1170 (change pattern 10 12)) = d2680 pattern
  rw [s3909, s3893]
  rfl
theorem s3911 (pattern : Twelve) : d1182 (change pattern 10 12) = d2681 pattern := by
  change (if pattern.a then d1179 (change pattern 10 12) else d1181 (change pattern 10 12)) = d2681 pattern
  rw [s3910, s3883]
  rfl
theorem s3912 (pattern : Twelve) : d1505 (change pattern 10 12) = d2128 pattern := by
  change (if pattern.h then d479 (change pattern 10 12) else d1108 (change pattern 10 12)) = d2128 pattern
  rw [s3669, s3832]
  rfl
theorem s3913 (pattern : Twelve) : d1517 (change pattern 10 12) = d2129 pattern := by
  change (if pattern.f then d1505 (change pattern 10 12) else d1119 (change pattern 10 12)) = d2129 pattern
  rw [s3912, s3835]
  rfl
theorem s3914 (pattern : Twelve) : d1518 (change pattern 10 12) = d2682 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d482 (change pattern 10 12)) = d2682 pattern
  rw [s3682, s3681]
  rfl
theorem s3915 (pattern : Twelve) : d1532 (change pattern 10 12) = d2683 pattern := by
  change (if pattern.e then d1518 (change pattern 10 12) else d1517 (change pattern 10 12)) = d2683 pattern
  rw [s3914, s3913]
  rfl
theorem s3916 (pattern : Twelve) : d1495 (change pattern 10 12) = d2060 pattern := by
  change (if pattern.i then d1106 (change pattern 10 12) else d1105 (change pattern 10 12)) = d2060 pattern
  rw [s3861, s3831]
  rfl
theorem s3917 (pattern : Twelve) : d1496 (change pattern 10 12) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d479 (change pattern 10 12)) = d45 pattern
  rw [s3682, s3669]
  rfl
theorem s3918 (pattern : Twelve) : d1506 (change pattern 10 12) = d2134 pattern := by
  change (if pattern.h then d1496 (change pattern 10 12) else d1495 (change pattern 10 12)) = d2134 pattern
  rw [s3917, s3916]
  rfl
theorem s3919 (pattern : Twelve) : d1519 (change pattern 10 12) = d2135 pattern := by
  change (if pattern.f then d1506 (change pattern 10 12) else d544 (change pattern 10 12)) = d2135 pattern
  rw [s3918, s3729]
  rfl
theorem s3920 (pattern : Twelve) : d1507 (change pattern 10 12) = d2684 pattern := by
  change (if pattern.h then d503 (change pattern 10 12) else d1109 (change pattern 10 12)) = d2684 pattern
  rw [s3683, s3836]
  rfl
theorem s3921 (pattern : Twelve) : d1520 (change pattern 10 12) = d2685 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d1507 (change pattern 10 12)) = d2685 pattern
  rw [s3682, s3920]
  rfl
theorem s3922 (pattern : Twelve) : d1533 (change pattern 10 12) = d2686 pattern := by
  change (if pattern.e then d1520 (change pattern 10 12) else d1519 (change pattern 10 12)) = d2686 pattern
  rw [s3921, s3919]
  rfl
theorem s3923 (pattern : Twelve) : d1541 (change pattern 10 12) = d2687 pattern := by
  change (if pattern.j then d1533 (change pattern 10 12) else d1532 (change pattern 10 12)) = d2687 pattern
  rw [s3922, s3915]
  rfl
theorem s3924 (pattern : Twelve) : d1521 (change pattern 10 12) = d2129 pattern := by
  change (if pattern.f then d1505 (change pattern 10 12) else d480 (change pattern 10 12)) = d2129 pattern
  rw [s3912, s3673]
  rfl
theorem s3925 (pattern : Twelve) : d1534 (change pattern 10 12) = d2683 pattern := by
  change (if pattern.e then d1518 (change pattern 10 12) else d1521 (change pattern 10 12)) = d2683 pattern
  rw [s3914, s3924]
  rfl
theorem s3926 (pattern : Twelve) : d1542 (change pattern 10 12) = d2687 pattern := by
  change (if pattern.j then d1533 (change pattern 10 12) else d1534 (change pattern 10 12)) = d2687 pattern
  rw [s3922, s3925]
  rfl
theorem s3927 (pattern : Twelve) : d1548 (change pattern 10 12) = d2687 pattern := by
  change (if pattern.d then d1542 (change pattern 10 12) else d1541 (change pattern 10 12)) = d2687 pattern
  rw [s3926, s3923]
  simp only [ite_self]
theorem s3928 (pattern : Twelve) : d1497 (change pattern 10 12) = d46 pattern := by
  change (if pattern.i then d492 (change pattern 10 12) else d479 (change pattern 10 12)) = d46 pattern
  rw [s3740, s3669]
  rfl
theorem s3929 (pattern : Twelve) : d1508 (change pattern 10 12) = d2140 pattern := by
  change (if pattern.h then d1497 (change pattern 10 12) else d1495 (change pattern 10 12)) = d2140 pattern
  rw [s3928, s3916]
  rfl
theorem s3930 (pattern : Twelve) : d1522 (change pattern 10 12) = d2141 pattern := by
  change (if pattern.f then d1508 (change pattern 10 12) else d509 (change pattern 10 12)) = d2141 pattern
  rw [s3929, s3709]
  rfl
theorem s3931 (pattern : Twelve) : d1523 (change pattern 10 12) = d2688 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d1109 (change pattern 10 12)) = d2688 pattern
  rw [s3682, s3836]
  rfl
theorem s3932 (pattern : Twelve) : d1535 (change pattern 10 12) = d2689 pattern := by
  change (if pattern.e then d1523 (change pattern 10 12) else d1522 (change pattern 10 12)) = d2689 pattern
  rw [s3931, s3930]
  rfl
theorem s3933 (pattern : Twelve) : d15 (change pattern 10 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 10 12) else d4 (change pattern 10 12)) = d15 pattern
  rw [s3692, s3699]
  rfl
theorem s3934 (pattern : Twelve) : d1493 (change pattern 10 12) = d15 pattern := by
  change d15 (change pattern 10 12) = d15 pattern
  exact s3933 pattern
theorem s3935 (pattern : Twelve) : d1498 (change pattern 10 12) = d2087 pattern := by
  change (if pattern.i then d1493 (change pattern 10 12) else d1106 (change pattern 10 12)) = d2087 pattern
  rw [s3934, s3861]
  rfl
theorem s3936 (pattern : Twelve) : d1509 (change pattern 10 12) = d2144 pattern := by
  change (if pattern.h then d529 (change pattern 10 12) else d1498 (change pattern 10 12)) = d2144 pattern
  rw [s3817, s3935]
  rfl
theorem s3937 (pattern : Twelve) : d1524 (change pattern 10 12) = d2145 pattern := by
  change (if pattern.f then d1509 (change pattern 10 12) else d549 (change pattern 10 12)) = d2145 pattern
  rw [s3936, s3753]
  rfl
theorem s3938 (pattern : Twelve) : d1510 (change pattern 10 12) = d2238 pattern := by
  change (if pattern.h then d522 (change pattern 10 12) else d1113 (change pattern 10 12)) = d2238 pattern
  rw [s3757, s3865]
  rfl
theorem s3939 (pattern : Twelve) : d1525 (change pattern 10 12) = d2690 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d1510 (change pattern 10 12)) = d2690 pattern
  rw [s3682, s3938]
  rfl
theorem s3940 (pattern : Twelve) : d1536 (change pattern 10 12) = d2691 pattern := by
  change (if pattern.e then d1525 (change pattern 10 12) else d1524 (change pattern 10 12)) = d2691 pattern
  rw [s3939, s3937]
  rfl
theorem s3941 (pattern : Twelve) : d1543 (change pattern 10 12) = d2692 pattern := by
  change (if pattern.j then d1536 (change pattern 10 12) else d1535 (change pattern 10 12)) = d2692 pattern
  rw [s3940, s3932]
  rfl
theorem s3942 (pattern : Twelve) : d1544 (change pattern 10 12) = d2693 pattern := by
  change (if pattern.j then d6 (change pattern 10 12) else d1533 (change pattern 10 12)) = d2693 pattern
  rw [s3682, s3922]
  rfl
theorem s3943 (pattern : Twelve) : d1549 (change pattern 10 12) = d2694 pattern := by
  change (if pattern.d then d1544 (change pattern 10 12) else d1543 (change pattern 10 12)) = d2694 pattern
  rw [s3942, s3941]
  rfl
theorem s3944 (pattern : Twelve) : d1551 (change pattern 10 12) = d2695 pattern := by
  change (if pattern.c then d1549 (change pattern 10 12) else d1548 (change pattern 10 12)) = d2695 pattern
  rw [s3943, s3927]
  rfl
theorem s3945 (pattern : Twelve) : d1552 (change pattern 10 12) = d2695 pattern := by
  change (if pattern.c then d1549 (change pattern 10 12) else d1542 (change pattern 10 12)) = d2695 pattern
  rw [s3943, s3926]
  rfl
theorem s3946 (pattern : Twelve) : d1554 (change pattern 10 12) = d2695 pattern := by
  change (if pattern.g then d1552 (change pattern 10 12) else d1551 (change pattern 10 12)) = d2695 pattern
  rw [s3945, s3944]
  simp only [ite_self]
theorem s3947 (pattern : Twelve) : d1555 (change pattern 10 12) = d2695 pattern := by
  change (if pattern.b then d1552 (change pattern 10 12) else d1554 (change pattern 10 12)) = d2695 pattern
  rw [s3945, s3946]
  simp only [ite_self]
theorem s3948 (pattern : Twelve) : d11 (change pattern 10 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 10 12) else d1 (change pattern 10 12)) = d11 pattern
  rw [s3691, s3665]
  rfl
theorem s3949 (pattern : Twelve) : d1494 (change pattern 10 12) = d11 pattern := by
  change d11 (change pattern 10 12) = d11 pattern
  exact s3948 pattern
theorem s3950 (pattern : Twelve) : d1499 (change pattern 10 12) = d2696 pattern := by
  change (if pattern.i then d1494 (change pattern 10 12) else d1105 (change pattern 10 12)) = d2696 pattern
  rw [s3949, s3831]
  rfl
theorem s3951 (pattern : Twelve) : d1500 (change pattern 10 12) = d2697 pattern := by
  change (if pattern.i then d1494 (change pattern 10 12) else d479 (change pattern 10 12)) = d2697 pattern
  rw [s3949, s3669]
  rfl
theorem s3952 (pattern : Twelve) : d1511 (change pattern 10 12) = d2698 pattern := by
  change (if pattern.h then d1500 (change pattern 10 12) else d1499 (change pattern 10 12)) = d2698 pattern
  rw [s3951, s3950]
  rfl
theorem s3953 (pattern : Twelve) : d1526 (change pattern 10 12) = d2699 pattern := by
  change (if pattern.f then d1511 (change pattern 10 12) else d480 (change pattern 10 12)) = d2699 pattern
  rw [s3952, s3673]
  rfl
theorem s3954 (pattern : Twelve) : d1537 (change pattern 10 12) = d2700 pattern := by
  change (if pattern.e then d1518 (change pattern 10 12) else d1526 (change pattern 10 12)) = d2700 pattern
  rw [s3914, s3953]
  rfl
theorem s3955 (pattern : Twelve) : d1512 (change pattern 10 12) = d2164 pattern := by
  change (if pattern.h then d1496 (change pattern 10 12) else d1111 (change pattern 10 12)) = d2164 pattern
  rw [s3917, s3855]
  rfl
theorem s3956 (pattern : Twelve) : d1527 (change pattern 10 12) = d2165 pattern := by
  change (if pattern.f then d1512 (change pattern 10 12) else d544 (change pattern 10 12)) = d2165 pattern
  rw [s3955, s3729]
  rfl
theorem s3957 (pattern : Twelve) : d1538 (change pattern 10 12) = d2701 pattern := by
  change (if pattern.e then d1520 (change pattern 10 12) else d1527 (change pattern 10 12)) = d2701 pattern
  rw [s3921, s3956]
  rfl
theorem s3958 (pattern : Twelve) : d1545 (change pattern 10 12) = d2702 pattern := by
  change (if pattern.j then d1538 (change pattern 10 12) else d1537 (change pattern 10 12)) = d2702 pattern
  rw [s3957, s3954]
  rfl
theorem s3959 (pattern : Twelve) : d1501 (change pattern 10 12) = d2169 pattern := by
  change (if pattern.i then d1493 (change pattern 10 12) else d479 (change pattern 10 12)) = d2169 pattern
  rw [s3934, s3669]
  rfl
theorem s3960 (pattern : Twelve) : d1513 (change pattern 10 12) = d2170 pattern := by
  change (if pattern.h then d1501 (change pattern 10 12) else d1111 (change pattern 10 12)) = d2170 pattern
  rw [s3959, s3855]
  rfl
theorem s3961 (pattern : Twelve) : d1528 (change pattern 10 12) = d2171 pattern := by
  change (if pattern.f then d1513 (change pattern 10 12) else d509 (change pattern 10 12)) = d2171 pattern
  rw [s3960, s3709]
  rfl
theorem s3962 (pattern : Twelve) : d1502 (change pattern 10 12) = d2703 pattern := by
  change (if pattern.i then d486 (change pattern 10 12) else d482 (change pattern 10 12)) = d2703 pattern
  rw [s3694, s3681]
  rfl
theorem s3963 (pattern : Twelve) : d1514 (change pattern 10 12) = d2704 pattern := by
  change (if pattern.h then d1502 (change pattern 10 12) else d1109 (change pattern 10 12)) = d2704 pattern
  rw [s3962, s3836]
  rfl
theorem s3964 (pattern : Twelve) : d1529 (change pattern 10 12) = d2705 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d1514 (change pattern 10 12)) = d2705 pattern
  rw [s3682, s3963]
  rfl
theorem s3965 (pattern : Twelve) : d1539 (change pattern 10 12) = d2706 pattern := by
  change (if pattern.e then d1529 (change pattern 10 12) else d1528 (change pattern 10 12)) = d2706 pattern
  rw [s3964, s3961]
  rfl
theorem s3966 (pattern : Twelve) : d1503 (change pattern 10 12) = d2176 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d1493 (change pattern 10 12)) = d2176 pattern
  rw [s3682, s3934]
  rfl
theorem s3967 (pattern : Twelve) : d1515 (change pattern 10 12) = d2177 pattern := by
  change (if pattern.h then d1503 (change pattern 10 12) else d1112 (change pattern 10 12)) = d2177 pattern
  rw [s3966, s3862]
  rfl
theorem s3968 (pattern : Twelve) : d1530 (change pattern 10 12) = d2178 pattern := by
  change (if pattern.f then d1515 (change pattern 10 12) else d549 (change pattern 10 12)) = d2178 pattern
  rw [s3967, s3753]
  rfl
theorem s3969 (pattern : Twelve) : d1504 (change pattern 10 12) = d2707 pattern := by
  change (if pattern.i then d22 (change pattern 10 12) else d495 (change pattern 10 12)) = d2707 pattern
  rw [s3706, s3756]
  rfl
theorem s3970 (pattern : Twelve) : d1516 (change pattern 10 12) = d2708 pattern := by
  change (if pattern.h then d531 (change pattern 10 12) else d1504 (change pattern 10 12)) = d2708 pattern
  rw [s3821, s3969]
  rfl
theorem s3971 (pattern : Twelve) : d1531 (change pattern 10 12) = d2709 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d1516 (change pattern 10 12)) = d2709 pattern
  rw [s3682, s3970]
  rfl
theorem s3972 (pattern : Twelve) : d1540 (change pattern 10 12) = d2710 pattern := by
  change (if pattern.e then d1531 (change pattern 10 12) else d1530 (change pattern 10 12)) = d2710 pattern
  rw [s3971, s3968]
  rfl
theorem s3973 (pattern : Twelve) : d1546 (change pattern 10 12) = d2711 pattern := by
  change (if pattern.j then d1540 (change pattern 10 12) else d1539 (change pattern 10 12)) = d2711 pattern
  rw [s3972, s3965]
  rfl
theorem s3974 (pattern : Twelve) : d1547 (change pattern 10 12) = d2712 pattern := by
  change (if pattern.j then d6 (change pattern 10 12) else d1538 (change pattern 10 12)) = d2712 pattern
  rw [s3682, s3957]
  rfl
theorem s3975 (pattern : Twelve) : d1550 (change pattern 10 12) = d2713 pattern := by
  change (if pattern.d then d1547 (change pattern 10 12) else d1546 (change pattern 10 12)) = d2713 pattern
  rw [s3974, s3973]
  rfl
theorem s3976 (pattern : Twelve) : d1553 (change pattern 10 12) = d2714 pattern := by
  change (if pattern.c then d1550 (change pattern 10 12) else d1545 (change pattern 10 12)) = d2714 pattern
  rw [s3975, s3958]
  rfl
theorem s3977 (pattern : Twelve) : d1556 (change pattern 10 12) = d2715 pattern := by
  change (if pattern.a then d1553 (change pattern 10 12) else d1555 (change pattern 10 12)) = d2715 pattern
  rw [s3976, s3947]
  rfl
theorem s3978 (pattern : Twelve) : d1753 (change pattern 10 12) = d2716 pattern := by
  change (if pattern.f then d1494 (change pattern 10 12) else d482 (change pattern 10 12)) = d2716 pattern
  rw [s3949, s3681]
  rfl
theorem s3979 (pattern : Twelve) : d1754 (change pattern 10 12) = d2717 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d495 (change pattern 10 12)) = d2717 pattern
  rw [s3682, s3756]
  rfl
theorem s3980 (pattern : Twelve) : d1763 (change pattern 10 12) = d2718 pattern := by
  change (if pattern.e then d1754 (change pattern 10 12) else d1753 (change pattern 10 12)) = d2718 pattern
  rw [s3979, s3978]
  rfl
theorem s3981 (pattern : Twelve) : d1745 (change pattern 10 12) = d2130 pattern := by
  change (if pattern.i then d486 (change pattern 10 12) else d1494 (change pattern 10 12)) = d2130 pattern
  rw [s3694, s3949]
  rfl
theorem s3982 (pattern : Twelve) : d1746 (change pattern 10 12) = d2061 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d1494 (change pattern 10 12)) = d2061 pattern
  rw [s3682, s3949]
  rfl
theorem s3983 (pattern : Twelve) : d1749 (change pattern 10 12) = d2196 pattern := by
  change (if pattern.h then d1746 (change pattern 10 12) else d1745 (change pattern 10 12)) = d2196 pattern
  rw [s3982, s3981]
  rfl
theorem s3984 (pattern : Twelve) : d1755 (change pattern 10 12) = d2719 pattern := by
  change (if pattern.f then d1749 (change pattern 10 12) else d1507 (change pattern 10 12)) = d2719 pattern
  rw [s3983, s3920]
  rfl
theorem s3985 (pattern : Twelve) : d1764 (change pattern 10 12) = d2720 pattern := by
  change (if pattern.e then d1525 (change pattern 10 12) else d1755 (change pattern 10 12)) = d2720 pattern
  rw [s3939, s3984]
  rfl
theorem s3986 (pattern : Twelve) : d1770 (change pattern 10 12) = d2721 pattern := by
  change (if pattern.j then d1764 (change pattern 10 12) else d1763 (change pattern 10 12)) = d2721 pattern
  rw [s3985, s3980]
  rfl
theorem s3987 (pattern : Twelve) : d1756 (change pattern 10 12) = d2722 pattern := by
  change (if pattern.f then d1745 (change pattern 10 12) else d1109 (change pattern 10 12)) = d2722 pattern
  rw [s3981, s3836]
  rfl
theorem s3988 (pattern : Twelve) : d1757 (change pattern 10 12) = d2723 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d1113 (change pattern 10 12)) = d2723 pattern
  rw [s3682, s3865]
  rfl
theorem s3989 (pattern : Twelve) : d1765 (change pattern 10 12) = d2724 pattern := by
  change (if pattern.e then d1757 (change pattern 10 12) else d1756 (change pattern 10 12)) = d2724 pattern
  rw [s3988, s3987]
  rfl
theorem s3990 (pattern : Twelve) : d1747 (change pattern 10 12) = d2147 pattern := by
  change (if pattern.i then d22 (change pattern 10 12) else d486 (change pattern 10 12)) = d2147 pattern
  rw [s3706, s3694]
  rfl
theorem s3991 (pattern : Twelve) : d1750 (change pattern 10 12) = d2206 pattern := by
  change (if pattern.h then d531 (change pattern 10 12) else d1747 (change pattern 10 12)) = d2206 pattern
  rw [s3821, s3990]
  rfl
theorem s3992 (pattern : Twelve) : d1758 (change pattern 10 12) = d2725 pattern := by
  change (if pattern.f then d1750 (change pattern 10 12) else d1510 (change pattern 10 12)) = d2725 pattern
  rw [s3991, s3938]
  rfl
theorem s3993 (pattern : Twelve) : d1759 (change pattern 10 12) = d2726 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d178 (change pattern 10 12)) = d2726 pattern
  rw [s3682, s3866]
  rfl
theorem s3994 (pattern : Twelve) : d1766 (change pattern 10 12) = d2727 pattern := by
  change (if pattern.e then d1759 (change pattern 10 12) else d1758 (change pattern 10 12)) = d2727 pattern
  rw [s3993, s3992]
  rfl
theorem s3995 (pattern : Twelve) : d1771 (change pattern 10 12) = d2728 pattern := by
  change (if pattern.j then d1766 (change pattern 10 12) else d1765 (change pattern 10 12)) = d2728 pattern
  rw [s3994, s3989]
  rfl
theorem s3996 (pattern : Twelve) : d1772 (change pattern 10 12) = d2729 pattern := by
  change (if pattern.j then d6 (change pattern 10 12) else d1764 (change pattern 10 12)) = d2729 pattern
  rw [s3682, s3985]
  rfl
theorem s3997 (pattern : Twelve) : d1775 (change pattern 10 12) = d2730 pattern := by
  change (if pattern.d then d1772 (change pattern 10 12) else d1771 (change pattern 10 12)) = d2730 pattern
  rw [s3996, s3995]
  rfl
theorem s3998 (pattern : Twelve) : d1777 (change pattern 10 12) = d2731 pattern := by
  change (if pattern.c then d1775 (change pattern 10 12) else d1770 (change pattern 10 12)) = d2731 pattern
  rw [s3997, s3986]
  rfl
theorem s3999 (pattern : Twelve) : d1760 (change pattern 10 12) = d2732 pattern := by
  change (if pattern.f then d1745 (change pattern 10 12) else d482 (change pattern 10 12)) = d2732 pattern
  rw [s3981, s3681]
  rfl
theorem s4000 (pattern : Twelve) : d1767 (change pattern 10 12) = d2733 pattern := by
  change (if pattern.e then d1754 (change pattern 10 12) else d1760 (change pattern 10 12)) = d2733 pattern
  rw [s3979, s3999]
  rfl
theorem s4001 (pattern : Twelve) : d1773 (change pattern 10 12) = d2734 pattern := by
  change (if pattern.j then d1764 (change pattern 10 12) else d1767 (change pattern 10 12)) = d2734 pattern
  rw [s3985, s4000]
  rfl
theorem s4002 (pattern : Twelve) : d1748 (change pattern 10 12) = d2160 pattern := by
  change (if pattern.i then d22 (change pattern 10 12) else d1494 (change pattern 10 12)) = d2160 pattern
  rw [s3706, s3949]
  rfl
theorem s4003 (pattern : Twelve) : d1751 (change pattern 10 12) = d2735 pattern := by
  change (if pattern.h then d1748 (change pattern 10 12) else d1745 (change pattern 10 12)) = d2735 pattern
  rw [s4002, s3981]
  rfl
theorem s4004 (pattern : Twelve) : d1761 (change pattern 10 12) = d2736 pattern := by
  change (if pattern.f then d1751 (change pattern 10 12) else d1109 (change pattern 10 12)) = d2736 pattern
  rw [s4003, s3836]
  rfl
theorem s4005 (pattern : Twelve) : d1768 (change pattern 10 12) = d2737 pattern := by
  change (if pattern.e then d1525 (change pattern 10 12) else d1761 (change pattern 10 12)) = d2737 pattern
  rw [s3939, s4004]
  rfl
theorem s4006 (pattern : Twelve) : d183 (change pattern 10 12) = d2148 pattern := by
  change (if pattern.i then d6 (change pattern 10 12) else d22 (change pattern 10 12)) = d2148 pattern
  rw [s3682, s3706]
  rfl
theorem s4007 (pattern : Twelve) : d1752 (change pattern 10 12) = d2738 pattern := by
  change (if pattern.h then d183 (change pattern 10 12) else d531 (change pattern 10 12)) = d2738 pattern
  rw [s4006, s3821]
  rfl
theorem s4008 (pattern : Twelve) : d1762 (change pattern 10 12) = d2739 pattern := by
  change (if pattern.f then d1752 (change pattern 10 12) else d1510 (change pattern 10 12)) = d2739 pattern
  rw [s4007, s3938]
  rfl
theorem s4009 (pattern : Twelve) : d191 (change pattern 10 12) = d2257 pattern := by
  change (if pattern.h then d6 (change pattern 10 12) else d178 (change pattern 10 12)) = d2257 pattern
  rw [s3682, s3866]
  rfl
theorem s4010 (pattern : Twelve) : d202 (change pattern 10 12) = d2740 pattern := by
  change (if pattern.f then d6 (change pattern 10 12) else d191 (change pattern 10 12)) = d2740 pattern
  rw [s3682, s4009]
  rfl
theorem s4011 (pattern : Twelve) : d1769 (change pattern 10 12) = d2741 pattern := by
  change (if pattern.e then d202 (change pattern 10 12) else d1762 (change pattern 10 12)) = d2741 pattern
  rw [s4010, s4008]
  rfl
theorem s4012 (pattern : Twelve) : d1774 (change pattern 10 12) = d2742 pattern := by
  change (if pattern.j then d1769 (change pattern 10 12) else d1768 (change pattern 10 12)) = d2742 pattern
  rw [s4011, s4005]
  rfl
theorem s4013 (pattern : Twelve) : d1776 (change pattern 10 12) = d2743 pattern := by
  change (if pattern.d then d1772 (change pattern 10 12) else d1774 (change pattern 10 12)) = d2743 pattern
  rw [s3996, s4012]
  rfl
theorem s4014 (pattern : Twelve) : d1778 (change pattern 10 12) = d2744 pattern := by
  change (if pattern.c then d1776 (change pattern 10 12) else d1773 (change pattern 10 12)) = d2744 pattern
  rw [s4013, s4001]
  rfl
theorem s4015 (pattern : Twelve) : d1779 (change pattern 10 12) = d2745 pattern := by
  change (if pattern.a then d1778 (change pattern 10 12) else d1777 (change pattern 10 12)) = d2745 pattern
  rw [s4014, s3998]
  rfl
theorem s4016 (pattern : Twelve) : d0 (change pattern 11 12) = d0 pattern := by
  rfl
theorem s4017 (pattern : Twelve) : d7 (change pattern 11 12) = d0 pattern := by
  change d0 (change pattern 11 12) = d0 pattern
  exact s4016 pattern
theorem s4018 (pattern : Twelve) : d158 (change pattern 11 12) = d0 pattern := by
  change d0 (change pattern 11 12) = d0 pattern
  exact s4016 pattern
theorem s4019 (pattern : Twelve) : d634 (change pattern 11 12) = d0 pattern := by
  change (if pattern.k then d158 (change pattern 11 12) else d7 (change pattern 11 12)) = d0 pattern
  rw [s4018, s4017]
  simp only [ite_self]
theorem s4020 (pattern : Twelve) : d647 (change pattern 11 12) = d0 pattern := by
  change (if pattern.i then d634 (change pattern 11 12) else d0 (change pattern 11 12)) = d0 pattern
  rw [s4019, s4016]
  simp only [ite_self]
theorem s4021 (pattern : Twelve) : d162 (change pattern 11 12) = d0 pattern := by
  change (if pattern.k then d158 (change pattern 11 12) else d0 (change pattern 11 12)) = d0 pattern
  rw [s4018, s4016]
  simp only [ite_self]
theorem s4022 (pattern : Twelve) : d649 (change pattern 11 12) = d0 pattern := by
  change (if pattern.i then d158 (change pattern 11 12) else d162 (change pattern 11 12)) = d0 pattern
  rw [s4018, s4021]
  simp only [ite_self]
theorem s4023 (pattern : Twelve) : d682 (change pattern 11 12) = d0 pattern := by
  change (if pattern.h then d649 (change pattern 11 12) else d647 (change pattern 11 12)) = d0 pattern
  rw [s4022, s4020]
  simp only [ite_self]
theorem s4024 (pattern : Twelve) : d1 (change pattern 11 12) = d1 pattern := by
  rfl
theorem s4025 (pattern : Twelve) : d157 (change pattern 11 12) = d1 pattern := by
  change d1 (change pattern 11 12) = d1 pattern
  exact s4024 pattern
theorem s4026 (pattern : Twelve) : d648 (change pattern 11 12) = d26 pattern := by
  change (if pattern.i then d157 (change pattern 11 12) else d162 (change pattern 11 12)) = d26 pattern
  rw [s4025, s4021]
  rfl
theorem s4027 (pattern : Twelve) : d636 (change pattern 11 12) = d477 pattern := by
  change (if pattern.k then d157 (change pattern 11 12) else d158 (change pattern 11 12)) = d477 pattern
  rw [s4025, s4018]
  rfl
theorem s4028 (pattern : Twelve) : d1183 (change pattern 11 12) = d2747 pattern := by
  change (if pattern.i then d157 (change pattern 11 12) else d636 (change pattern 11 12)) = d2747 pattern
  rw [s4025, s4027]
  rfl
theorem s4029 (pattern : Twelve) : d1189 (change pattern 11 12) = d2748 pattern := by
  change (if pattern.h then d1183 (change pattern 11 12) else d648 (change pattern 11 12)) = d2748 pattern
  rw [s4028, s4026]
  rfl
theorem s4030 (pattern : Twelve) : d1199 (change pattern 11 12) = d2749 pattern := by
  change (if pattern.f then d1189 (change pattern 11 12) else d682 (change pattern 11 12)) = d2749 pattern
  rw [s4029, s4023]
  rfl
theorem s4031 (pattern : Twelve) : d1190 (change pattern 11 12) = d0 pattern := by
  change (if pattern.h then d158 (change pattern 11 12) else d649 (change pattern 11 12)) = d0 pattern
  rw [s4018, s4022]
  simp only [ite_self]
theorem s4032 (pattern : Twelve) : d2 (change pattern 11 12) = d2 pattern := by
  rfl
theorem s4033 (pattern : Twelve) : d160 (change pattern 11 12) = d2 pattern := by
  change d2 (change pattern 11 12) = d2 pattern
  exact s4032 pattern
theorem s4034 (pattern : Twelve) : d3 (change pattern 11 12) = d3 pattern := by
  rfl
theorem s4035 (pattern : Twelve) : d159 (change pattern 11 12) = d3 pattern := by
  change d3 (change pattern 11 12) = d3 pattern
  exact s4034 pattern
theorem s4036 (pattern : Twelve) : d644 (change pattern 11 12) = d2750 pattern := by
  change (if pattern.k then d159 (change pattern 11 12) else d160 (change pattern 11 12)) = d2750 pattern
  rw [s4035, s4033]
  rfl
theorem s4037 (pattern : Twelve) : d1184 (change pattern 11 12) = d2751 pattern := by
  change (if pattern.i then d644 (change pattern 11 12) else d636 (change pattern 11 12)) = d2751 pattern
  rw [s4036, s4027]
  rfl
theorem s4038 (pattern : Twelve) : d6 (change pattern 11 12) = d6 pattern := by
  rfl
theorem s4039 (pattern : Twelve) : d670 (change pattern 11 12) = d2752 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d644 (change pattern 11 12)) = d2752 pattern
  rw [s4038, s4036]
  rfl
theorem s4040 (pattern : Twelve) : d1191 (change pattern 11 12) = d2753 pattern := by
  change (if pattern.h then d670 (change pattern 11 12) else d1184 (change pattern 11 12)) = d2753 pattern
  rw [s4039, s4037]
  rfl
theorem s4041 (pattern : Twelve) : d1200 (change pattern 11 12) = d2754 pattern := by
  change (if pattern.f then d1191 (change pattern 11 12) else d1190 (change pattern 11 12)) = d2754 pattern
  rw [s4040, s4031]
  rfl
theorem s4042 (pattern : Twelve) : d1216 (change pattern 11 12) = d2755 pattern := by
  change (if pattern.e then d1200 (change pattern 11 12) else d1199 (change pattern 11 12)) = d2755 pattern
  rw [s4041, s4030]
  rfl
theorem s4043 (pattern : Twelve) : d10 (change pattern 11 12) = d0 pattern := by
  change d0 (change pattern 11 12) = d0 pattern
  exact s4016 pattern
theorem s4044 (pattern : Twelve) : d638 (change pattern 11 12) = d0 pattern := by
  change (if pattern.k then d158 (change pattern 11 12) else d10 (change pattern 11 12)) = d0 pattern
  rw [s4018, s4043]
  simp only [ite_self]
theorem s4045 (pattern : Twelve) : d654 (change pattern 11 12) = d30 pattern := by
  change (if pattern.i then d160 (change pattern 11 12) else d638 (change pattern 11 12)) = d30 pattern
  rw [s4033, s4044]
  rfl
theorem s4046 (pattern : Twelve) : d663 (change pattern 11 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d158 (change pattern 11 12)) = d35 pattern
  rw [s4038, s4018]
  rfl
theorem s4047 (pattern : Twelve) : d1192 (change pattern 11 12) = d56 pattern := by
  change (if pattern.h then d663 (change pattern 11 12) else d654 (change pattern 11 12)) = d56 pattern
  rw [s4046, s4045]
  rfl
theorem s4048 (pattern : Twelve) : d657 (change pattern 11 12) = d30 pattern := by
  change (if pattern.i then d160 (change pattern 11 12) else d158 (change pattern 11 12)) = d30 pattern
  rw [s4033, s4018]
  rfl
theorem s4049 (pattern : Twelve) : d651 (change pattern 11 12) = d2756 pattern := by
  change (if pattern.i then d6 (change pattern 11 12) else d636 (change pattern 11 12)) = d2756 pattern
  rw [s4038, s4027]
  rfl
end NetHack.Sokoban21.Diagram
