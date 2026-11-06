/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions22
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2760 (p : Pattern) : d265 (change p 132 (some 106)) = d1224 p := by
  change (if p 112 then d264 (change p 132 (some 106)) else d262 (change p 132 (some 106))) = d1224 p
  rw [sub2759, sub2748]
  rfl
theorem sub2761 (p : Pattern) : d266 (change p 132 (some 106)) = d1224 p := by
  change d265 (change p 132 (some 106)) = d1224 p
  exact sub2760 p
theorem sub2762 (p : Pattern) : d86 (change p 132 (some 106)) = d86 p := by
  change (if p 138 then d52 (change p 132 (some 106)) else d8 (change p 132 (some 106))) = d86 p
  rw [sub2752, sub2724]
  rfl
theorem sub2763 (p : Pattern) : d87 (change p 132 (some 106)) = d87 p := by
  change (if p 138 then d54 (change p 132 (some 106)) else d20 (change p 132 (some 106))) = d87 p
  rw [sub2754, sub2737]
  rfl
theorem sub2764 (p : Pattern) : d88 (change p 132 (some 106)) = d88 p := by
  change (if p 134 then d87 (change p 132 (some 106)) else d86 (change p 132 (some 106))) = d88 p
  rw [sub2763, sub2762]
  rfl
theorem sub2765 (p : Pattern) : d89 (change p 132 (some 106)) = d89 p := by
  change (if p 133 then d88 (change p 132 (some 106)) else d86 (change p 132 (some 106))) = d89 p
  rw [sub2764, sub2762]
  rfl
theorem sub2766 (p : Pattern) : d273 (change p 132 (some 106)) = d89 p := by
  change d89 (change p 132 (some 106)) = d89 p
  exact sub2765 p
theorem sub2767 (p : Pattern) : d274 (change p 132 (some 106)) = d1225 p := by
  change (if p 113 then d273 (change p 132 (some 106)) else d261 (change p 132 (some 106))) = d1225 p
  rw [sub2766, sub2747]
  rfl
theorem sub2768 (p : Pattern) : d97 (change p 132 (some 106)) = d97 p := by
  change (if p 139 then d2 (change p 132 (some 106)) else d14 (change p 132 (some 106))) = d97 p
  rw [sub2718, sub2731]
  rfl
theorem sub2769 (p : Pattern) : d98 (change p 132 (some 106)) = d98 p := by
  change (if p 138 then d97 (change p 132 (some 106)) else d14 (change p 132 (some 106))) = d98 p
  rw [sub2768, sub2731]
  rfl
theorem sub2770 (p : Pattern) : d70 (change p 132 (some 106)) = d70 p := by
  change (if p 139 then d2 (change p 132 (some 106)) else d24 (change p 132 (some 106))) = d70 p
  rw [sub2718, sub2741]
  rfl
theorem sub2771 (p : Pattern) : d71 (change p 132 (some 106)) = d71 p := by
  change (if p 138 then d70 (change p 132 (some 106)) else d24 (change p 132 (some 106))) = d71 p
  rw [sub2770, sub2741]
  rfl
theorem sub2772 (p : Pattern) : d99 (change p 132 (some 106)) = d99 p := by
  change (if p 134 then d71 (change p 132 (some 106)) else d98 (change p 132 (some 106))) = d99 p
  rw [sub2771, sub2769]
  rfl
theorem sub2773 (p : Pattern) : d100 (change p 132 (some 106)) = d100 p := by
  change (if p 133 then d99 (change p 132 (some 106)) else d98 (change p 132 (some 106))) = d100 p
  rw [sub2772, sub2769]
  rfl
theorem sub2774 (p : Pattern) : d270 (change p 132 (some 106)) = d100 p := by
  change d100 (change p 132 (some 106)) = d100 p
  exact sub2773 p
theorem sub2775 (p : Pattern) : d109 (change p 132 (some 106)) = d109 p := by
  change (if p 134 then d70 (change p 132 (some 106)) else d97 (change p 132 (some 106))) = d109 p
  rw [sub2770, sub2768]
  rfl
theorem sub2776 (p : Pattern) : d110 (change p 132 (some 106)) = d110 p := by
  change (if p 133 then d109 (change p 132 (some 106)) else d97 (change p 132 (some 106))) = d110 p
  rw [sub2775, sub2768]
  rfl
theorem sub2777 (p : Pattern) : d275 (change p 132 (some 106)) = d110 p := by
  change d110 (change p 132 (some 106)) = d110 p
  exact sub2776 p
theorem sub2778 (p : Pattern) : d276 (change p 132 (some 106)) = d1227 p := by
  change (if p 113 then d275 (change p 132 (some 106)) else d270 (change p 132 (some 106))) = d1227 p
  rw [sub2777, sub2774]
  rfl
theorem sub2779 (p : Pattern) : d277 (change p 132 (some 106)) = d1228 p := by
  change (if p 112 then d276 (change p 132 (some 106)) else d274 (change p 132 (some 106))) = d1228 p
  rw [sub2778, sub2767]
  rfl
theorem sub2780 (p : Pattern) : d278 (change p 132 (some 106)) = d1228 p := by
  change d277 (change p 132 (some 106)) = d1228 p
  exact sub2779 p
theorem sub2781 (p : Pattern) : d279 (change p 132 (some 106)) = d1501 p := by
  change (if p 86 then d278 (change p 132 (some 106)) else d266 (change p 132 (some 106))) = d1501 p
  rw [sub2780, sub2761]
  rfl
theorem sub2782 (p : Pattern) : d280 (change p 132 (some 106)) = d28 p := by
  change d28 (change p 132 (some 106)) = d28 p
  exact sub2745 p
theorem sub2783 (p : Pattern) : d281 (change p 132 (some 106)) = d28 p := by
  change (if p 113 then d280 (change p 132 (some 106)) else d261 (change p 132 (some 106))) = d28 p
  rw [sub2782, sub2747]
  simp only [ite_self]
theorem sub2784 (p : Pattern) : d282 (change p 132 (some 106)) = d47 p := by
  change d47 (change p 132 (some 106)) = d47 p
  exact sub2750 p
theorem sub2785 (p : Pattern) : d283 (change p 132 (some 106)) = d57 p := by
  change d57 (change p 132 (some 106)) = d57 p
  exact sub2757 p
theorem sub2786 (p : Pattern) : d284 (change p 132 (some 106)) = d1223 p := by
  change (if p 113 then d283 (change p 132 (some 106)) else d282 (change p 132 (some 106))) = d1223 p
  rw [sub2785, sub2784]
  rfl
theorem sub2787 (p : Pattern) : d285 (change p 132 (some 106)) = d1224 p := by
  change (if p 112 then d284 (change p 132 (some 106)) else d281 (change p 132 (some 106))) = d1224 p
  rw [sub2786, sub2783]
  rfl
theorem sub2788 (p : Pattern) : d286 (change p 132 (some 106)) = d1224 p := by
  change d285 (change p 132 (some 106)) = d1224 p
  exact sub2787 p
theorem sub2789 (p : Pattern) : d287 (change p 132 (some 106)) = d1231 p := by
  change (if p 113 then d283 (change p 132 (some 106)) else d280 (change p 132 (some 106))) = d1231 p
  rw [sub2785, sub2782]
  rfl
theorem sub2790 (p : Pattern) : d288 (change p 132 (some 106)) = d1232 p := by
  change (if p 113 then d2 (change p 132 (some 106)) else d275 (change p 132 (some 106))) = d1232 p
  rw [sub2718, sub2777]
  rfl
theorem sub2791 (p : Pattern) : d289 (change p 132 (some 106)) = d1233 p := by
  change (if p 112 then d288 (change p 132 (some 106)) else d287 (change p 132 (some 106))) = d1233 p
  rw [sub2790, sub2789]
  rfl
theorem sub2792 (p : Pattern) : d290 (change p 132 (some 106)) = d1233 p := by
  change d289 (change p 132 (some 106)) = d1233 p
  exact sub2791 p
theorem sub2793 (p : Pattern) : d291 (change p 132 (some 106)) = d1502 p := by
  change (if p 86 then d290 (change p 132 (some 106)) else d286 (change p 132 (some 106))) = d1502 p
  rw [sub2792, sub2788]
  rfl
theorem sub2794 (p : Pattern) : d292 (change p 132 (some 106)) = d1503 p := by
  change (if p 80 then d291 (change p 132 (some 106)) else d279 (change p 132 (some 106))) = d1503 p
  rw [sub2793, sub2781]
  rfl
theorem sub2795 (p : Pattern) : d0 (change p 159 (some 160)) = d0 p := by
  rfl
theorem sub2796 (p : Pattern) : d2 (change p 159 (some 160)) = d2 p := by
  rfl
theorem sub2797 (p : Pattern) : d3 (change p 159 (some 160)) = d3 p := by
  change (if p 161 then d2 (change p 159 (some 160)) else d0 (change p 159 (some 160))) = d3 p
  rw [sub2796, sub2795]
  rfl
theorem sub2798 (p : Pattern) : d4 (change p 159 (some 160)) = d3 p := by
  change d3 (change p 159 (some 160)) = d3 p
  exact sub2797 p
theorem sub2799 (p : Pattern) : d7 (change p 159 (some 160)) = d3 p := by
  change d4 (change p 159 (some 160)) = d3 p
  exact sub2798 p
theorem sub2800 (p : Pattern) : d1 (change p 159 (some 160)) = d1 p := by
  rfl
theorem sub2801 (p : Pattern) : d9 (change p 159 (some 160)) = d9 p := by
  change (if p 161 then d2 (change p 159 (some 160)) else d1 (change p 159 (some 160))) = d9 p
  rw [sub2796, sub2800]
  rfl
theorem sub2802 (p : Pattern) : d10 (change p 159 (some 160)) = d9 p := by
  change d9 (change p 159 (some 160)) = d9 p
  exact sub2801 p
theorem sub2803 (p : Pattern) : d13 (change p 159 (some 160)) = d9 p := by
  change d10 (change p 159 (some 160)) = d9 p
  exact sub2802 p
theorem sub2804 (p : Pattern) : d653 (change p 159 (some 160)) = d1507 p := by
  change (if p 139 then d13 (change p 159 (some 160)) else d7 (change p 159 (some 160))) = d1507 p
  rw [sub2803, sub2799]
  rfl
theorem sub2805 (p : Pattern) : d654 (change p 159 (some 160)) = d1508 p := by
  change (if p 138 then d653 (change p 159 (some 160)) else d7 (change p 159 (some 160))) = d1508 p
  rw [sub2804, sub2799]
  rfl
theorem sub2806 (p : Pattern) : d655 (change p 159 (some 160)) = d1509 p := by
  change (if p 139 then d2 (change p 159 (some 160)) else d7 (change p 159 (some 160))) = d1509 p
  rw [sub2796, sub2799]
  rfl
theorem sub2807 (p : Pattern) : d656 (change p 159 (some 160)) = d1510 p := by
  change (if p 138 then d655 (change p 159 (some 160)) else d653 (change p 159 (some 160))) = d1510 p
  rw [sub2806, sub2804]
  rfl
theorem sub2808 (p : Pattern) : d657 (change p 159 (some 160)) = d1511 p := by
  change (if p 113 then d656 (change p 159 (some 160)) else d653 (change p 159 (some 160))) = d1511 p
  rw [sub2807, sub2804]
  rfl
theorem sub2809 (p : Pattern) : d658 (change p 159 (some 160)) = d1512 p := by
  change (if p 112 then d657 (change p 159 (some 160)) else d654 (change p 159 (some 160))) = d1512 p
  rw [sub2808, sub2805]
  rfl
theorem sub2810 (p : Pattern) : d659 (change p 159 (some 160)) = d1513 p := by
  change (if p 139 then d2 (change p 159 (some 160)) else d13 (change p 159 (some 160))) = d1513 p
  rw [sub2796, sub2803]
  rfl
theorem sub2811 (p : Pattern) : d660 (change p 159 (some 160)) = d1514 p := by
  change (if p 138 then d659 (change p 159 (some 160)) else d13 (change p 159 (some 160))) = d1514 p
  rw [sub2810, sub2803]
  rfl
theorem sub2812 (p : Pattern) : d661 (change p 159 (some 160)) = d1515 p := by
  change (if p 133 then d660 (change p 159 (some 160)) else d654 (change p 159 (some 160))) = d1515 p
  rw [sub2811, sub2805]
  rfl
theorem sub2813 (p : Pattern) : d662 (change p 159 (some 160)) = d1516 p := by
  change (if p 132 then d661 (change p 159 (some 160)) else d654 (change p 159 (some 160))) = d1516 p
  rw [sub2812, sub2805]
  rfl
theorem sub2814 (p : Pattern) : d663 (change p 159 (some 160)) = d1517 p := by
  change (if p 133 then d659 (change p 159 (some 160)) else d654 (change p 159 (some 160))) = d1517 p
  rw [sub2810, sub2805]
  rfl
theorem sub2815 (p : Pattern) : d664 (change p 159 (some 160)) = d1518 p := by
  change (if p 132 then d663 (change p 159 (some 160)) else d654 (change p 159 (some 160))) = d1518 p
  rw [sub2814, sub2805]
  rfl
theorem sub2816 (p : Pattern) : d665 (change p 159 (some 160)) = d1519 p := by
  change (if p 113 then d664 (change p 159 (some 160)) else d662 (change p 159 (some 160))) = d1519 p
  rw [sub2815, sub2813]
  rfl
theorem sub2817 (p : Pattern) : d666 (change p 159 (some 160)) = d1520 p := by
  change (if p 133 then d659 (change p 159 (some 160)) else d653 (change p 159 (some 160))) = d1520 p
  rw [sub2810, sub2804]
  rfl
theorem sub2818 (p : Pattern) : d667 (change p 159 (some 160)) = d1521 p := by
  change (if p 132 then d666 (change p 159 (some 160)) else d653 (change p 159 (some 160))) = d1521 p
  rw [sub2817, sub2804]
  rfl
theorem sub2819 (p : Pattern) : d668 (change p 159 (some 160)) = d1522 p := by
  change (if p 133 then d659 (change p 159 (some 160)) else d656 (change p 159 (some 160))) = d1522 p
  rw [sub2810, sub2807]
  rfl
theorem sub2820 (p : Pattern) : d669 (change p 159 (some 160)) = d1523 p := by
  change (if p 132 then d668 (change p 159 (some 160)) else d656 (change p 159 (some 160))) = d1523 p
  rw [sub2819, sub2807]
  rfl
theorem sub2821 (p : Pattern) : d670 (change p 159 (some 160)) = d1524 p := by
  change (if p 113 then d669 (change p 159 (some 160)) else d667 (change p 159 (some 160))) = d1524 p
  rw [sub2820, sub2818]
  rfl
theorem sub2822 (p : Pattern) : d671 (change p 159 (some 160)) = d1525 p := by
  change (if p 112 then d670 (change p 159 (some 160)) else d665 (change p 159 (some 160))) = d1525 p
  rw [sub2821, sub2816]
  rfl
theorem sub2823 (p : Pattern) : d672 (change p 159 (some 160)) = d1526 p := by
  change (if p 106 then d671 (change p 159 (some 160)) else d658 (change p 159 (some 160))) = d1526 p
  rw [sub2822, sub2809]
  rfl
theorem sub2824 (p : Pattern) : d673 (change p 159 (some 160)) = d1527 p := by
  change (if p 138 then d655 (change p 159 (some 160)) else d7 (change p 159 (some 160))) = d1527 p
  rw [sub2806, sub2799]
  rfl
theorem sub2825 (p : Pattern) : d674 (change p 159 (some 160)) = d1528 p := by
  change (if p 113 then d673 (change p 159 (some 160)) else d654 (change p 159 (some 160))) = d1528 p
  rw [sub2824, sub2805]
  rfl
theorem sub2826 (p : Pattern) : d675 (change p 159 (some 160)) = d1529 p := by
  change (if p 112 then d660 (change p 159 (some 160)) else d674 (change p 159 (some 160))) = d1529 p
  rw [sub2811, sub2825]
  rfl
theorem sub2827 (p : Pattern) : d676 (change p 159 (some 160)) = d1530 p := by
  change (if p 133 then d659 (change p 159 (some 160)) else d673 (change p 159 (some 160))) = d1530 p
  rw [sub2810, sub2824]
  rfl
theorem sub2828 (p : Pattern) : d677 (change p 159 (some 160)) = d1531 p := by
  change (if p 132 then d676 (change p 159 (some 160)) else d673 (change p 159 (some 160))) = d1531 p
  rw [sub2827, sub2824]
  rfl
theorem sub2829 (p : Pattern) : d678 (change p 159 (some 160)) = d1532 p := by
  change (if p 113 then d677 (change p 159 (some 160)) else d664 (change p 159 (some 160))) = d1532 p
  rw [sub2828, sub2815]
  rfl
theorem sub2830 (p : Pattern) : d679 (change p 159 (some 160)) = d1533 p := by
  change (if p 133 then d2 (change p 159 (some 160)) else d660 (change p 159 (some 160))) = d1533 p
  rw [sub2796, sub2811]
  rfl
theorem sub2831 (p : Pattern) : d680 (change p 159 (some 160)) = d1534 p := by
  change (if p 132 then d679 (change p 159 (some 160)) else d660 (change p 159 (some 160))) = d1534 p
  rw [sub2830, sub2811]
  rfl
theorem sub2832 (p : Pattern) : d681 (change p 159 (some 160)) = d1535 p := by
  change (if p 133 then d2 (change p 159 (some 160)) else d659 (change p 159 (some 160))) = d1535 p
  rw [sub2796, sub2810]
  rfl
theorem sub2833 (p : Pattern) : d682 (change p 159 (some 160)) = d1536 p := by
  change (if p 132 then d681 (change p 159 (some 160)) else d659 (change p 159 (some 160))) = d1536 p
  rw [sub2832, sub2810]
  rfl
theorem sub2834 (p : Pattern) : d683 (change p 159 (some 160)) = d1537 p := by
  change (if p 113 then d682 (change p 159 (some 160)) else d680 (change p 159 (some 160))) = d1537 p
  rw [sub2833, sub2831]
  rfl
theorem sub2835 (p : Pattern) : d684 (change p 159 (some 160)) = d1538 p := by
  change (if p 112 then d683 (change p 159 (some 160)) else d678 (change p 159 (some 160))) = d1538 p
  rw [sub2834, sub2829]
  rfl
theorem sub2836 (p : Pattern) : d685 (change p 159 (some 160)) = d1539 p := by
  change (if p 106 then d684 (change p 159 (some 160)) else d675 (change p 159 (some 160))) = d1539 p
  rw [sub2835, sub2826]
  rfl
theorem sub2837 (p : Pattern) : d686 (change p 159 (some 160)) = d1540 p := by
  change (if p 86 then d685 (change p 159 (some 160)) else d672 (change p 159 (some 160))) = d1540 p
  rw [sub2836, sub2823]
  rfl
theorem sub2838 (p : Pattern) : d687 (change p 159 (some 160)) = d1541 p := by
  change (if p 112 then d670 (change p 159 (some 160)) else d664 (change p 159 (some 160))) = d1541 p
  rw [sub2821, sub2815]
  rfl
theorem sub2839 (p : Pattern) : d688 (change p 159 (some 160)) = d1542 p := by
  change (if p 106 then d687 (change p 159 (some 160)) else d658 (change p 159 (some 160))) = d1542 p
  rw [sub2838, sub2809]
  rfl
theorem sub2840 (p : Pattern) : d689 (change p 159 (some 160)) = d1543 p := by
  change (if p 113 then d659 (change p 159 (some 160)) else d660 (change p 159 (some 160))) = d1543 p
  rw [sub2810, sub2811]
  rfl
theorem sub2841 (p : Pattern) : d690 (change p 159 (some 160)) = d1544 p := by
  change (if p 112 then d689 (change p 159 (some 160)) else d674 (change p 159 (some 160))) = d1544 p
  rw [sub2840, sub2825]
  rfl
theorem sub2842 (p : Pattern) : d691 (change p 159 (some 160)) = d1545 p := by
  change (if p 113 then d669 (change p 159 (some 160)) else d664 (change p 159 (some 160))) = d1545 p
  rw [sub2820, sub2815]
  rfl
theorem sub2843 (p : Pattern) : d692 (change p 159 (some 160)) = d1546 p := by
  change (if p 113 then d2 (change p 159 (some 160)) else d682 (change p 159 (some 160))) = d1546 p
  rw [sub2796, sub2833]
  rfl
theorem sub2844 (p : Pattern) : d693 (change p 159 (some 160)) = d1547 p := by
  change (if p 112 then d692 (change p 159 (some 160)) else d691 (change p 159 (some 160))) = d1547 p
  rw [sub2843, sub2842]
  rfl
theorem sub2845 (p : Pattern) : d694 (change p 159 (some 160)) = d1548 p := by
  change (if p 106 then d693 (change p 159 (some 160)) else d690 (change p 159 (some 160))) = d1548 p
  rw [sub2844, sub2841]
  rfl
theorem sub2846 (p : Pattern) : d695 (change p 159 (some 160)) = d1549 p := by
  change (if p 86 then d694 (change p 159 (some 160)) else d688 (change p 159 (some 160))) = d1549 p
  rw [sub2845, sub2839]
  rfl
theorem sub2847 (p : Pattern) : d696 (change p 159 (some 160)) = d1550 p := by
  change (if p 80 then d695 (change p 159 (some 160)) else d686 (change p 159 (some 160))) = d1550 p
  rw [sub2846, sub2837]
  rfl
theorem sub2848 (p : Pattern) : d0 (change p 160 (some 161)) = d0 p := by
  rfl
theorem sub2849 (p : Pattern) : d5 (change p 160 (some 161)) = d0 p := by
  change d0 (change p 160 (some 161)) = d0 p
  exact sub2848 p
theorem sub2850 (p : Pattern) : d2 (change p 160 (some 161)) = d2 p := by
  rfl
theorem sub2851 (p : Pattern) : d37 (change p 160 (some 161)) = d1554 p := by
  change (if p 159 then d2 (change p 160 (some 161)) else d5 (change p 160 (some 161))) = d1554 p
  rw [sub2850, sub2849]
  rfl
theorem sub2852 (p : Pattern) : d697 (change p 160 (some 161)) = d1555 p := by
  change (if p 158 then d37 (change p 160 (some 161)) else d5 (change p 160 (some 161))) = d1555 p
  rw [sub2851, sub2849]
  rfl
theorem sub2853 (p : Pattern) : d1 (change p 160 (some 161)) = d1 p := by
  rfl
theorem sub2854 (p : Pattern) : d11 (change p 160 (some 161)) = d1 p := by
  change d1 (change p 160 (some 161)) = d1 p
  exact sub2853 p
theorem sub2855 (p : Pattern) : d39 (change p 160 (some 161)) = d1556 p := by
  change (if p 159 then d2 (change p 160 (some 161)) else d11 (change p 160 (some 161))) = d1556 p
  rw [sub2850, sub2854]
  rfl
theorem sub2856 (p : Pattern) : d698 (change p 160 (some 161)) = d1557 p := by
  change (if p 158 then d39 (change p 160 (some 161)) else d11 (change p 160 (some 161))) = d1557 p
  rw [sub2855, sub2854]
  rfl
theorem sub2857 (p : Pattern) : d699 (change p 160 (some 161)) = d1558 p := by
  change (if p 139 then d698 (change p 160 (some 161)) else d697 (change p 160 (some 161))) = d1558 p
  rw [sub2856, sub2852]
  rfl
theorem sub2858 (p : Pattern) : d700 (change p 160 (some 161)) = d1559 p := by
  change (if p 138 then d699 (change p 160 (some 161)) else d697 (change p 160 (some 161))) = d1559 p
  rw [sub2857, sub2852]
  rfl
theorem sub2859 (p : Pattern) : d701 (change p 160 (some 161)) = d1560 p := by
  change (if p 139 then d2 (change p 160 (some 161)) else d697 (change p 160 (some 161))) = d1560 p
  rw [sub2850, sub2852]
  rfl
theorem sub2860 (p : Pattern) : d702 (change p 160 (some 161)) = d1561 p := by
  change (if p 138 then d701 (change p 160 (some 161)) else d699 (change p 160 (some 161))) = d1561 p
  rw [sub2859, sub2857]
  rfl
theorem sub2861 (p : Pattern) : d703 (change p 160 (some 161)) = d1562 p := by
  change (if p 113 then d702 (change p 160 (some 161)) else d699 (change p 160 (some 161))) = d1562 p
  rw [sub2860, sub2857]
  rfl
theorem sub2862 (p : Pattern) : d704 (change p 160 (some 161)) = d1563 p := by
  change (if p 112 then d703 (change p 160 (some 161)) else d700 (change p 160 (some 161))) = d1563 p
  rw [sub2861, sub2858]
  rfl
theorem sub2863 (p : Pattern) : d705 (change p 160 (some 161)) = d1564 p := by
  change (if p 139 then d2 (change p 160 (some 161)) else d698 (change p 160 (some 161))) = d1564 p
  rw [sub2850, sub2856]
  rfl
theorem sub2864 (p : Pattern) : d706 (change p 160 (some 161)) = d1565 p := by
  change (if p 138 then d705 (change p 160 (some 161)) else d698 (change p 160 (some 161))) = d1565 p
  rw [sub2863, sub2856]
  rfl
theorem sub2865 (p : Pattern) : d707 (change p 160 (some 161)) = d1566 p := by
  change (if p 133 then d706 (change p 160 (some 161)) else d700 (change p 160 (some 161))) = d1566 p
  rw [sub2864, sub2858]
  rfl
theorem sub2866 (p : Pattern) : d708 (change p 160 (some 161)) = d1567 p := by
  change (if p 132 then d707 (change p 160 (some 161)) else d700 (change p 160 (some 161))) = d1567 p
  rw [sub2865, sub2858]
  rfl
theorem sub2867 (p : Pattern) : d709 (change p 160 (some 161)) = d1568 p := by
  change (if p 133 then d705 (change p 160 (some 161)) else d700 (change p 160 (some 161))) = d1568 p
  rw [sub2863, sub2858]
  rfl
theorem sub2868 (p : Pattern) : d710 (change p 160 (some 161)) = d1569 p := by
  change (if p 132 then d709 (change p 160 (some 161)) else d700 (change p 160 (some 161))) = d1569 p
  rw [sub2867, sub2858]
  rfl
theorem sub2869 (p : Pattern) : d711 (change p 160 (some 161)) = d1570 p := by
  change (if p 113 then d710 (change p 160 (some 161)) else d708 (change p 160 (some 161))) = d1570 p
  rw [sub2868, sub2866]
  rfl
theorem sub2870 (p : Pattern) : d712 (change p 160 (some 161)) = d1571 p := by
  change (if p 133 then d705 (change p 160 (some 161)) else d699 (change p 160 (some 161))) = d1571 p
  rw [sub2863, sub2857]
  rfl
theorem sub2871 (p : Pattern) : d713 (change p 160 (some 161)) = d1572 p := by
  change (if p 132 then d712 (change p 160 (some 161)) else d699 (change p 160 (some 161))) = d1572 p
  rw [sub2870, sub2857]
  rfl
theorem sub2872 (p : Pattern) : d714 (change p 160 (some 161)) = d1573 p := by
  change (if p 133 then d705 (change p 160 (some 161)) else d702 (change p 160 (some 161))) = d1573 p
  rw [sub2863, sub2860]
  rfl
theorem sub2873 (p : Pattern) : d715 (change p 160 (some 161)) = d1574 p := by
  change (if p 132 then d714 (change p 160 (some 161)) else d702 (change p 160 (some 161))) = d1574 p
  rw [sub2872, sub2860]
  rfl
theorem sub2874 (p : Pattern) : d716 (change p 160 (some 161)) = d1575 p := by
  change (if p 113 then d715 (change p 160 (some 161)) else d713 (change p 160 (some 161))) = d1575 p
  rw [sub2873, sub2871]
  rfl
theorem sub2875 (p : Pattern) : d717 (change p 160 (some 161)) = d1576 p := by
  change (if p 112 then d716 (change p 160 (some 161)) else d711 (change p 160 (some 161))) = d1576 p
  rw [sub2874, sub2869]
  rfl
theorem sub2876 (p : Pattern) : d718 (change p 160 (some 161)) = d1577 p := by
  change (if p 106 then d717 (change p 160 (some 161)) else d704 (change p 160 (some 161))) = d1577 p
  rw [sub2875, sub2862]
  rfl
theorem sub2877 (p : Pattern) : d719 (change p 160 (some 161)) = d1578 p := by
  change (if p 138 then d701 (change p 160 (some 161)) else d697 (change p 160 (some 161))) = d1578 p
  rw [sub2859, sub2852]
  rfl
theorem sub2878 (p : Pattern) : d720 (change p 160 (some 161)) = d1579 p := by
  change (if p 113 then d719 (change p 160 (some 161)) else d700 (change p 160 (some 161))) = d1579 p
  rw [sub2877, sub2858]
  rfl
theorem sub2879 (p : Pattern) : d721 (change p 160 (some 161)) = d1580 p := by
  change (if p 112 then d706 (change p 160 (some 161)) else d720 (change p 160 (some 161))) = d1580 p
  rw [sub2864, sub2878]
  rfl
end NetHack.Sokoban32Refined
