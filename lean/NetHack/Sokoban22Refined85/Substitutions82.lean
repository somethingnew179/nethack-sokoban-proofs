/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions81
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub9840 (p : Pattern) : d2692 (change p 225 none) = d5659 p := by
  change (if p 204 then d2691 (change p 225 none) else d2689 (change p 225 none)) = d5659 p
  rw [sub9839, sub9835]
  rfl
theorem sub9841 (p : Pattern) : d7 (change p 225 none) = d7 p := by
  rfl
theorem sub9842 (p : Pattern) : d1880 (change p 225 none) = d1880 p := by
  change (if p 247 then d7 (change p 225 none) else d5 (change p 225 none)) = d1880 p
  rw [sub9841, sub9816]
  rfl
theorem sub9843 (p : Pattern) : d119 (change p 225 none) = d119 p := by
  change (if p 247 then d12 (change p 225 none) else d7 (change p 225 none)) = d119 p
  rw [sub9592, sub9841]
  rfl
theorem sub9844 (p : Pattern) : d1881 (change p 225 none) = d1881 p := by
  change (if p 246 then d119 (change p 225 none) else d1880 (change p 225 none)) = d1881 p
  rw [sub9843, sub9842]
  rfl
theorem sub9845 (p : Pattern) : d2693 (change p 225 none) = d1881 p := by
  change d1881 (change p 225 none) = d1881 p
  exact sub9844 p
theorem sub9846 (p : Pattern) : d2694 (change p 225 none) = d5660 p := by
  change (if p 224 then d2693 (change p 225 none) else d2689 (change p 225 none)) = d5660 p
  rw [sub9845, sub9835]
  rfl
theorem sub9847 (p : Pattern) : d2695 (change p 225 none) = d5661 p := by
  change (if p 204 then d12 (change p 225 none) else d2694 (change p 225 none)) = d5661 p
  rw [sub9592, sub9846]
  rfl
theorem sub9848 (p : Pattern) : d2696 (change p 225 none) = d5662 p := by
  change (if p 182 then d2695 (change p 225 none) else d2692 (change p 225 none)) = d5662 p
  rw [sub9847, sub9840]
  rfl
theorem sub9849 (p : Pattern) : d2697 (change p 225 none) = d5663 p := by
  change (if p 163 then d2696 (change p 225 none) else d2687 (change p 225 none)) = d5663 p
  rw [sub9848, sub9832]
  rfl
theorem sub9850 (p : Pattern) : d2698 (change p 225 none) = d5664 p := by
  change (if p 162 then d2697 (change p 225 none) else d2688 (change p 225 none)) = d5664 p
  rw [sub9849, sub9833]
  rfl
theorem sub9851 (p : Pattern) : d2699 (change p 225 none) = d5665 p := by
  change (if p 163 then d12 (change p 225 none) else d2581 (change p 225 none)) = d5665 p
  rw [sub9592, sub9715]
  rfl
theorem sub9852 (p : Pattern) : d2700 (change p 225 none) = d5666 p := by
  change (if p 162 then d2699 (change p 225 none) else d2697 (change p 225 none)) = d5666 p
  rw [sub9851, sub9849]
  rfl
theorem sub9853 (p : Pattern) : d2701 (change p 225 none) = d5667 p := by
  change (if p 161 then d2700 (change p 225 none) else d2698 (change p 225 none)) = d5667 p
  rw [sub9852, sub9850]
  rfl
theorem sub9854 (p : Pattern) : d116 (change p 225 none) = d116 p := by
  change (if p 246 then d115 (change p 225 none) else d3 (change p 225 none)) = d116 p
  rw [sub9825, sub9823]
  rfl
theorem sub9855 (p : Pattern) : d2702 (change p 225 none) = d116 p := by
  change d116 (change p 225 none) = d116 p
  exact sub9854 p
theorem sub9856 (p : Pattern) : d1894 (change p 225 none) = d1894 p := by
  change (if p 247 then d7 (change p 225 none) else d3 (change p 225 none)) = d1894 p
  rw [sub9841, sub9823]
  rfl
theorem sub9857 (p : Pattern) : d1895 (change p 225 none) = d1895 p := by
  change (if p 246 then d119 (change p 225 none) else d1894 (change p 225 none)) = d1895 p
  rw [sub9843, sub9856]
  rfl
theorem sub9858 (p : Pattern) : d2703 (change p 225 none) = d1895 p := by
  change d1895 (change p 225 none) = d1895 p
  exact sub9857 p
theorem sub9859 (p : Pattern) : d2704 (change p 225 none) = d5668 p := by
  change (if p 224 then d2703 (change p 225 none) else d2702 (change p 225 none)) = d5668 p
  rw [sub9858, sub9855]
  rfl
theorem sub9860 (p : Pattern) : d2705 (change p 225 none) = d5669 p := by
  change (if p 204 then d12 (change p 225 none) else d2704 (change p 225 none)) = d5669 p
  rw [sub9592, sub9859]
  rfl
theorem sub9861 (p : Pattern) : d2706 (change p 225 none) = d5670 p := by
  change (if p 182 then d2705 (change p 225 none) else d2686 (change p 225 none)) = d5670 p
  rw [sub9860, sub9831]
  rfl
theorem sub9862 (p : Pattern) : d120 (change p 225 none) = d120 p := by
  change (if p 246 then d119 (change p 225 none) else d7 (change p 225 none)) = d120 p
  rw [sub9843, sub9841]
  rfl
theorem sub9863 (p : Pattern) : d2707 (change p 225 none) = d120 p := by
  change d120 (change p 225 none) = d120 p
  exact sub9862 p
theorem sub9864 (p : Pattern) : d1902 (change p 225 none) = d1902 p := by
  change (if p 247 then d11 (change p 225 none) else d7 (change p 225 none)) = d1902 p
  rw [sub9647, sub9841]
  rfl
theorem sub9865 (p : Pattern) : d1903 (change p 225 none) = d1903 p := by
  change (if p 246 then d39 (change p 225 none) else d1902 (change p 225 none)) = d1903 p
  rw [sub9649, sub9864]
  rfl
theorem sub9866 (p : Pattern) : d2708 (change p 225 none) = d1903 p := by
  change d1903 (change p 225 none) = d1903 p
  exact sub9865 p
theorem sub9867 (p : Pattern) : d2709 (change p 225 none) = d5671 p := by
  change (if p 224 then d2708 (change p 225 none) else d2707 (change p 225 none)) = d5671 p
  rw [sub9866, sub9863]
  rfl
theorem sub9868 (p : Pattern) : d2710 (change p 225 none) = d5672 p := by
  change (if p 204 then d12 (change p 225 none) else d2709 (change p 225 none)) = d5672 p
  rw [sub9592, sub9867]
  rfl
theorem sub9869 (p : Pattern) : d2711 (change p 225 none) = d5673 p := by
  change (if p 182 then d2710 (change p 225 none) else d2686 (change p 225 none)) = d5673 p
  rw [sub9868, sub9831]
  rfl
theorem sub9870 (p : Pattern) : d2712 (change p 225 none) = d5674 p := by
  change (if p 163 then d2711 (change p 225 none) else d2706 (change p 225 none)) = d5674 p
  rw [sub9869, sub9861]
  rfl
theorem sub9871 (p : Pattern) : d2713 (change p 225 none) = d5675 p := by
  change (if p 182 then d12 (change p 225 none) else d2686 (change p 225 none)) = d5675 p
  rw [sub9592, sub9831]
  rfl
theorem sub9872 (p : Pattern) : d2714 (change p 225 none) = d5676 p := by
  change (if p 182 then d12 (change p 225 none) else d2692 (change p 225 none)) = d5676 p
  rw [sub9592, sub9840]
  rfl
theorem sub9873 (p : Pattern) : d2715 (change p 225 none) = d5677 p := by
  change (if p 163 then d2714 (change p 225 none) else d2713 (change p 225 none)) = d5677 p
  rw [sub9872, sub9871]
  rfl
theorem sub9874 (p : Pattern) : d2716 (change p 225 none) = d5678 p := by
  change (if p 162 then d2715 (change p 225 none) else d2712 (change p 225 none)) = d5678 p
  rw [sub9873, sub9870]
  rfl
theorem sub9875 (p : Pattern) : d2717 (change p 225 none) = d5679 p := by
  change (if p 163 then d12 (change p 225 none) else d2592 (change p 225 none)) = d5679 p
  rw [sub9592, sub9726]
  rfl
theorem sub9876 (p : Pattern) : d2718 (change p 225 none) = d5680 p := by
  change (if p 162 then d2717 (change p 225 none) else d2715 (change p 225 none)) = d5680 p
  rw [sub9875, sub9873]
  rfl
theorem sub9877 (p : Pattern) : d2719 (change p 225 none) = d5681 p := by
  change (if p 161 then d2718 (change p 225 none) else d2716 (change p 225 none)) = d5681 p
  rw [sub9876, sub9874]
  rfl
theorem sub9878 (p : Pattern) : d2720 (change p 225 none) = d5682 p := by
  change (if p 160 then d2719 (change p 225 none) else d2701 (change p 225 none)) = d5682 p
  rw [sub9877, sub9853]
  rfl
theorem sub9879 (p : Pattern) : d2721 (change p 225 none) = d103 p := by
  change d103 (change p 225 none) = d103 p
  exact sub9812 p
theorem sub9880 (p : Pattern) : d2722 (change p 225 none) = d103 p := by
  change (if p 224 then d2677 (change p 225 none) else d2721 (change p 225 none)) = d103 p
  rw [sub9814, sub9879]
  simp only [ite_self]
theorem sub9881 (p : Pattern) : d2723 (change p 225 none) = d5654 p := by
  change (if p 204 then d2680 (change p 225 none) else d2722 (change p 225 none)) = d5654 p
  rw [sub9821, sub9880]
  rfl
theorem sub9882 (p : Pattern) : d2724 (change p 225 none) = d5657 p := by
  change (if p 182 then d2684 (change p 225 none) else d2723 (change p 225 none)) = d5657 p
  rw [sub9829, sub9881]
  rfl
theorem sub9883 (p : Pattern) : d2725 (change p 225 none) = d5683 p := by
  change (if p 204 then d2704 (change p 225 none) else d2702 (change p 225 none)) = d5683 p
  rw [sub9859, sub9855]
  rfl
theorem sub9884 (p : Pattern) : d1918 (change p 225 none) = d1918 p := by
  change (if p 247 then d5 (change p 225 none) else d3 (change p 225 none)) = d1918 p
  rw [sub9816, sub9823]
  rfl
theorem sub9885 (p : Pattern) : d1919 (change p 225 none) = d1919 p := by
  change (if p 246 then d106 (change p 225 none) else d1918 (change p 225 none)) = d1919 p
  rw [sub9818, sub9884]
  rfl
theorem sub9886 (p : Pattern) : d2726 (change p 225 none) = d1919 p := by
  change d1919 (change p 225 none) = d1919 p
  exact sub9885 p
theorem sub9887 (p : Pattern) : d2727 (change p 225 none) = d5684 p := by
  change (if p 224 then d2726 (change p 225 none) else d2702 (change p 225 none)) = d5684 p
  rw [sub9886, sub9855]
  rfl
theorem sub9888 (p : Pattern) : d2728 (change p 225 none) = d5685 p := by
  change (if p 204 then d12 (change p 225 none) else d2727 (change p 225 none)) = d5685 p
  rw [sub9592, sub9887]
  rfl
theorem sub9889 (p : Pattern) : d2729 (change p 225 none) = d5686 p := by
  change (if p 182 then d2728 (change p 225 none) else d2725 (change p 225 none)) = d5686 p
  rw [sub9888, sub9883]
  rfl
theorem sub9890 (p : Pattern) : d2730 (change p 225 none) = d5687 p := by
  change (if p 163 then d2729 (change p 225 none) else d2724 (change p 225 none)) = d5687 p
  rw [sub9889, sub9882]
  rfl
theorem sub9891 (p : Pattern) : d2731 (change p 225 none) = d5688 p := by
  change (if p 163 then d2581 (change p 225 none) else d2696 (change p 225 none)) = d5688 p
  rw [sub9715, sub9848]
  rfl
theorem sub9892 (p : Pattern) : d2732 (change p 225 none) = d5689 p := by
  change (if p 162 then d2731 (change p 225 none) else d2730 (change p 225 none)) = d5689 p
  rw [sub9891, sub9890]
  rfl
theorem sub9893 (p : Pattern) : d2733 (change p 225 none) = d5690 p := by
  change (if p 163 then d2584 (change p 225 none) else d2696 (change p 225 none)) = d5690 p
  rw [sub9718, sub9848]
  rfl
theorem sub9894 (p : Pattern) : d2734 (change p 225 none) = d5691 p := by
  change (if p 162 then d12 (change p 225 none) else d2733 (change p 225 none)) = d5691 p
  rw [sub9592, sub9893]
  rfl
theorem sub9895 (p : Pattern) : d2735 (change p 225 none) = d5692 p := by
  change (if p 161 then d2734 (change p 225 none) else d2732 (change p 225 none)) = d5692 p
  rw [sub9894, sub9892]
  rfl
theorem sub9896 (p : Pattern) : d2736 (change p 225 none) = d5693 p := by
  change (if p 182 then d12 (change p 225 none) else d2725 (change p 225 none)) = d5693 p
  rw [sub9592, sub9883]
  rfl
theorem sub9897 (p : Pattern) : d2737 (change p 225 none) = d5694 p := by
  change (if p 163 then d2736 (change p 225 none) else d2711 (change p 225 none)) = d5694 p
  rw [sub9896, sub9869]
  rfl
theorem sub9898 (p : Pattern) : d2738 (change p 225 none) = d5695 p := by
  change (if p 163 then d2592 (change p 225 none) else d2714 (change p 225 none)) = d5695 p
  rw [sub9726, sub9872]
  rfl
theorem sub9899 (p : Pattern) : d2739 (change p 225 none) = d5696 p := by
  change (if p 162 then d2738 (change p 225 none) else d2737 (change p 225 none)) = d5696 p
  rw [sub9898, sub9897]
  rfl
theorem sub9900 (p : Pattern) : d2740 (change p 225 none) = d5697 p := by
  change (if p 163 then d2594 (change p 225 none) else d2714 (change p 225 none)) = d5697 p
  rw [sub9728, sub9872]
  rfl
theorem sub9901 (p : Pattern) : d2741 (change p 225 none) = d5698 p := by
  change (if p 162 then d12 (change p 225 none) else d2740 (change p 225 none)) = d5698 p
  rw [sub9592, sub9900]
  rfl
theorem sub9902 (p : Pattern) : d2742 (change p 225 none) = d5699 p := by
  change (if p 161 then d2741 (change p 225 none) else d2739 (change p 225 none)) = d5699 p
  rw [sub9901, sub9899]
  rfl
theorem sub9903 (p : Pattern) : d2743 (change p 225 none) = d5700 p := by
  change (if p 160 then d2742 (change p 225 none) else d2735 (change p 225 none)) = d5700 p
  rw [sub9902, sub9895]
  rfl
theorem sub9904 (p : Pattern) : d2744 (change p 225 none) = d5701 p := by
  change (if p 141 then d2743 (change p 225 none) else d2720 (change p 225 none)) = d5701 p
  rw [sub9903, sub9878]
  rfl
theorem sub9905 (p : Pattern) : d2745 (change p 225 none) = d5702 p := by
  change (if p 204 then d12 (change p 225 none) else d2680 (change p 225 none)) = d5702 p
  rw [sub9592, sub9821]
  rfl
theorem sub9906 (p : Pattern) : d2746 (change p 225 none) = d5703 p := by
  change (if p 182 then d2745 (change p 225 none) else d2686 (change p 225 none)) = d5703 p
  rw [sub9905, sub9831]
  rfl
theorem sub9907 (p : Pattern) : d2747 (change p 225 none) = d5704 p := by
  change (if p 204 then d12 (change p 225 none) else d2691 (change p 225 none)) = d5704 p
  rw [sub9592, sub9839]
  rfl
theorem sub9908 (p : Pattern) : d2748 (change p 225 none) = d5705 p := by
  change (if p 182 then d2747 (change p 225 none) else d2692 (change p 225 none)) = d5705 p
  rw [sub9907, sub9840]
  rfl
theorem sub9909 (p : Pattern) : d2749 (change p 225 none) = d5706 p := by
  change (if p 163 then d2748 (change p 225 none) else d2746 (change p 225 none)) = d5706 p
  rw [sub9908, sub9906]
  rfl
theorem sub9910 (p : Pattern) : d2750 (change p 225 none) = d5707 p := by
  change (if p 162 then d2749 (change p 225 none) else d2746 (change p 225 none)) = d5707 p
  rw [sub9909, sub9906]
  rfl
theorem sub9911 (p : Pattern) : d2751 (change p 225 none) = d5708 p := by
  change (if p 162 then d2699 (change p 225 none) else d2749 (change p 225 none)) = d5708 p
  rw [sub9851, sub9909]
  rfl
theorem sub9912 (p : Pattern) : d2752 (change p 225 none) = d5709 p := by
  change (if p 161 then d2751 (change p 225 none) else d2750 (change p 225 none)) = d5709 p
  rw [sub9911, sub9910]
  rfl
theorem sub9913 (p : Pattern) : d2753 (change p 225 none) = d5710 p := by
  change (if p 182 then d2705 (change p 225 none) else d2725 (change p 225 none)) = d5710 p
  rw [sub9860, sub9883]
  rfl
theorem sub9914 (p : Pattern) : d2754 (change p 225 none) = d5711 p := by
  change (if p 204 then d2709 (change p 225 none) else d2707 (change p 225 none)) = d5711 p
  rw [sub9867, sub9863]
  rfl
theorem sub9915 (p : Pattern) : d2755 (change p 225 none) = d5712 p := by
  change (if p 182 then d2710 (change p 225 none) else d2754 (change p 225 none)) = d5712 p
  rw [sub9868, sub9914]
  rfl
theorem sub9916 (p : Pattern) : d2756 (change p 225 none) = d5713 p := by
  change (if p 163 then d2755 (change p 225 none) else d2753 (change p 225 none)) = d5713 p
  rw [sub9915, sub9913]
  rfl
theorem sub9917 (p : Pattern) : d2757 (change p 225 none) = d5714 p := by
  change (if p 162 then d12 (change p 225 none) else d2756 (change p 225 none)) = d5714 p
  rw [sub9592, sub9916]
  rfl
theorem sub9918 (p : Pattern) : d2758 (change p 225 none) = d5715 p := by
  change (if p 161 then d12 (change p 225 none) else d2757 (change p 225 none)) = d5715 p
  rw [sub9592, sub9917]
  rfl
theorem sub9919 (p : Pattern) : d2759 (change p 225 none) = d5716 p := by
  change (if p 160 then d2758 (change p 225 none) else d2752 (change p 225 none)) = d5716 p
  rw [sub9918, sub9912]
  rfl
theorem sub9920 (p : Pattern) : d2760 (change p 225 none) = d5717 p := by
  change (if p 163 then d2753 (change p 225 none) else d2746 (change p 225 none)) = d5717 p
  rw [sub9913, sub9906]
  rfl
theorem sub9921 (p : Pattern) : d2761 (change p 225 none) = d5718 p := by
  change (if p 163 then d2581 (change p 225 none) else d2748 (change p 225 none)) = d5718 p
  rw [sub9715, sub9908]
  rfl
theorem sub9922 (p : Pattern) : d2762 (change p 225 none) = d5719 p := by
  change (if p 162 then d2761 (change p 225 none) else d2760 (change p 225 none)) = d5719 p
  rw [sub9921, sub9920]
  rfl
theorem sub9923 (p : Pattern) : d2763 (change p 225 none) = d5720 p := by
  change (if p 163 then d2584 (change p 225 none) else d2748 (change p 225 none)) = d5720 p
  rw [sub9718, sub9908]
  rfl
theorem sub9924 (p : Pattern) : d2764 (change p 225 none) = d5721 p := by
  change (if p 162 then d12 (change p 225 none) else d2763 (change p 225 none)) = d5721 p
  rw [sub9592, sub9923]
  rfl
theorem sub9925 (p : Pattern) : d2765 (change p 225 none) = d5722 p := by
  change (if p 161 then d2764 (change p 225 none) else d2762 (change p 225 none)) = d5722 p
  rw [sub9924, sub9922]
  rfl
theorem sub9926 (p : Pattern) : d2766 (change p 225 none) = d5723 p := by
  change (if p 163 then d12 (change p 225 none) else d2755 (change p 225 none)) = d5723 p
  rw [sub9592, sub9915]
  rfl
theorem sub9927 (p : Pattern) : d2767 (change p 225 none) = d5724 p := by
  change (if p 162 then d12 (change p 225 none) else d2766 (change p 225 none)) = d5724 p
  rw [sub9592, sub9926]
  rfl
theorem sub9928 (p : Pattern) : d2768 (change p 225 none) = d5725 p := by
  change (if p 161 then d12 (change p 225 none) else d2767 (change p 225 none)) = d5725 p
  rw [sub9592, sub9927]
  rfl
theorem sub9929 (p : Pattern) : d2769 (change p 225 none) = d5726 p := by
  change (if p 160 then d2768 (change p 225 none) else d2765 (change p 225 none)) = d5726 p
  rw [sub9928, sub9925]
  rfl
theorem sub9930 (p : Pattern) : d2770 (change p 225 none) = d5727 p := by
  change (if p 141 then d2769 (change p 225 none) else d2759 (change p 225 none)) = d5727 p
  rw [sub9929, sub9919]
  rfl
theorem sub9931 (p : Pattern) : d2771 (change p 225 none) = d5728 p := by
  change (if p 138 then d2770 (change p 225 none) else d2744 (change p 225 none)) = d5728 p
  rw [sub9930, sub9904]
  rfl
theorem sub9932 (p : Pattern) : d2772 (change p 225 none) = d5729 p := by
  change (if p 162 then d12 (change p 225 none) else d2699 (change p 225 none)) = d5729 p
  rw [sub9592, sub9851]
  rfl
theorem sub9933 (p : Pattern) : d2773 (change p 225 none) = d5730 p := by
  change (if p 161 then d12 (change p 225 none) else d2772 (change p 225 none)) = d5730 p
  rw [sub9592, sub9932]
  rfl
theorem sub9934 (p : Pattern) : d2774 (change p 225 none) = d5731 p := by
  change (if p 160 then d12 (change p 225 none) else d2773 (change p 225 none)) = d5731 p
  rw [sub9592, sub9933]
  rfl
theorem sub9935 (p : Pattern) : d2775 (change p 225 none) = d5732 p := by
  change (if p 141 then d12 (change p 225 none) else d2774 (change p 225 none)) = d5732 p
  rw [sub9592, sub9934]
  rfl
theorem sub9936 (p : Pattern) : d2776 (change p 225 none) = d5733 p := by
  change (if p 138 then d2775 (change p 225 none) else d2770 (change p 225 none)) = d5733 p
  rw [sub9935, sub9930]
  rfl
theorem sub9937 (p : Pattern) : d2777 (change p 225 none) = d5734 p := by
  change (if p 116 then d2776 (change p 225 none) else d2771 (change p 225 none)) = d5734 p
  rw [sub9936, sub9931]
  rfl
theorem sub9938 (p : Pattern) : d2778 (change p 225 none) = d5664 p := by
  change (if p 162 then d2697 (change p 225 none) else d2687 (change p 225 none)) = d5664 p
  rw [sub9849, sub9832]
  rfl
theorem sub9939 (p : Pattern) : d2779 (change p 225 none) = d5667 p := by
  change (if p 161 then d2700 (change p 225 none) else d2778 (change p 225 none)) = d5667 p
  rw [sub9852, sub9938]
  rfl
theorem sub9940 (p : Pattern) : d2780 (change p 225 none) = d5682 p := by
  change (if p 160 then d2719 (change p 225 none) else d2779 (change p 225 none)) = d5682 p
  rw [sub9877, sub9939]
  rfl
theorem sub9941 (p : Pattern) : d2781 (change p 225 none) = d5687 p := by
  change (if p 163 then d2729 (change p 225 none) else d2687 (change p 225 none)) = d5687 p
  rw [sub9889, sub9832]
  rfl
theorem sub9942 (p : Pattern) : d2782 (change p 225 none) = d5689 p := by
  change (if p 162 then d2731 (change p 225 none) else d2781 (change p 225 none)) = d5689 p
  rw [sub9891, sub9941]
  rfl
theorem sub9943 (p : Pattern) : d2783 (change p 225 none) = d5692 p := by
  change (if p 161 then d2734 (change p 225 none) else d2782 (change p 225 none)) = d5692 p
  rw [sub9894, sub9942]
  rfl
theorem sub9944 (p : Pattern) : d2784 (change p 225 none) = d5700 p := by
  change (if p 160 then d2742 (change p 225 none) else d2783 (change p 225 none)) = d5700 p
  rw [sub9902, sub9943]
  rfl
theorem sub9945 (p : Pattern) : d2785 (change p 225 none) = d5701 p := by
  change (if p 141 then d2784 (change p 225 none) else d2780 (change p 225 none)) = d5701 p
  rw [sub9944, sub9940]
  rfl
theorem sub9946 (p : Pattern) : d2786 (change p 225 none) = d5728 p := by
  change (if p 138 then d2770 (change p 225 none) else d2785 (change p 225 none)) = d5728 p
  rw [sub9930, sub9945]
  rfl
theorem sub9947 (p : Pattern) : d2787 (change p 225 none) = d5735 p := by
  change (if p 138 then d12 (change p 225 none) else d2770 (change p 225 none)) = d5735 p
  rw [sub9592, sub9930]
  rfl
theorem sub9948 (p : Pattern) : d2788 (change p 225 none) = d5736 p := by
  change (if p 116 then d2787 (change p 225 none) else d2786 (change p 225 none)) = d5736 p
  rw [sub9947, sub9946]
  rfl
theorem sub9949 (p : Pattern) : d2789 (change p 225 none) = d5737 p := by
  change (if p 115 then d2788 (change p 225 none) else d2777 (change p 225 none)) = d5737 p
  rw [sub9948, sub9937]
  rfl
theorem sub9950 (p : Pattern) : d2790 (change p 225 none) = d5738 p := by
  change (if p 71 then d2789 (change p 225 none) else d2652 (change p 225 none)) = d5738 p
  rw [sub9949, sub9786]
  rfl
theorem sub9951 (p : Pattern) : d2791 (change p 225 none) = d5739 p := by
  change (if p 49 then d2790 (change p 225 none) else d2675 (change p 225 none)) = d5739 p
  rw [sub9950, sub9809]
  rfl
theorem sub9952 (p : Pattern) : d2792 (change p 225 none) = d5740 p := by
  change (if p 182 then d2548 (change p 225 none) else d2569 (change p 225 none)) = d5740 p
  rw [sub9674, sub9698]
  rfl
theorem sub9953 (p : Pattern) : d2793 (change p 225 none) = d5741 p := by
  change (if p 163 then d2792 (change p 225 none) else d2611 (change p 225 none)) = d5741 p
  rw [sub9952, sub9745]
  rfl
theorem sub9954 (p : Pattern) : d2794 (change p 225 none) = d5742 p := by
  change (if p 182 then d2553 (change p 225 none) else d2569 (change p 225 none)) = d5742 p
  rw [sub9682, sub9698]
  rfl
theorem sub9955 (p : Pattern) : d2795 (change p 225 none) = d5743 p := by
  change (if p 182 then d12 (change p 225 none) else d2612 (change p 225 none)) = d5743 p
  rw [sub9592, sub9746]
  rfl
theorem sub9956 (p : Pattern) : d2796 (change p 225 none) = d5744 p := by
  change (if p 163 then d2795 (change p 225 none) else d2794 (change p 225 none)) = d5744 p
  rw [sub9955, sub9954]
  rfl
theorem sub9957 (p : Pattern) : d2797 (change p 225 none) = d5745 p := by
  change (if p 162 then d2796 (change p 225 none) else d2793 (change p 225 none)) = d5745 p
  rw [sub9956, sub9953]
  rfl
theorem sub9958 (p : Pattern) : d2798 (change p 225 none) = d5746 p := by
  change (if p 163 then d2795 (change p 225 none) else d2588 (change p 225 none)) = d5746 p
  rw [sub9955, sub9722]
  rfl
theorem sub9959 (p : Pattern) : d2799 (change p 225 none) = d5747 p := by
  change (if p 162 then d2595 (change p 225 none) else d2798 (change p 225 none)) = d5747 p
  rw [sub9729, sub9958]
  rfl
end NetHack.Sokoban22Refined85
