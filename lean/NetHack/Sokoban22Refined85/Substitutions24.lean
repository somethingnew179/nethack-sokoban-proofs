/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2880 (p : Pattern) : d271 (change p 138 (some 160)) = d271 p := by
  change (if p 163 then d270 (change p 138 (some 160)) else d269 (change p 138 (some 160))) = d271 p
  rw [sub2879, sub2878]
  rfl
theorem sub2881 (p : Pattern) : d272 (change p 138 (some 160)) = d272 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d268 (change p 138 (some 160))) = d272 p
  rw [sub2678, sub2877]
  rfl
theorem sub2882 (p : Pattern) : d273 (change p 138 (some 160)) = d273 p := by
  change (if p 204 then d120 (change p 138 (some 160)) else d107 (change p 138 (some 160))) = d273 p
  rw [sub2784, sub2791]
  rfl
theorem sub2883 (p : Pattern) : d274 (change p 138 (some 160)) = d274 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d273 (change p 138 (some 160))) = d274 p
  rw [sub2678, sub2882]
  rfl
theorem sub2884 (p : Pattern) : d275 (change p 138 (some 160)) = d275 p := by
  change (if p 163 then d274 (change p 138 (some 160)) else d272 (change p 138 (some 160))) = d275 p
  rw [sub2883, sub2881]
  rfl
theorem sub2885 (p : Pattern) : d276 (change p 138 (some 160)) = d276 p := by
  change (if p 162 then d275 (change p 138 (some 160)) else d271 (change p 138 (some 160))) = d276 p
  rw [sub2884, sub2880]
  rfl
theorem sub2886 (p : Pattern) : d279 (change p 138 (some 160)) = d279 p := by
  change (if p 162 then d278 (change p 138 (some 160)) else d275 (change p 138 (some 160))) = d279 p
  rw [sub2818, sub2884]
  rfl
theorem sub2887 (p : Pattern) : d280 (change p 138 (some 160)) = d280 p := by
  change (if p 161 then d279 (change p 138 (some 160)) else d276 (change p 138 (some 160))) = d280 p
  rw [sub2886, sub2885]
  rfl
theorem sub2888 (p : Pattern) : d281 (change p 138 (some 160)) = d280 p := by
  change d280 (change p 138 (some 160)) = d280 p
  exact sub2887 p
theorem sub2889 (p : Pattern) : d282 (change p 138 (some 160)) = d282 p := by
  change (if p 204 then d107 (change p 138 (some 160)) else d116 (change p 138 (some 160))) = d282 p
  rw [sub2791, sub2779]
  rfl
theorem sub2890 (p : Pattern) : d283 (change p 138 (some 160)) = d283 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d282 (change p 138 (some 160))) = d283 p
  rw [sub2678, sub2889]
  rfl
theorem sub2891 (p : Pattern) : d284 (change p 138 (some 160)) = d284 p := by
  change (if p 163 then d283 (change p 138 (some 160)) else d270 (change p 138 (some 160))) = d284 p
  rw [sub2890, sub2879]
  rfl
theorem sub2892 (p : Pattern) : d285 (change p 138 (some 160)) = d285 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d274 (change p 138 (some 160))) = d285 p
  rw [sub2678, sub2883]
  rfl
theorem sub2893 (p : Pattern) : d286 (change p 138 (some 160)) = d286 p := by
  change (if p 162 then d285 (change p 138 (some 160)) else d284 (change p 138 (some 160))) = d286 p
  rw [sub2892, sub2891]
  rfl
theorem sub2894 (p : Pattern) : d287 (change p 138 (some 160)) = d287 p := by
  change (if p 162 then d12 (change p 138 (some 160)) else d285 (change p 138 (some 160))) = d287 p
  rw [sub2678, sub2892]
  rfl
theorem sub2895 (p : Pattern) : d288 (change p 138 (some 160)) = d288 p := by
  change (if p 161 then d287 (change p 138 (some 160)) else d286 (change p 138 (some 160))) = d288 p
  rw [sub2894, sub2893]
  rfl
theorem sub2896 (p : Pattern) : d289 (change p 138 (some 160)) = d288 p := by
  change d288 (change p 138 (some 160)) = d288 p
  exact sub2895 p
theorem sub2897 (p : Pattern) : d290 (change p 138 (some 160)) = d4135 p := by
  change (if p 141 then d289 (change p 138 (some 160)) else d281 (change p 138 (some 160))) = d4135 p
  rw [sub2896, sub2888]
  rfl
theorem sub2898 (p : Pattern) : d619 (change p 138 (some 160)) = d4135 p := by
  change d290 (change p 138 (some 160)) = d4135 p
  exact sub2897 p
theorem sub2899 (p : Pattern) : d620 (change p 138 (some 160)) = d620 p := by
  change (if p 204 then d120 (change p 138 (some 160)) else d103 (change p 138 (some 160))) = d620 p
  rw [sub2784, sub2776]
  rfl
theorem sub2900 (p : Pattern) : d621 (change p 138 (some 160)) = d621 p := by
  change (if p 182 then d121 (change p 138 (some 160)) else d620 (change p 138 (some 160))) = d621 p
  rw [sub2785, sub2899]
  rfl
theorem sub2901 (p : Pattern) : d622 (change p 138 (some 160)) = d622 p := by
  change (if p 182 then d41 (change p 138 (some 160)) else d620 (change p 138 (some 160))) = d622 p
  rw [sub2695, sub2899]
  rfl
theorem sub2902 (p : Pattern) : d623 (change p 138 (some 160)) = d623 p := by
  change (if p 163 then d622 (change p 138 (some 160)) else d621 (change p 138 (some 160))) = d623 p
  rw [sub2901, sub2900]
  rfl
theorem sub2903 (p : Pattern) : d624 (change p 138 (some 160)) = d624 p := by
  change (if p 204 then d40 (change p 138 (some 160)) else d24 (change p 138 (some 160))) = d624 p
  rw [sub2694, sub2707]
  rfl
theorem sub2904 (p : Pattern) : d625 (change p 138 (some 160)) = d625 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d624 (change p 138 (some 160))) = d625 p
  rw [sub2678, sub2903]
  rfl
theorem sub2905 (p : Pattern) : d626 (change p 138 (some 160)) = d626 p := by
  change (if p 163 then d625 (change p 138 (some 160)) else d571 (change p 138 (some 160))) = d626 p
  rw [sub2904, sub2823]
  rfl
theorem sub2906 (p : Pattern) : d627 (change p 138 (some 160)) = d627 p := by
  change (if p 162 then d626 (change p 138 (some 160)) else d623 (change p 138 (some 160))) = d627 p
  rw [sub2905, sub2902]
  rfl
theorem sub2907 (p : Pattern) : d628 (change p 138 (some 160)) = d628 p := by
  change (if p 163 then d625 (change p 138 (some 160)) else d274 (change p 138 (some 160))) = d628 p
  rw [sub2904, sub2883]
  rfl
theorem sub2908 (p : Pattern) : d629 (change p 138 (some 160)) = d629 p := by
  change (if p 162 then d12 (change p 138 (some 160)) else d628 (change p 138 (some 160))) = d629 p
  rw [sub2678, sub2907]
  rfl
theorem sub2909 (p : Pattern) : d630 (change p 138 (some 160)) = d630 p := by
  change (if p 161 then d629 (change p 138 (some 160)) else d627 (change p 138 (some 160))) = d630 p
  rw [sub2908, sub2906]
  rfl
theorem sub2910 (p : Pattern) : d631 (change p 138 (some 160)) = d630 p := by
  change d630 (change p 138 (some 160)) = d630 p
  exact sub2909 p
theorem sub2911 (p : Pattern) : d632 (change p 138 (some 160)) = d632 p := by
  change (if p 182 then d41 (change p 138 (some 160)) else d570 (change p 138 (some 160))) = d632 p
  rw [sub2695, sub2822]
  rfl
theorem sub2912 (p : Pattern) : d633 (change p 138 (some 160)) = d633 p := by
  change (if p 204 then d24 (change p 138 (some 160)) else d116 (change p 138 (some 160))) = d633 p
  rw [sub2707, sub2779]
  rfl
theorem sub2913 (p : Pattern) : d634 (change p 138 (some 160)) = d634 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d633 (change p 138 (some 160))) = d634 p
  rw [sub2678, sub2912]
  rfl
theorem sub2914 (p : Pattern) : d635 (change p 138 (some 160)) = d635 p := by
  change (if p 163 then d634 (change p 138 (some 160)) else d632 (change p 138 (some 160))) = d635 p
  rw [sub2913, sub2911]
  rfl
theorem sub2915 (p : Pattern) : d636 (change p 138 (some 160)) = d636 p := by
  change (if p 204 then d40 (change p 138 (some 160)) else d107 (change p 138 (some 160))) = d636 p
  rw [sub2694, sub2791]
  rfl
theorem sub2916 (p : Pattern) : d637 (change p 138 (some 160)) = d637 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d636 (change p 138 (some 160))) = d637 p
  rw [sub2678, sub2915]
  rfl
theorem sub2917 (p : Pattern) : d638 (change p 138 (some 160)) = d638 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d637 (change p 138 (some 160))) = d638 p
  rw [sub2678, sub2916]
  rfl
theorem sub2918 (p : Pattern) : d639 (change p 138 (some 160)) = d639 p := by
  change (if p 162 then d638 (change p 138 (some 160)) else d635 (change p 138 (some 160))) = d639 p
  rw [sub2917, sub2914]
  rfl
theorem sub2919 (p : Pattern) : d640 (change p 138 (some 160)) = d640 p := by
  change (if p 204 then d40 (change p 138 (some 160)) else d120 (change p 138 (some 160))) = d640 p
  rw [sub2694, sub2784]
  rfl
theorem sub2920 (p : Pattern) : d641 (change p 138 (some 160)) = d641 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d640 (change p 138 (some 160))) = d641 p
  rw [sub2678, sub2919]
  rfl
theorem sub2921 (p : Pattern) : d642 (change p 138 (some 160)) = d642 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d641 (change p 138 (some 160))) = d642 p
  rw [sub2678, sub2920]
  rfl
theorem sub2922 (p : Pattern) : d643 (change p 138 (some 160)) = d643 p := by
  change (if p 162 then d12 (change p 138 (some 160)) else d642 (change p 138 (some 160))) = d643 p
  rw [sub2678, sub2921]
  rfl
theorem sub2923 (p : Pattern) : d644 (change p 138 (some 160)) = d644 p := by
  change (if p 161 then d643 (change p 138 (some 160)) else d639 (change p 138 (some 160))) = d644 p
  rw [sub2922, sub2918]
  rfl
theorem sub2924 (p : Pattern) : d645 (change p 138 (some 160)) = d644 p := by
  change d644 (change p 138 (some 160)) = d644 p
  exact sub2923 p
theorem sub2925 (p : Pattern) : d646 (change p 138 (some 160)) = d4136 p := by
  change (if p 141 then d645 (change p 138 (some 160)) else d631 (change p 138 (some 160))) = d4136 p
  rw [sub2924, sub2910]
  rfl
theorem sub2926 (p : Pattern) : d647 (change p 138 (some 160)) = d4136 p := by
  change d646 (change p 138 (some 160)) = d4136 p
  exact sub2925 p
theorem sub2927 (p : Pattern) : d648 (change p 138 (some 160)) = d4137 p := by
  change (if p 116 then d647 (change p 138 (some 160)) else d619 (change p 138 (some 160))) = d4137 p
  rw [sub2926, sub2898]
  rfl
theorem sub2928 (p : Pattern) : d649 (change p 138 (some 160)) = d4138 p := by
  change (if p 115 then d648 (change p 138 (some 160)) else d618 (change p 138 (some 160))) = d4138 p
  rw [sub2927, sub2876]
  rfl
theorem sub2929 (p : Pattern) : d650 (change p 138 (some 160)) = d4139 p := by
  change (if p 71 then d649 (change p 138 (some 160)) else d549 (change p 138 (some 160))) = d4139 p
  rw [sub2928, sub2766]
  rfl
theorem sub2930 (p : Pattern) : d651 (change p 138 (some 160)) = d4140 p := by
  change (if p 49 then d650 (change p 138 (some 160)) else d609 (change p 138 (some 160))) = d4140 p
  rw [sub2929, sub2861]
  rfl
theorem sub2931 (p : Pattern) : d652 (change p 138 (some 160)) = d4141 p := by
  change (if p 48 then d651 (change p 138 (some 160)) else d587 (change p 138 (some 160))) = d4141 p
  rw [sub2930, sub2839]
  rfl
theorem sub2932 (p : Pattern) : d0 (change p 115 none) = d0 p := by
  rfl
theorem sub2933 (p : Pattern) : d12 (change p 115 none) = d12 p := by
  rfl
theorem sub2934 (p : Pattern) : d13 (change p 115 none) = d13 p := by
  change (if p 247 then d12 (change p 115 none) else d0 (change p 115 none)) = d13 p
  rw [sub2933, sub2932]
  rfl
theorem sub2935 (p : Pattern) : d14 (change p 115 none) = d14 p := by
  change (if p 246 then d13 (change p 115 none) else d0 (change p 115 none)) = d14 p
  rw [sub2934, sub2932]
  rfl
theorem sub2936 (p : Pattern) : d15 (change p 115 none) = d15 p := by
  change (if p 204 then d12 (change p 115 none) else d14 (change p 115 none)) = d15 p
  rw [sub2933, sub2935]
  rfl
theorem sub2937 (p : Pattern) : d16 (change p 115 none) = d16 p := by
  change (if p 182 then d15 (change p 115 none) else d14 (change p 115 none)) = d16 p
  rw [sub2936, sub2935]
  rfl
theorem sub2938 (p : Pattern) : d4 (change p 115 none) = d4 p := by
  rfl
theorem sub2939 (p : Pattern) : d17 (change p 115 none) = d17 p := by
  change (if p 247 then d12 (change p 115 none) else d4 (change p 115 none)) = d17 p
  rw [sub2933, sub2938]
  rfl
theorem sub2940 (p : Pattern) : d18 (change p 115 none) = d18 p := by
  change (if p 246 then d17 (change p 115 none) else d4 (change p 115 none)) = d18 p
  rw [sub2939, sub2938]
  rfl
theorem sub2941 (p : Pattern) : d19 (change p 115 none) = d19 p := by
  change (if p 204 then d12 (change p 115 none) else d18 (change p 115 none)) = d19 p
  rw [sub2933, sub2940]
  rfl
theorem sub2942 (p : Pattern) : d20 (change p 115 none) = d20 p := by
  change (if p 182 then d19 (change p 115 none) else d18 (change p 115 none)) = d20 p
  rw [sub2941, sub2940]
  rfl
theorem sub2943 (p : Pattern) : d21 (change p 115 none) = d21 p := by
  change (if p 163 then d20 (change p 115 none) else d16 (change p 115 none)) = d21 p
  rw [sub2942, sub2937]
  rfl
theorem sub2944 (p : Pattern) : d22 (change p 115 none) = d22 p := by
  change (if p 162 then d21 (change p 115 none) else d16 (change p 115 none)) = d22 p
  rw [sub2943, sub2937]
  rfl
theorem sub2945 (p : Pattern) : d9 (change p 115 none) = d9 p := by
  rfl
theorem sub2946 (p : Pattern) : d23 (change p 115 none) = d23 p := by
  change (if p 247 then d12 (change p 115 none) else d9 (change p 115 none)) = d23 p
  rw [sub2933, sub2945]
  rfl
theorem sub2947 (p : Pattern) : d24 (change p 115 none) = d24 p := by
  change (if p 246 then d23 (change p 115 none) else d9 (change p 115 none)) = d24 p
  rw [sub2946, sub2945]
  rfl
theorem sub2948 (p : Pattern) : d25 (change p 115 none) = d25 p := by
  change (if p 204 then d12 (change p 115 none) else d24 (change p 115 none)) = d25 p
  rw [sub2933, sub2947]
  rfl
theorem sub2949 (p : Pattern) : d26 (change p 115 none) = d26 p := by
  change (if p 182 then d25 (change p 115 none) else d24 (change p 115 none)) = d26 p
  rw [sub2948, sub2947]
  rfl
theorem sub2950 (p : Pattern) : d27 (change p 115 none) = d27 p := by
  change (if p 163 then d12 (change p 115 none) else d26 (change p 115 none)) = d27 p
  rw [sub2933, sub2949]
  rfl
theorem sub2951 (p : Pattern) : d28 (change p 115 none) = d28 p := by
  change (if p 162 then d27 (change p 115 none) else d21 (change p 115 none)) = d28 p
  rw [sub2950, sub2943]
  rfl
theorem sub2952 (p : Pattern) : d29 (change p 115 none) = d29 p := by
  change (if p 161 then d28 (change p 115 none) else d22 (change p 115 none)) = d29 p
  rw [sub2951, sub2944]
  rfl
theorem sub2953 (p : Pattern) : d2 (change p 115 none) = d2 p := by
  rfl
theorem sub2954 (p : Pattern) : d30 (change p 115 none) = d30 p := by
  change (if p 247 then d12 (change p 115 none) else d2 (change p 115 none)) = d30 p
  rw [sub2933, sub2953]
  rfl
theorem sub2955 (p : Pattern) : d31 (change p 115 none) = d31 p := by
  change (if p 246 then d30 (change p 115 none) else d2 (change p 115 none)) = d31 p
  rw [sub2954, sub2953]
  rfl
theorem sub2956 (p : Pattern) : d32 (change p 115 none) = d32 p := by
  change (if p 204 then d12 (change p 115 none) else d31 (change p 115 none)) = d32 p
  rw [sub2933, sub2955]
  rfl
theorem sub2957 (p : Pattern) : d33 (change p 115 none) = d33 p := by
  change (if p 182 then d32 (change p 115 none) else d14 (change p 115 none)) = d33 p
  rw [sub2956, sub2935]
  rfl
theorem sub2958 (p : Pattern) : d6 (change p 115 none) = d6 p := by
  rfl
theorem sub2959 (p : Pattern) : d34 (change p 115 none) = d34 p := by
  change (if p 247 then d12 (change p 115 none) else d6 (change p 115 none)) = d34 p
  rw [sub2933, sub2958]
  rfl
theorem sub2960 (p : Pattern) : d35 (change p 115 none) = d35 p := by
  change (if p 246 then d34 (change p 115 none) else d6 (change p 115 none)) = d35 p
  rw [sub2959, sub2958]
  rfl
theorem sub2961 (p : Pattern) : d36 (change p 115 none) = d36 p := by
  change (if p 204 then d12 (change p 115 none) else d35 (change p 115 none)) = d36 p
  rw [sub2933, sub2960]
  rfl
theorem sub2962 (p : Pattern) : d37 (change p 115 none) = d37 p := by
  change (if p 182 then d36 (change p 115 none) else d14 (change p 115 none)) = d37 p
  rw [sub2961, sub2935]
  rfl
theorem sub2963 (p : Pattern) : d38 (change p 115 none) = d38 p := by
  change (if p 163 then d37 (change p 115 none) else d33 (change p 115 none)) = d38 p
  rw [sub2962, sub2957]
  rfl
theorem sub2964 (p : Pattern) : d11 (change p 115 none) = d11 p := by
  rfl
theorem sub2965 (p : Pattern) : d39 (change p 115 none) = d39 p := by
  change (if p 247 then d12 (change p 115 none) else d11 (change p 115 none)) = d39 p
  rw [sub2933, sub2964]
  rfl
theorem sub2966 (p : Pattern) : d40 (change p 115 none) = d40 p := by
  change (if p 246 then d39 (change p 115 none) else d11 (change p 115 none)) = d40 p
  rw [sub2965, sub2964]
  rfl
theorem sub2967 (p : Pattern) : d41 (change p 115 none) = d41 p := by
  change (if p 204 then d12 (change p 115 none) else d40 (change p 115 none)) = d41 p
  rw [sub2933, sub2966]
  rfl
theorem sub2968 (p : Pattern) : d42 (change p 115 none) = d42 p := by
  change (if p 182 then d41 (change p 115 none) else d14 (change p 115 none)) = d42 p
  rw [sub2967, sub2935]
  rfl
theorem sub2969 (p : Pattern) : d43 (change p 115 none) = d43 p := by
  change (if p 182 then d12 (change p 115 none) else d18 (change p 115 none)) = d43 p
  rw [sub2933, sub2940]
  rfl
theorem sub2970 (p : Pattern) : d44 (change p 115 none) = d44 p := by
  change (if p 163 then d43 (change p 115 none) else d42 (change p 115 none)) = d44 p
  rw [sub2969, sub2968]
  rfl
theorem sub2971 (p : Pattern) : d45 (change p 115 none) = d45 p := by
  change (if p 162 then d44 (change p 115 none) else d38 (change p 115 none)) = d45 p
  rw [sub2970, sub2963]
  rfl
theorem sub2972 (p : Pattern) : d46 (change p 115 none) = d46 p := by
  change (if p 182 then d12 (change p 115 none) else d14 (change p 115 none)) = d46 p
  rw [sub2933, sub2935]
  rfl
theorem sub2973 (p : Pattern) : d47 (change p 115 none) = d47 p := by
  change (if p 163 then d43 (change p 115 none) else d46 (change p 115 none)) = d47 p
  rw [sub2969, sub2972]
  rfl
theorem sub2974 (p : Pattern) : d48 (change p 115 none) = d48 p := by
  change (if p 182 then d12 (change p 115 none) else d24 (change p 115 none)) = d48 p
  rw [sub2933, sub2947]
  rfl
theorem sub2975 (p : Pattern) : d49 (change p 115 none) = d49 p := by
  change (if p 163 then d12 (change p 115 none) else d48 (change p 115 none)) = d49 p
  rw [sub2933, sub2974]
  rfl
theorem sub2976 (p : Pattern) : d50 (change p 115 none) = d50 p := by
  change (if p 162 then d49 (change p 115 none) else d47 (change p 115 none)) = d50 p
  rw [sub2975, sub2973]
  rfl
theorem sub2977 (p : Pattern) : d51 (change p 115 none) = d51 p := by
  change (if p 161 then d50 (change p 115 none) else d45 (change p 115 none)) = d51 p
  rw [sub2976, sub2971]
  rfl
theorem sub2978 (p : Pattern) : d52 (change p 115 none) = d52 p := by
  change (if p 160 then d51 (change p 115 none) else d29 (change p 115 none)) = d52 p
  rw [sub2977, sub2952]
  rfl
theorem sub2979 (p : Pattern) : d53 (change p 115 none) = d53 p := by
  change (if p 182 then d32 (change p 115 none) else d31 (change p 115 none)) = d53 p
  rw [sub2956, sub2955]
  rfl
theorem sub2980 (p : Pattern) : d54 (change p 115 none) = d54 p := by
  change (if p 163 then d53 (change p 115 none) else d16 (change p 115 none)) = d54 p
  rw [sub2979, sub2937]
  rfl
theorem sub2981 (p : Pattern) : d55 (change p 115 none) = d55 p := by
  change (if p 163 then d26 (change p 115 none) else d20 (change p 115 none)) = d55 p
  rw [sub2949, sub2942]
  rfl
theorem sub2982 (p : Pattern) : d56 (change p 115 none) = d56 p := by
  change (if p 162 then d55 (change p 115 none) else d54 (change p 115 none)) = d56 p
  rw [sub2981, sub2980]
  rfl
theorem sub2983 (p : Pattern) : d10 (change p 115 none) = d10 p := by
  rfl
theorem sub2984 (p : Pattern) : d57 (change p 115 none) = d57 p := by
  change (if p 247 then d12 (change p 115 none) else d10 (change p 115 none)) = d57 p
  rw [sub2933, sub2983]
  rfl
theorem sub2985 (p : Pattern) : d58 (change p 115 none) = d58 p := by
  change (if p 246 then d57 (change p 115 none) else d10 (change p 115 none)) = d58 p
  rw [sub2984, sub2983]
  rfl
theorem sub2986 (p : Pattern) : d59 (change p 115 none) = d59 p := by
  change (if p 204 then d12 (change p 115 none) else d58 (change p 115 none)) = d59 p
  rw [sub2933, sub2985]
  rfl
theorem sub2987 (p : Pattern) : d60 (change p 115 none) = d60 p := by
  change (if p 182 then d59 (change p 115 none) else d58 (change p 115 none)) = d60 p
  rw [sub2986, sub2985]
  rfl
theorem sub2988 (p : Pattern) : d61 (change p 115 none) = d61 p := by
  change (if p 163 then d60 (change p 115 none) else d20 (change p 115 none)) = d61 p
  rw [sub2987, sub2942]
  rfl
theorem sub2989 (p : Pattern) : d62 (change p 115 none) = d62 p := by
  change (if p 182 then d41 (change p 115 none) else d40 (change p 115 none)) = d62 p
  rw [sub2967, sub2966]
  rfl
theorem sub2990 (p : Pattern) : d63 (change p 115 none) = d63 p := by
  change (if p 163 then d12 (change p 115 none) else d62 (change p 115 none)) = d63 p
  rw [sub2933, sub2989]
  rfl
theorem sub2991 (p : Pattern) : d64 (change p 115 none) = d64 p := by
  change (if p 162 then d63 (change p 115 none) else d61 (change p 115 none)) = d64 p
  rw [sub2990, sub2988]
  rfl
theorem sub2992 (p : Pattern) : d65 (change p 115 none) = d65 p := by
  change (if p 161 then d64 (change p 115 none) else d56 (change p 115 none)) = d65 p
  rw [sub2991, sub2982]
  rfl
theorem sub2993 (p : Pattern) : d66 (change p 115 none) = d66 p := by
  change (if p 182 then d12 (change p 115 none) else d31 (change p 115 none)) = d66 p
  rw [sub2933, sub2955]
  rfl
theorem sub2994 (p : Pattern) : d67 (change p 115 none) = d67 p := by
  change (if p 163 then d66 (change p 115 none) else d37 (change p 115 none)) = d67 p
  rw [sub2993, sub2962]
  rfl
theorem sub2995 (p : Pattern) : d68 (change p 115 none) = d68 p := by
  change (if p 163 then d48 (change p 115 none) else d43 (change p 115 none)) = d68 p
  rw [sub2974, sub2969]
  rfl
theorem sub2996 (p : Pattern) : d69 (change p 115 none) = d69 p := by
  change (if p 162 then d68 (change p 115 none) else d67 (change p 115 none)) = d69 p
  rw [sub2995, sub2994]
  rfl
theorem sub2997 (p : Pattern) : d70 (change p 115 none) = d70 p := by
  change (if p 182 then d12 (change p 115 none) else d58 (change p 115 none)) = d70 p
  rw [sub2933, sub2985]
  rfl
theorem sub2998 (p : Pattern) : d71 (change p 115 none) = d71 p := by
  change (if p 163 then d70 (change p 115 none) else d43 (change p 115 none)) = d71 p
  rw [sub2997, sub2969]
  rfl
theorem sub2999 (p : Pattern) : d72 (change p 115 none) = d72 p := by
  change (if p 182 then d12 (change p 115 none) else d40 (change p 115 none)) = d72 p
  rw [sub2933, sub2966]
  rfl
end NetHack.Sokoban22Refined85
