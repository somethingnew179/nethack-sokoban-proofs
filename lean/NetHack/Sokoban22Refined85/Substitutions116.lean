/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions115
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub13920 (p : Pattern) : d1904 (change p 10000 (some 247)) = d7702 p := by
  change (if p 225 then d317 (change p 10000 (some 247)) else d1903 (change p 10000 (some 247))) = d7702 p
  rw [sub13916, sub13919]
  rfl
theorem sub13921 (p : Pattern) : d1905 (change p 10000 (some 247)) = d7834 p := by
  change (if p 224 then d1904 (change p 10000 (some 247)) else d1901 (change p 10000 (some 247))) = d7834 p
  rw [sub13920, sub13917]
  rfl
theorem sub13922 (p : Pattern) : d1906 (change p 10000 (some 247)) = d7835 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1905 (change p 10000 (some 247))) = d7835 p
  rw [sub13654, sub13921]
  rfl
theorem sub13923 (p : Pattern) : d3004 (change p 10000 (some 247)) = d7836 p := by
  change (if p 182 then d1906 (change p 10000 (some 247)) else d3002 (change p 10000 (some 247))) = d7836 p
  rw [sub13922, sub13903]
  rfl
theorem sub13924 (p : Pattern) : d3005 (change p 10000 (some 247)) = d7837 p := by
  change (if p 163 then d3004 (change p 10000 (some 247)) else d3003 (change p 10000 (some 247))) = d7837 p
  rw [sub13923, sub13914]
  rfl
theorem sub13925 (p : Pattern) : d3006 (change p 10000 (some 247)) = d7838 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d3002 (change p 10000 (some 247))) = d7838 p
  rw [sub13654, sub13903]
  rfl
theorem sub13926 (p : Pattern) : d1960 (change p 10000 (some 247)) = d11 p := by
  change d11 (change p 10000 (some 247)) = d11 p
  exact sub13697 p
theorem sub13927 (p : Pattern) : d1961 (change p 10000 (some 247)) = d3257 p := by
  change (if p 246 then d39 (change p 10000 (some 247)) else d1960 (change p 10000 (some 247))) = d3257 p
  rw [sub13699, sub13926]
  rfl
theorem sub13928 (p : Pattern) : d1962 (change p 10000 (some 247)) = d7839 p := by
  change (if p 225 then d1961 (change p 10000 (some 247)) else d107 (change p 10000 (some 247))) = d7839 p
  rw [sub13927, sub13878]
  rfl
theorem sub13929 (p : Pattern) : d348 (change p 10000 (some 247)) = d12 p := by
  change (if p 246 then d12 (change p 10000 (some 247)) else d106 (change p 10000 (some 247))) = d12 p
  rw [sub13654, sub13865]
  simp only [ite_self]
theorem sub13930 (p : Pattern) : d1965 (change p 10000 (some 247)) = d7678 p := by
  change (if p 225 then d348 (change p 10000 (some 247)) else d1964 (change p 10000 (some 247))) = d7678 p
  rw [sub13929, sub13880]
  rfl
theorem sub13931 (p : Pattern) : d1966 (change p 10000 (some 247)) = d7840 p := by
  change (if p 224 then d1965 (change p 10000 (some 247)) else d1962 (change p 10000 (some 247))) = d7840 p
  rw [sub13930, sub13928]
  rfl
theorem sub13932 (p : Pattern) : d3007 (change p 10000 (some 247)) = d7841 p := by
  change (if p 204 then d1966 (change p 10000 (some 247)) else d107 (change p 10000 (some 247))) = d7841 p
  rw [sub13931, sub13878]
  rfl
theorem sub13933 (p : Pattern) : d3008 (change p 10000 (some 247)) = d7842 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d3007 (change p 10000 (some 247))) = d7842 p
  rw [sub13654, sub13932]
  rfl
theorem sub13934 (p : Pattern) : d3009 (change p 10000 (some 247)) = d7843 p := by
  change (if p 163 then d3008 (change p 10000 (some 247)) else d3006 (change p 10000 (some 247))) = d7843 p
  rw [sub13933, sub13925]
  rfl
theorem sub13935 (p : Pattern) : d3010 (change p 10000 (some 247)) = d7844 p := by
  change (if p 162 then d3009 (change p 10000 (some 247)) else d3005 (change p 10000 (some 247))) = d7844 p
  rw [sub13934, sub13924]
  rfl
theorem sub13936 (p : Pattern) : d3011 (change p 10000 (some 247)) = d7845 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d2940 (change p 10000 (some 247))) = d7845 p
  rw [sub13654, sub13792]
  rfl
theorem sub13937 (p : Pattern) : d3012 (change p 10000 (some 247)) = d7846 p := by
  change (if p 162 then d3011 (change p 10000 (some 247)) else d3009 (change p 10000 (some 247))) = d7846 p
  rw [sub13936, sub13934]
  rfl
theorem sub13938 (p : Pattern) : d3013 (change p 10000 (some 247)) = d7847 p := by
  change (if p 161 then d3012 (change p 10000 (some 247)) else d3010 (change p 10000 (some 247))) = d7847 p
  rw [sub13937, sub13935]
  rfl
theorem sub13939 (p : Pattern) : d3014 (change p 10000 (some 247)) = d7848 p := by
  change (if p 160 then d3013 (change p 10000 (some 247)) else d3001 (change p 10000 (some 247))) = d7848 p
  rw [sub13938, sub13896]
  rfl
theorem sub13940 (p : Pattern) : d2124 (change p 10000 (some 247)) = d7849 p := by
  change (if p 225 then d1895 (change p 10000 (some 247)) else d116 (change p 10000 (some 247))) = d7849 p
  rw [sub13909, sub13904]
  rfl
theorem sub13941 (p : Pattern) : d2125 (change p 10000 (some 247)) = d7850 p := by
  change (if p 224 then d1895 (change p 10000 (some 247)) else d2124 (change p 10000 (some 247))) = d7850 p
  rw [sub13909, sub13940]
  rfl
theorem sub13942 (p : Pattern) : d3015 (change p 10000 (some 247)) = d7851 p := by
  change (if p 204 then d2125 (change p 10000 (some 247)) else d116 (change p 10000 (some 247))) = d7851 p
  rw [sub13941, sub13904]
  rfl
theorem sub13943 (p : Pattern) : d1918 (change p 10000 (some 247)) = d5 p := by
  change d5 (change p 10000 (some 247)) = d5 p
  exact sub13863 p
theorem sub13944 (p : Pattern) : d1919 (change p 10000 (some 247)) = d3366 p := by
  change (if p 246 then d106 (change p 10000 (some 247)) else d1918 (change p 10000 (some 247))) = d3366 p
  rw [sub13865, sub13943]
  rfl
theorem sub13945 (p : Pattern) : d1920 (change p 10000 (some 247)) = d7852 p := by
  change (if p 225 then d1919 (change p 10000 (some 247)) else d116 (change p 10000 (some 247))) = d7852 p
  rw [sub13944, sub13904]
  rfl
theorem sub13946 (p : Pattern) : d1921 (change p 10000 (some 247)) = d7853 p := by
  change (if p 224 then d1919 (change p 10000 (some 247)) else d1920 (change p 10000 (some 247))) = d7853 p
  rw [sub13944, sub13945]
  rfl
theorem sub13947 (p : Pattern) : d1922 (change p 10000 (some 247)) = d7854 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1921 (change p 10000 (some 247))) = d7854 p
  rw [sub13654, sub13946]
  rfl
theorem sub13948 (p : Pattern) : d3016 (change p 10000 (some 247)) = d7855 p := by
  change (if p 182 then d1922 (change p 10000 (some 247)) else d3015 (change p 10000 (some 247))) = d7855 p
  rw [sub13947, sub13942]
  rfl
theorem sub13949 (p : Pattern) : d3017 (change p 10000 (some 247)) = d7856 p := by
  change (if p 163 then d3016 (change p 10000 (some 247)) else d2994 (change p 10000 (some 247))) = d7856 p
  rw [sub13948, sub13877]
  rfl
theorem sub13950 (p : Pattern) : d3018 (change p 10000 (some 247)) = d7857 p := by
  change (if p 163 then d2928 (change p 10000 (some 247)) else d2996 (change p 10000 (some 247))) = d7857 p
  rw [sub13780, sub13891]
  rfl
theorem sub13951 (p : Pattern) : d3019 (change p 10000 (some 247)) = d7858 p := by
  change (if p 162 then d3018 (change p 10000 (some 247)) else d3017 (change p 10000 (some 247))) = d7858 p
  rw [sub13950, sub13949]
  rfl
theorem sub13952 (p : Pattern) : d3020 (change p 10000 (some 247)) = d7859 p := by
  change (if p 163 then d2931 (change p 10000 (some 247)) else d2996 (change p 10000 (some 247))) = d7859 p
  rw [sub13783, sub13891]
  rfl
theorem sub13953 (p : Pattern) : d3021 (change p 10000 (some 247)) = d7860 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3020 (change p 10000 (some 247))) = d7860 p
  rw [sub13654, sub13952]
  rfl
theorem sub13954 (p : Pattern) : d3022 (change p 10000 (some 247)) = d7861 p := by
  change (if p 161 then d3021 (change p 10000 (some 247)) else d3019 (change p 10000 (some 247))) = d7861 p
  rw [sub13953, sub13951]
  rfl
theorem sub13955 (p : Pattern) : d3023 (change p 10000 (some 247)) = d7862 p := by
  change (if p 204 then d1898 (change p 10000 (some 247)) else d116 (change p 10000 (some 247))) = d7862 p
  rw [sub13912, sub13904]
  rfl
theorem sub13956 (p : Pattern) : d3024 (change p 10000 (some 247)) = d7863 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d3023 (change p 10000 (some 247))) = d7863 p
  rw [sub13654, sub13955]
  rfl
theorem sub13957 (p : Pattern) : d3025 (change p 10000 (some 247)) = d7864 p := by
  change (if p 163 then d3024 (change p 10000 (some 247)) else d3004 (change p 10000 (some 247))) = d7864 p
  rw [sub13956, sub13923]
  rfl
theorem sub13958 (p : Pattern) : d3026 (change p 10000 (some 247)) = d7865 p := by
  change (if p 163 then d2940 (change p 10000 (some 247)) else d3008 (change p 10000 (some 247))) = d7865 p
  rw [sub13792, sub13933]
  rfl
theorem sub13959 (p : Pattern) : d3027 (change p 10000 (some 247)) = d7866 p := by
  change (if p 162 then d3026 (change p 10000 (some 247)) else d3025 (change p 10000 (some 247))) = d7866 p
  rw [sub13958, sub13957]
  rfl
theorem sub13960 (p : Pattern) : d3028 (change p 10000 (some 247)) = d7867 p := by
  change (if p 163 then d2942 (change p 10000 (some 247)) else d3008 (change p 10000 (some 247))) = d7867 p
  rw [sub13794, sub13933]
  rfl
theorem sub13961 (p : Pattern) : d3029 (change p 10000 (some 247)) = d7868 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3028 (change p 10000 (some 247))) = d7868 p
  rw [sub13654, sub13960]
  rfl
theorem sub13962 (p : Pattern) : d3030 (change p 10000 (some 247)) = d7869 p := by
  change (if p 161 then d3029 (change p 10000 (some 247)) else d3027 (change p 10000 (some 247))) = d7869 p
  rw [sub13961, sub13959]
  rfl
theorem sub13963 (p : Pattern) : d3031 (change p 10000 (some 247)) = d7870 p := by
  change (if p 160 then d3030 (change p 10000 (some 247)) else d3022 (change p 10000 (some 247))) = d7870 p
  rw [sub13962, sub13954]
  rfl
theorem sub13964 (p : Pattern) : d3032 (change p 10000 (some 247)) = d7871 p := by
  change (if p 141 then d3031 (change p 10000 (some 247)) else d3014 (change p 10000 (some 247))) = d7871 p
  rw [sub13963, sub13939]
  rfl
theorem sub13965 (p : Pattern) : d2107 (change p 10000 (some 247)) = d7816 p := by
  change (if p 225 then d1946 (change p 10000 (some 247)) else d1940 (change p 10000 (some 247))) = d7816 p
  rw [sub13898, sub13866]
  rfl
theorem sub13966 (p : Pattern) : d2108 (change p 10000 (some 247)) = d7872 p := by
  change (if p 224 then d2107 (change p 10000 (some 247)) else d1947 (change p 10000 (some 247))) = d7872 p
  rw [sub13965, sub13899]
  rfl
theorem sub13967 (p : Pattern) : d3033 (change p 10000 (some 247)) = d7873 p := by
  change (if p 204 then d2108 (change p 10000 (some 247)) else d103 (change p 10000 (some 247))) = d7873 p
  rw [sub13966, sub13862]
  rfl
theorem sub13968 (p : Pattern) : d1943 (change p 10000 (some 247)) = d7874 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1942 (change p 10000 (some 247))) = d7874 p
  rw [sub13654, sub13868]
  rfl
theorem sub13969 (p : Pattern) : d3034 (change p 10000 (some 247)) = d7875 p := by
  change (if p 182 then d1943 (change p 10000 (some 247)) else d3033 (change p 10000 (some 247))) = d7875 p
  rw [sub13968, sub13967]
  rfl
theorem sub13970 (p : Pattern) : d3035 (change p 10000 (some 247)) = d11 p := by
  change d11 (change p 10000 (some 247)) = d11 p
  exact sub13697 p
theorem sub13971 (p : Pattern) : d3036 (change p 10000 (some 247)) = d3257 p := by
  change (if p 246 then d57 (change p 10000 (some 247)) else d3035 (change p 10000 (some 247))) = d3257 p
  rw [sub13732, sub13970]
  rfl
theorem sub13972 (p : Pattern) : d3037 (change p 10000 (some 247)) = d7839 p := by
  change (if p 225 then d3036 (change p 10000 (some 247)) else d1940 (change p 10000 (some 247))) = d7839 p
  rw [sub13971, sub13866]
  rfl
theorem sub13973 (p : Pattern) : d3038 (change p 10000 (some 247)) = d7876 p := by
  change (if p 224 then d3037 (change p 10000 (some 247)) else d1947 (change p 10000 (some 247))) = d7876 p
  rw [sub13972, sub13899]
  rfl
theorem sub13974 (p : Pattern) : d3039 (change p 10000 (some 247)) = d7877 p := by
  change (if p 204 then d3038 (change p 10000 (some 247)) else d103 (change p 10000 (some 247))) = d7877 p
  rw [sub13973, sub13862]
  rfl
theorem sub13975 (p : Pattern) : d1948 (change p 10000 (some 247)) = d9 p := by
  change d9 (change p 10000 (some 247)) = d9 p
  exact sub13690 p
theorem sub13976 (p : Pattern) : d1949 (change p 10000 (some 247)) = d3244 p := by
  change (if p 246 then d23 (change p 10000 (some 247)) else d1948 (change p 10000 (some 247))) = d3244 p
  rw [sub13691, sub13975]
  rfl
theorem sub13977 (p : Pattern) : d1950 (change p 10000 (some 247)) = d7813 p := by
  change (if p 225 then d1949 (change p 10000 (some 247)) else d1940 (change p 10000 (some 247))) = d7813 p
  rw [sub13976, sub13866]
  rfl
theorem sub13978 (p : Pattern) : d1951 (change p 10000 (some 247)) = d7878 p := by
  change (if p 224 then d1950 (change p 10000 (some 247)) else d1947 (change p 10000 (some 247))) = d7878 p
  rw [sub13977, sub13899]
  rfl
theorem sub13979 (p : Pattern) : d1952 (change p 10000 (some 247)) = d7879 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1951 (change p 10000 (some 247))) = d7879 p
  rw [sub13654, sub13978]
  rfl
theorem sub13980 (p : Pattern) : d3040 (change p 10000 (some 247)) = d7880 p := by
  change (if p 182 then d1952 (change p 10000 (some 247)) else d3039 (change p 10000 (some 247))) = d7880 p
  rw [sub13979, sub13974]
  rfl
theorem sub13981 (p : Pattern) : d3041 (change p 10000 (some 247)) = d7881 p := by
  change (if p 163 then d3040 (change p 10000 (some 247)) else d3034 (change p 10000 (some 247))) = d7881 p
  rw [sub13980, sub13969]
  rfl
theorem sub13982 (p : Pattern) : d1958 (change p 10000 (some 247)) = d7882 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1957 (change p 10000 (some 247))) = d7882 p
  rw [sub13654, sub13902]
  rfl
theorem sub13983 (p : Pattern) : d3042 (change p 10000 (some 247)) = d7883 p := by
  change (if p 182 then d1958 (change p 10000 (some 247)) else d3002 (change p 10000 (some 247))) = d7883 p
  rw [sub13982, sub13903]
  rfl
theorem sub13984 (p : Pattern) : d1967 (change p 10000 (some 247)) = d7884 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d1966 (change p 10000 (some 247))) = d7884 p
  rw [sub13654, sub13931]
  rfl
theorem sub13985 (p : Pattern) : d3043 (change p 10000 (some 247)) = d7885 p := by
  change (if p 182 then d1967 (change p 10000 (some 247)) else d3007 (change p 10000 (some 247))) = d7885 p
  rw [sub13984, sub13932]
  rfl
theorem sub13986 (p : Pattern) : d3044 (change p 10000 (some 247)) = d7886 p := by
  change (if p 163 then d3043 (change p 10000 (some 247)) else d3042 (change p 10000 (some 247))) = d7886 p
  rw [sub13985, sub13983]
  rfl
theorem sub13987 (p : Pattern) : d3045 (change p 10000 (some 247)) = d7887 p := by
  change (if p 162 then d3044 (change p 10000 (some 247)) else d3041 (change p 10000 (some 247))) = d7887 p
  rw [sub13986, sub13981]
  rfl
theorem sub13988 (p : Pattern) : d3046 (change p 10000 (some 247)) = d7888 p := by
  change (if p 162 then d2999 (change p 10000 (some 247)) else d3044 (change p 10000 (some 247))) = d7888 p
  rw [sub13894, sub13986]
  rfl
theorem sub13989 (p : Pattern) : d3047 (change p 10000 (some 247)) = d7889 p := by
  change (if p 161 then d3046 (change p 10000 (some 247)) else d3045 (change p 10000 (some 247))) = d7889 p
  rw [sub13988, sub13987]
  rfl
theorem sub13990 (p : Pattern) : d3048 (change p 10000 (some 247)) = d7890 p := by
  change (if p 182 then d1899 (change p 10000 (some 247)) else d3023 (change p 10000 (some 247))) = d7890 p
  rw [sub13913, sub13955]
  rfl
theorem sub13991 (p : Pattern) : d3049 (change p 10000 (some 247)) = d7891 p := by
  change (if p 204 then d1905 (change p 10000 (some 247)) else d120 (change p 10000 (some 247))) = d7891 p
  rw [sub13921, sub13915]
  rfl
theorem sub13992 (p : Pattern) : d3050 (change p 10000 (some 247)) = d7892 p := by
  change (if p 182 then d1906 (change p 10000 (some 247)) else d3049 (change p 10000 (some 247))) = d7892 p
  rw [sub13922, sub13991]
  rfl
theorem sub13993 (p : Pattern) : d3051 (change p 10000 (some 247)) = d7893 p := by
  change (if p 163 then d3050 (change p 10000 (some 247)) else d3048 (change p 10000 (some 247))) = d7893 p
  rw [sub13992, sub13990]
  rfl
theorem sub13994 (p : Pattern) : d3052 (change p 10000 (some 247)) = d7894 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3051 (change p 10000 (some 247))) = d7894 p
  rw [sub13654, sub13993]
  rfl
theorem sub13995 (p : Pattern) : d3053 (change p 10000 (some 247)) = d7895 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d3052 (change p 10000 (some 247))) = d7895 p
  rw [sub13654, sub13994]
  rfl
theorem sub13996 (p : Pattern) : d3054 (change p 10000 (some 247)) = d7896 p := by
  change (if p 160 then d3053 (change p 10000 (some 247)) else d3047 (change p 10000 (some 247))) = d7896 p
  rw [sub13995, sub13989]
  rfl
theorem sub13997 (p : Pattern) : d3055 (change p 10000 (some 247)) = d7897 p := by
  change (if p 163 then d3048 (change p 10000 (some 247)) else d3040 (change p 10000 (some 247))) = d7897 p
  rw [sub13990, sub13980]
  rfl
theorem sub13998 (p : Pattern) : d3056 (change p 10000 (some 247)) = d7898 p := by
  change (if p 163 then d2928 (change p 10000 (some 247)) else d3043 (change p 10000 (some 247))) = d7898 p
  rw [sub13780, sub13985]
  rfl
theorem sub13999 (p : Pattern) : d3057 (change p 10000 (some 247)) = d7899 p := by
  change (if p 162 then d3056 (change p 10000 (some 247)) else d3055 (change p 10000 (some 247))) = d7899 p
  rw [sub13998, sub13997]
  rfl
theorem sub14000 (p : Pattern) : d3058 (change p 10000 (some 247)) = d7900 p := by
  change (if p 163 then d2931 (change p 10000 (some 247)) else d3043 (change p 10000 (some 247))) = d7900 p
  rw [sub13783, sub13985]
  rfl
theorem sub14001 (p : Pattern) : d3059 (change p 10000 (some 247)) = d7901 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3058 (change p 10000 (some 247))) = d7901 p
  rw [sub13654, sub14000]
  rfl
theorem sub14002 (p : Pattern) : d3060 (change p 10000 (some 247)) = d7902 p := by
  change (if p 161 then d3059 (change p 10000 (some 247)) else d3057 (change p 10000 (some 247))) = d7902 p
  rw [sub14001, sub13999]
  rfl
theorem sub14003 (p : Pattern) : d3061 (change p 10000 (some 247)) = d7903 p := by
  change (if p 163 then d12 (change p 10000 (some 247)) else d3050 (change p 10000 (some 247))) = d7903 p
  rw [sub13654, sub13992]
  rfl
theorem sub14004 (p : Pattern) : d3062 (change p 10000 (some 247)) = d7904 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d3061 (change p 10000 (some 247))) = d7904 p
  rw [sub13654, sub14003]
  rfl
theorem sub14005 (p : Pattern) : d3063 (change p 10000 (some 247)) = d7905 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d3062 (change p 10000 (some 247))) = d7905 p
  rw [sub13654, sub14004]
  rfl
theorem sub14006 (p : Pattern) : d3064 (change p 10000 (some 247)) = d7906 p := by
  change (if p 160 then d3063 (change p 10000 (some 247)) else d3060 (change p 10000 (some 247))) = d7906 p
  rw [sub14005, sub14002]
  rfl
theorem sub14007 (p : Pattern) : d3065 (change p 10000 (some 247)) = d7907 p := by
  change (if p 141 then d3064 (change p 10000 (some 247)) else d3054 (change p 10000 (some 247))) = d7907 p
  rw [sub14006, sub13996]
  rfl
theorem sub14008 (p : Pattern) : d3066 (change p 10000 (some 247)) = d7908 p := by
  change (if p 138 then d3065 (change p 10000 (some 247)) else d3032 (change p 10000 (some 247))) = d7908 p
  rw [sub14007, sub13964]
  rfl
theorem sub14009 (p : Pattern) : d3067 (change p 10000 (some 247)) = d7909 p := by
  change (if p 162 then d12 (change p 10000 (some 247)) else d2999 (change p 10000 (some 247))) = d7909 p
  rw [sub13654, sub13894]
  rfl
theorem sub14010 (p : Pattern) : d3068 (change p 10000 (some 247)) = d7910 p := by
  change (if p 161 then d12 (change p 10000 (some 247)) else d3067 (change p 10000 (some 247))) = d7910 p
  rw [sub13654, sub14009]
  rfl
theorem sub14011 (p : Pattern) : d3069 (change p 10000 (some 247)) = d7911 p := by
  change (if p 160 then d12 (change p 10000 (some 247)) else d3068 (change p 10000 (some 247))) = d7911 p
  rw [sub13654, sub14010]
  rfl
theorem sub14012 (p : Pattern) : d3070 (change p 10000 (some 247)) = d7912 p := by
  change (if p 141 then d12 (change p 10000 (some 247)) else d3069 (change p 10000 (some 247))) = d7912 p
  rw [sub13654, sub14011]
  rfl
theorem sub14013 (p : Pattern) : d3071 (change p 10000 (some 247)) = d7913 p := by
  change (if p 138 then d3070 (change p 10000 (some 247)) else d3065 (change p 10000 (some 247))) = d7913 p
  rw [sub14012, sub14007]
  rfl
theorem sub14014 (p : Pattern) : d3072 (change p 10000 (some 247)) = d7914 p := by
  change (if p 116 then d3071 (change p 10000 (some 247)) else d3066 (change p 10000 (some 247))) = d7914 p
  rw [sub14013, sub14008]
  rfl
theorem sub14015 (p : Pattern) : d3073 (change p 10000 (some 247)) = d7915 p := by
  change (if p 138 then d12 (change p 10000 (some 247)) else d3065 (change p 10000 (some 247))) = d7915 p
  rw [sub13654, sub14007]
  rfl
theorem sub14016 (p : Pattern) : d3074 (change p 10000 (some 247)) = d7916 p := by
  change (if p 116 then d3073 (change p 10000 (some 247)) else d3066 (change p 10000 (some 247))) = d7916 p
  rw [sub14015, sub14008]
  rfl
theorem sub14017 (p : Pattern) : d3075 (change p 10000 (some 247)) = d7917 p := by
  change (if p 115 then d3074 (change p 10000 (some 247)) else d3072 (change p 10000 (some 247))) = d7917 p
  rw [sub14016, sub14014]
  rfl
theorem sub14018 (p : Pattern) : d3076 (change p 10000 (some 247)) = d7918 p := by
  change (if p 71 then d3075 (change p 10000 (some 247)) else d2992 (change p 10000 (some 247))) = d7918 p
  rw [sub14017, sub13859]
  rfl
theorem sub14019 (p : Pattern) : d3077 (change p 10000 (some 247)) = d7919 p := by
  change (if p 49 then d3076 (change p 10000 (some 247)) else d2992 (change p 10000 (some 247))) = d7919 p
  rw [sub14018, sub13859]
  rfl
theorem sub14020 (p : Pattern) : d3078 (change p 10000 (some 247)) = d7920 p := by
  change (if p 225 then d1792 (change p 10000 (some 247)) else d1795 (change p 10000 (some 247))) = d7920 p
  rw [sub13746, sub13676]
  rfl
theorem sub14021 (p : Pattern) : d3079 (change p 10000 (some 247)) = d7921 p := by
  change (if p 224 then d3078 (change p 10000 (some 247)) else d1793 (change p 10000 (some 247))) = d7921 p
  rw [sub14020, sub13747]
  rfl
theorem sub14022 (p : Pattern) : d3080 (change p 10000 (some 247)) = d7922 p := by
  change (if p 204 then d3079 (change p 10000 (some 247)) else d18 (change p 10000 (some 247))) = d7922 p
  rw [sub14021, sub13672]
  rfl
theorem sub14023 (p : Pattern) : d2013 (change p 10000 (some 247)) = d7923 p := by
  change (if p 204 then d12 (change p 10000 (some 247)) else d2012 (change p 10000 (some 247))) = d7923 p
  rw [sub13654, sub13678]
  rfl
theorem sub14024 (p : Pattern) : d3081 (change p 10000 (some 247)) = d7924 p := by
  change (if p 182 then d2013 (change p 10000 (some 247)) else d3080 (change p 10000 (some 247))) = d7924 p
  rw [sub14023, sub14022]
  rfl
theorem sub14025 (p : Pattern) : d3082 (change p 10000 (some 247)) = d7925 p := by
  change (if p 163 then d3081 (change p 10000 (some 247)) else d2949 (change p 10000 (some 247))) = d7925 p
  rw [sub14024, sub13804]
  rfl
theorem sub14026 (p : Pattern) : d3083 (change p 10000 (some 247)) = d7926 p := by
  change (if p 162 then d3082 (change p 10000 (some 247)) else d2949 (change p 10000 (some 247))) = d7926 p
  rw [sub14025, sub13804]
  rfl
theorem sub14027 (p : Pattern) : d3084 (change p 10000 (some 247)) = d7927 p := by
  change (if p 162 then d2958 (change p 10000 (some 247)) else d3082 (change p 10000 (some 247))) = d7927 p
  rw [sub13825, sub14025]
  rfl
theorem sub14028 (p : Pattern) : d3085 (change p 10000 (some 247)) = d7928 p := by
  change (if p 161 then d3084 (change p 10000 (some 247)) else d3083 (change p 10000 (some 247))) = d7928 p
  rw [sub14027, sub14026]
  rfl
theorem sub14029 (p : Pattern) : d3086 (change p 10000 (some 247)) = d7929 p := by
  change (if p 182 then d1725 (change p 10000 (some 247)) else d2935 (change p 10000 (some 247))) = d7929 p
  rw [sub13736, sub13787]
  rfl
theorem sub14030 (p : Pattern) : d3087 (change p 10000 (some 247)) = d7930 p := by
  change (if p 163 then d3086 (change p 10000 (some 247)) else d2961 (change p 10000 (some 247))) = d7930 p
  rw [sub14029, sub13828]
  rfl
theorem sub14031 (p : Pattern) : d3088 (change p 10000 (some 247)) = d7931 p := by
  change (if p 182 then d1730 (change p 10000 (some 247)) else d2935 (change p 10000 (some 247))) = d7931 p
  rw [sub13743, sub13787]
  rfl
theorem sub14032 (p : Pattern) : d3089 (change p 10000 (some 247)) = d7932 p := by
  change (if p 182 then d12 (change p 10000 (some 247)) else d2962 (change p 10000 (some 247))) = d7932 p
  rw [sub13654, sub13829]
  rfl
theorem sub14033 (p : Pattern) : d3090 (change p 10000 (some 247)) = d7933 p := by
  change (if p 163 then d3089 (change p 10000 (some 247)) else d3088 (change p 10000 (some 247))) = d7933 p
  rw [sub14032, sub14031]
  rfl
theorem sub14034 (p : Pattern) : d3091 (change p 10000 (some 247)) = d7934 p := by
  change (if p 162 then d3090 (change p 10000 (some 247)) else d3087 (change p 10000 (some 247))) = d7934 p
  rw [sub14033, sub14030]
  rfl
theorem sub14035 (p : Pattern) : d3092 (change p 10000 (some 247)) = d7935 p := by
  change (if p 163 then d3089 (change p 10000 (some 247)) else d2936 (change p 10000 (some 247))) = d7935 p
  rw [sub14032, sub13788]
  rfl
theorem sub14036 (p : Pattern) : d3093 (change p 10000 (some 247)) = d7936 p := by
  change (if p 162 then d2943 (change p 10000 (some 247)) else d3092 (change p 10000 (some 247))) = d7936 p
  rw [sub13795, sub14035]
  rfl
theorem sub14037 (p : Pattern) : d3094 (change p 10000 (some 247)) = d7937 p := by
  change (if p 161 then d3093 (change p 10000 (some 247)) else d3091 (change p 10000 (some 247))) = d7937 p
  rw [sub14036, sub14034]
  rfl
theorem sub14038 (p : Pattern) : d3095 (change p 10000 (some 247)) = d7938 p := by
  change (if p 160 then d3094 (change p 10000 (some 247)) else d3085 (change p 10000 (some 247))) = d7938 p
  rw [sub14037, sub14028]
  rfl
theorem sub14039 (p : Pattern) : d3096 (change p 10000 (some 247)) = d7939 p := by
  change (if p 225 then d1711 (change p 10000 (some 247)) else d1714 (change p 10000 (some 247))) = d7939 p
  rw [sub13718, sub13721]
  rfl
end NetHack.Sokoban22Refined85
