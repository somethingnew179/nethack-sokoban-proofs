/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions73
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub8880 (p : Pattern) : d2957 (change p 10000 none) = d2957 p := by
  change (if p 182 then d1804 (change p 10000 none) else d2901 (change p 10000 none)) = d2957 p
  rw [sub8879, sub8761]
  rfl
theorem sub8881 (p : Pattern) : d2958 (change p 10000 none) = d2958 p := by
  change (if p 163 then d12 (change p 10000 none) else d2957 (change p 10000 none)) = d2958 p
  rw [sub1, sub8880]
  rfl
theorem sub8882 (p : Pattern) : d2959 (change p 10000 none) = d2959 p := by
  change (if p 162 then d2958 (change p 10000 none) else d2955 (change p 10000 none)) = d2959 p
  rw [sub8881, sub8877]
  rfl
theorem sub8883 (p : Pattern) : d2960 (change p 10000 none) = d2960 p := by
  change (if p 161 then d2959 (change p 10000 none) else d2956 (change p 10000 none)) = d2960 p
  rw [sub8882, sub8878]
  rfl
theorem sub8884 (p : Pattern) : d2961 (change p 10000 none) = d2961 p := by
  change (if p 182 then d1718 (change p 10000 none) else d2935 (change p 10000 none)) = d2961 p
  rw [sub8787, sub8843]
  rfl
theorem sub8885 (p : Pattern) : d2962 (change p 10000 none) = d2962 p := by
  change (if p 204 then d1724 (change p 10000 none) else d35 (change p 10000 none)) = d2962 p
  rw [sub8794, sub28]
  rfl
theorem sub8886 (p : Pattern) : d2963 (change p 10000 none) = d2963 p := by
  change (if p 182 then d1725 (change p 10000 none) else d2962 (change p 10000 none)) = d2963 p
  rw [sub8795, sub8885]
  rfl
theorem sub8887 (p : Pattern) : d2964 (change p 10000 none) = d2964 p := by
  change (if p 163 then d2963 (change p 10000 none) else d2961 (change p 10000 none)) = d2964 p
  rw [sub8886, sub8884]
  rfl
theorem sub8888 (p : Pattern) : d2965 (change p 10000 none) = d2965 p := by
  change (if p 162 then d2932 (change p 10000 none) else d2964 (change p 10000 none)) = d2965 p
  rw [sub8840, sub8887]
  rfl
theorem sub8889 (p : Pattern) : d2966 (change p 10000 none) = d2966 p := by
  change (if p 161 then d12 (change p 10000 none) else d2965 (change p 10000 none)) = d2966 p
  rw [sub1, sub8888]
  rfl
theorem sub8890 (p : Pattern) : d2967 (change p 10000 none) = d2967 p := by
  change (if p 160 then d2966 (change p 10000 none) else d2960 (change p 10000 none)) = d2967 p
  rw [sub8889, sub8883]
  rfl
theorem sub8891 (p : Pattern) : d2968 (change p 10000 none) = d2968 p := by
  change (if p 163 then d2961 (change p 10000 none) else d2951 (change p 10000 none)) = d2968 p
  rw [sub8884, sub8871]
  rfl
theorem sub8892 (p : Pattern) : d2969 (change p 10000 none) = d2969 p := by
  change (if p 163 then d2957 (change p 10000 none) else d2954 (change p 10000 none)) = d2969 p
  rw [sub8880, sub8876]
  rfl
theorem sub8893 (p : Pattern) : d2970 (change p 10000 none) = d2970 p := by
  change (if p 162 then d2969 (change p 10000 none) else d2968 (change p 10000 none)) = d2970 p
  rw [sub8892, sub8891]
  rfl
theorem sub8894 (p : Pattern) : d2971 (change p 10000 none) = d2971 p := by
  change (if p 163 then d2928 (change p 10000 none) else d2954 (change p 10000 none)) = d2971 p
  rw [sub8836, sub8876]
  rfl
theorem sub8895 (p : Pattern) : d2972 (change p 10000 none) = d2972 p := by
  change (if p 162 then d2932 (change p 10000 none) else d2971 (change p 10000 none)) = d2972 p
  rw [sub8840, sub8894]
  rfl
theorem sub8896 (p : Pattern) : d2973 (change p 10000 none) = d2973 p := by
  change (if p 161 then d2972 (change p 10000 none) else d2970 (change p 10000 none)) = d2973 p
  rw [sub8895, sub8893]
  rfl
theorem sub8897 (p : Pattern) : d2974 (change p 10000 none) = d2974 p := by
  change (if p 163 then d12 (change p 10000 none) else d2963 (change p 10000 none)) = d2974 p
  rw [sub1, sub8886]
  rfl
theorem sub8898 (p : Pattern) : d2975 (change p 10000 none) = d2975 p := by
  change (if p 162 then d12 (change p 10000 none) else d2974 (change p 10000 none)) = d2975 p
  rw [sub1, sub8897]
  rfl
theorem sub8899 (p : Pattern) : d2976 (change p 10000 none) = d2976 p := by
  change (if p 161 then d12 (change p 10000 none) else d2975 (change p 10000 none)) = d2976 p
  rw [sub1, sub8898]
  rfl
theorem sub8900 (p : Pattern) : d2977 (change p 10000 none) = d2977 p := by
  change (if p 160 then d2976 (change p 10000 none) else d2973 (change p 10000 none)) = d2977 p
  rw [sub8899, sub8896]
  rfl
theorem sub8901 (p : Pattern) : d2978 (change p 10000 none) = d2978 p := by
  change (if p 141 then d2977 (change p 10000 none) else d2967 (change p 10000 none)) = d2978 p
  rw [sub8900, sub8890]
  rfl
theorem sub8902 (p : Pattern) : d2979 (change p 10000 none) = d2979 p := by
  change (if p 138 then d2978 (change p 10000 none) else d2947 (change p 10000 none)) = d2979 p
  rw [sub8901, sub8855]
  rfl
theorem sub8903 (p : Pattern) : d2980 (change p 10000 none) = d2980 p := by
  change (if p 163 then d2931 (change p 10000 none) else d2957 (change p 10000 none)) = d2980 p
  rw [sub8839, sub8880]
  rfl
theorem sub8904 (p : Pattern) : d2981 (change p 10000 none) = d2981 p := by
  change (if p 162 then d2932 (change p 10000 none) else d2980 (change p 10000 none)) = d2981 p
  rw [sub8840, sub8903]
  rfl
theorem sub8905 (p : Pattern) : d2982 (change p 10000 none) = d2982 p := by
  change (if p 162 then d12 (change p 10000 none) else d2932 (change p 10000 none)) = d2982 p
  rw [sub1, sub8840]
  rfl
theorem sub8906 (p : Pattern) : d2983 (change p 10000 none) = d2983 p := by
  change (if p 161 then d2982 (change p 10000 none) else d2981 (change p 10000 none)) = d2983 p
  rw [sub8905, sub8904]
  rfl
theorem sub8907 (p : Pattern) : d2984 (change p 10000 none) = d2984 p := by
  change (if p 161 then d12 (change p 10000 none) else d2982 (change p 10000 none)) = d2984 p
  rw [sub1, sub8905]
  rfl
theorem sub8908 (p : Pattern) : d2985 (change p 10000 none) = d2985 p := by
  change (if p 160 then d2984 (change p 10000 none) else d2983 (change p 10000 none)) = d2985 p
  rw [sub8907, sub8906]
  rfl
theorem sub8909 (p : Pattern) : d2986 (change p 10000 none) = d2986 p := by
  change (if p 160 then d12 (change p 10000 none) else d2984 (change p 10000 none)) = d2986 p
  rw [sub1, sub8907]
  rfl
theorem sub8910 (p : Pattern) : d2987 (change p 10000 none) = d2987 p := by
  change (if p 141 then d2986 (change p 10000 none) else d2985 (change p 10000 none)) = d2987 p
  rw [sub8909, sub8908]
  rfl
theorem sub8911 (p : Pattern) : d2988 (change p 10000 none) = d2988 p := by
  change (if p 138 then d2987 (change p 10000 none) else d2978 (change p 10000 none)) = d2988 p
  rw [sub8910, sub8901]
  rfl
theorem sub8912 (p : Pattern) : d2989 (change p 10000 none) = d2989 p := by
  change (if p 116 then d2988 (change p 10000 none) else d2979 (change p 10000 none)) = d2989 p
  rw [sub8911, sub8902]
  rfl
theorem sub8913 (p : Pattern) : d2990 (change p 10000 none) = d2990 p := by
  change (if p 138 then d12 (change p 10000 none) else d2978 (change p 10000 none)) = d2990 p
  rw [sub1, sub8901]
  rfl
theorem sub8914 (p : Pattern) : d2991 (change p 10000 none) = d2991 p := by
  change (if p 116 then d2990 (change p 10000 none) else d2979 (change p 10000 none)) = d2991 p
  rw [sub8913, sub8902]
  rfl
theorem sub8915 (p : Pattern) : d2992 (change p 10000 none) = d2992 p := by
  change (if p 115 then d2991 (change p 10000 none) else d2989 (change p 10000 none)) = d2992 p
  rw [sub8914, sub8912]
  rfl
theorem sub8916 (p : Pattern) : d1939 (change p 10000 none) = d1939 p := by
  change (if p 247 then d5 (change p 10000 none) else d1 (change p 10000 none)) = d1939 p
  rw [sub102, sub97]
  rfl
theorem sub8917 (p : Pattern) : d1940 (change p 10000 none) = d1940 p := by
  change (if p 246 then d106 (change p 10000 none) else d1939 (change p 10000 none)) = d1940 p
  rw [sub103, sub8916]
  rfl
theorem sub8918 (p : Pattern) : d1941 (change p 10000 none) = d1941 p := by
  change (if p 225 then d1940 (change p 10000 none) else d103 (change p 10000 none)) = d1941 p
  rw [sub8917, sub99]
  rfl
theorem sub8919 (p : Pattern) : d1942 (change p 10000 none) = d1942 p := by
  change (if p 224 then d1940 (change p 10000 none) else d1941 (change p 10000 none)) = d1942 p
  rw [sub8917, sub8918]
  rfl
theorem sub8920 (p : Pattern) : d2993 (change p 10000 none) = d2993 p := by
  change (if p 204 then d1942 (change p 10000 none) else d103 (change p 10000 none)) = d2993 p
  rw [sub8919, sub99]
  rfl
theorem sub8921 (p : Pattern) : d1872 (change p 10000 none) = d1872 p := by
  change (if p 247 then d3 (change p 10000 none) else d1 (change p 10000 none)) = d1872 p
  rw [sub112, sub97]
  rfl
theorem sub8922 (p : Pattern) : d1873 (change p 10000 none) = d1873 p := by
  change (if p 246 then d115 (change p 10000 none) else d1872 (change p 10000 none)) = d1873 p
  rw [sub113, sub8921]
  rfl
theorem sub8923 (p : Pattern) : d1874 (change p 10000 none) = d1874 p := by
  change (if p 225 then d1873 (change p 10000 none) else d103 (change p 10000 none)) = d1874 p
  rw [sub8922, sub99]
  rfl
theorem sub8924 (p : Pattern) : d1875 (change p 10000 none) = d1875 p := by
  change (if p 224 then d1873 (change p 10000 none) else d1874 (change p 10000 none)) = d1875 p
  rw [sub8922, sub8923]
  rfl
theorem sub8925 (p : Pattern) : d1876 (change p 10000 none) = d1876 p := by
  change (if p 204 then d12 (change p 10000 none) else d1875 (change p 10000 none)) = d1876 p
  rw [sub1, sub8924]
  rfl
theorem sub8926 (p : Pattern) : d2994 (change p 10000 none) = d2994 p := by
  change (if p 182 then d1876 (change p 10000 none) else d2993 (change p 10000 none)) = d2994 p
  rw [sub8925, sub8920]
  rfl
theorem sub8927 (p : Pattern) : d1963 (change p 10000 none) = d1963 p := by
  change (if p 247 then d9 (change p 10000 none) else d5 (change p 10000 none)) = d1963 p
  rw [sub13, sub102]
  rfl
theorem sub8928 (p : Pattern) : d1964 (change p 10000 none) = d1964 p := by
  change (if p 246 then d23 (change p 10000 none) else d1963 (change p 10000 none)) = d1964 p
  rw [sub14, sub8927]
  rfl
theorem sub8929 (p : Pattern) : d2129 (change p 10000 none) = d2129 p := by
  change (if p 225 then d1964 (change p 10000 none) else d107 (change p 10000 none)) = d2129 p
  rw [sub8928, sub104]
  rfl
theorem sub8930 (p : Pattern) : d2130 (change p 10000 none) = d2130 p := by
  change (if p 224 then d1964 (change p 10000 none) else d2129 (change p 10000 none)) = d2130 p
  rw [sub8928, sub8929]
  rfl
theorem sub8931 (p : Pattern) : d2995 (change p 10000 none) = d2995 p := by
  change (if p 204 then d2130 (change p 10000 none) else d107 (change p 10000 none)) = d2995 p
  rw [sub8930, sub104]
  rfl
theorem sub8932 (p : Pattern) : d1880 (change p 10000 none) = d1880 p := by
  change (if p 247 then d7 (change p 10000 none) else d5 (change p 10000 none)) = d1880 p
  rw [sub117, sub102]
  rfl
theorem sub8933 (p : Pattern) : d1881 (change p 10000 none) = d1881 p := by
  change (if p 246 then d119 (change p 10000 none) else d1880 (change p 10000 none)) = d1881 p
  rw [sub118, sub8932]
  rfl
theorem sub8934 (p : Pattern) : d1882 (change p 10000 none) = d1882 p := by
  change (if p 225 then d1881 (change p 10000 none) else d107 (change p 10000 none)) = d1882 p
  rw [sub8933, sub104]
  rfl
theorem sub8935 (p : Pattern) : d1883 (change p 10000 none) = d1883 p := by
  change (if p 224 then d1881 (change p 10000 none) else d1882 (change p 10000 none)) = d1883 p
  rw [sub8933, sub8934]
  rfl
theorem sub8936 (p : Pattern) : d1884 (change p 10000 none) = d1884 p := by
  change (if p 204 then d12 (change p 10000 none) else d1883 (change p 10000 none)) = d1884 p
  rw [sub1, sub8935]
  rfl
theorem sub8937 (p : Pattern) : d2996 (change p 10000 none) = d2996 p := by
  change (if p 182 then d1884 (change p 10000 none) else d2995 (change p 10000 none)) = d2996 p
  rw [sub8936, sub8931]
  rfl
theorem sub8938 (p : Pattern) : d2997 (change p 10000 none) = d2997 p := by
  change (if p 163 then d2996 (change p 10000 none) else d2994 (change p 10000 none)) = d2997 p
  rw [sub8937, sub8926]
  rfl
theorem sub8939 (p : Pattern) : d2998 (change p 10000 none) = d2998 p := by
  change (if p 162 then d2997 (change p 10000 none) else d2994 (change p 10000 none)) = d2998 p
  rw [sub8938, sub8926]
  rfl
theorem sub8940 (p : Pattern) : d2999 (change p 10000 none) = d2999 p := by
  change (if p 163 then d12 (change p 10000 none) else d2928 (change p 10000 none)) = d2999 p
  rw [sub1, sub8836]
  rfl
theorem sub8941 (p : Pattern) : d3000 (change p 10000 none) = d3000 p := by
  change (if p 162 then d2999 (change p 10000 none) else d2997 (change p 10000 none)) = d3000 p
  rw [sub8940, sub8938]
  rfl
theorem sub8942 (p : Pattern) : d3001 (change p 10000 none) = d3001 p := by
  change (if p 161 then d3000 (change p 10000 none) else d2998 (change p 10000 none)) = d3001 p
  rw [sub8941, sub8939]
  rfl
theorem sub8943 (p : Pattern) : d1945 (change p 10000 none) = d1945 p := by
  change (if p 247 then d7 (change p 10000 none) else d1 (change p 10000 none)) = d1945 p
  rw [sub117, sub97]
  rfl
theorem sub8944 (p : Pattern) : d1946 (change p 10000 none) = d1946 p := by
  change (if p 246 then d119 (change p 10000 none) else d1945 (change p 10000 none)) = d1946 p
  rw [sub118, sub8943]
  rfl
theorem sub8945 (p : Pattern) : d1947 (change p 10000 none) = d1947 p := by
  change (if p 225 then d1946 (change p 10000 none) else d103 (change p 10000 none)) = d1947 p
  rw [sub8944, sub99]
  rfl
theorem sub8946 (p : Pattern) : d1955 (change p 10000 none) = d1955 p := by
  change (if p 246 then d57 (change p 10000 none) else d102 (change p 10000 none)) = d1955 p
  rw [sub52, sub98]
  rfl
theorem sub8947 (p : Pattern) : d1956 (change p 10000 none) = d1956 p := by
  change (if p 225 then d1955 (change p 10000 none) else d1940 (change p 10000 none)) = d1956 p
  rw [sub8946, sub8917]
  rfl
theorem sub8948 (p : Pattern) : d1957 (change p 10000 none) = d1957 p := by
  change (if p 224 then d1956 (change p 10000 none) else d1947 (change p 10000 none)) = d1957 p
  rw [sub8947, sub8945]
  rfl
theorem sub8949 (p : Pattern) : d3002 (change p 10000 none) = d3002 p := by
  change (if p 204 then d1957 (change p 10000 none) else d103 (change p 10000 none)) = d3002 p
  rw [sub8948, sub99]
  rfl
theorem sub8950 (p : Pattern) : d1891 (change p 10000 none) = d1891 p := by
  change (if p 247 then d9 (change p 10000 none) else d3 (change p 10000 none)) = d1891 p
  rw [sub13, sub112]
  rfl
theorem sub8951 (p : Pattern) : d1892 (change p 10000 none) = d1892 p := by
  change (if p 246 then d23 (change p 10000 none) else d1891 (change p 10000 none)) = d1892 p
  rw [sub14, sub8950]
  rfl
theorem sub8952 (p : Pattern) : d1893 (change p 10000 none) = d1893 p := by
  change (if p 225 then d1892 (change p 10000 none) else d116 (change p 10000 none)) = d1893 p
  rw [sub8951, sub114]
  rfl
theorem sub8953 (p : Pattern) : d1894 (change p 10000 none) = d1894 p := by
  change (if p 247 then d7 (change p 10000 none) else d3 (change p 10000 none)) = d1894 p
  rw [sub117, sub112]
  rfl
theorem sub8954 (p : Pattern) : d1895 (change p 10000 none) = d1895 p := by
  change (if p 246 then d119 (change p 10000 none) else d1894 (change p 10000 none)) = d1895 p
  rw [sub118, sub8953]
  rfl
theorem sub8955 (p : Pattern) : d1896 (change p 10000 none) = d1896 p := by
  change (if p 246 then d12 (change p 10000 none) else d115 (change p 10000 none)) = d1896 p
  rw [sub1, sub113]
  rfl
theorem sub8956 (p : Pattern) : d1897 (change p 10000 none) = d1897 p := by
  change (if p 225 then d1896 (change p 10000 none) else d1895 (change p 10000 none)) = d1897 p
  rw [sub8955, sub8954]
  rfl
theorem sub8957 (p : Pattern) : d1898 (change p 10000 none) = d1898 p := by
  change (if p 224 then d1897 (change p 10000 none) else d1893 (change p 10000 none)) = d1898 p
  rw [sub8956, sub8952]
  rfl
theorem sub8958 (p : Pattern) : d1899 (change p 10000 none) = d1899 p := by
  change (if p 204 then d12 (change p 10000 none) else d1898 (change p 10000 none)) = d1899 p
  rw [sub1, sub8957]
  rfl
theorem sub8959 (p : Pattern) : d3003 (change p 10000 none) = d3003 p := by
  change (if p 182 then d1899 (change p 10000 none) else d3002 (change p 10000 none)) = d3003 p
  rw [sub8958, sub8949]
  rfl
theorem sub8960 (p : Pattern) : d317 (change p 10000 none) = d317 p := by
  change (if p 246 then d12 (change p 10000 none) else d119 (change p 10000 none)) = d317 p
  rw [sub1, sub118]
  rfl
theorem sub8961 (p : Pattern) : d1901 (change p 10000 none) = d1901 p := by
  change (if p 225 then d317 (change p 10000 none) else d120 (change p 10000 none)) = d1901 p
  rw [sub8960, sub119]
  rfl
theorem sub8962 (p : Pattern) : d1902 (change p 10000 none) = d1902 p := by
  change (if p 247 then d11 (change p 10000 none) else d7 (change p 10000 none)) = d1902 p
  rw [sub32, sub117]
  rfl
theorem sub8963 (p : Pattern) : d1903 (change p 10000 none) = d1903 p := by
  change (if p 246 then d39 (change p 10000 none) else d1902 (change p 10000 none)) = d1903 p
  rw [sub33, sub8962]
  rfl
theorem sub8964 (p : Pattern) : d1904 (change p 10000 none) = d1904 p := by
  change (if p 225 then d317 (change p 10000 none) else d1903 (change p 10000 none)) = d1904 p
  rw [sub8960, sub8963]
  rfl
theorem sub8965 (p : Pattern) : d1905 (change p 10000 none) = d1905 p := by
  change (if p 224 then d1904 (change p 10000 none) else d1901 (change p 10000 none)) = d1905 p
  rw [sub8964, sub8961]
  rfl
theorem sub8966 (p : Pattern) : d1906 (change p 10000 none) = d1906 p := by
  change (if p 204 then d12 (change p 10000 none) else d1905 (change p 10000 none)) = d1906 p
  rw [sub1, sub8965]
  rfl
theorem sub8967 (p : Pattern) : d3004 (change p 10000 none) = d3004 p := by
  change (if p 182 then d1906 (change p 10000 none) else d3002 (change p 10000 none)) = d3004 p
  rw [sub8966, sub8949]
  rfl
theorem sub8968 (p : Pattern) : d3005 (change p 10000 none) = d3005 p := by
  change (if p 163 then d3004 (change p 10000 none) else d3003 (change p 10000 none)) = d3005 p
  rw [sub8967, sub8959]
  rfl
theorem sub8969 (p : Pattern) : d3006 (change p 10000 none) = d3006 p := by
  change (if p 182 then d12 (change p 10000 none) else d3002 (change p 10000 none)) = d3006 p
  rw [sub1, sub8949]
  rfl
theorem sub8970 (p : Pattern) : d1960 (change p 10000 none) = d1960 p := by
  change (if p 247 then d11 (change p 10000 none) else d5 (change p 10000 none)) = d1960 p
  rw [sub32, sub102]
  rfl
theorem sub8971 (p : Pattern) : d1961 (change p 10000 none) = d1961 p := by
  change (if p 246 then d39 (change p 10000 none) else d1960 (change p 10000 none)) = d1961 p
  rw [sub33, sub8970]
  rfl
theorem sub8972 (p : Pattern) : d1962 (change p 10000 none) = d1962 p := by
  change (if p 225 then d1961 (change p 10000 none) else d107 (change p 10000 none)) = d1962 p
  rw [sub8971, sub104]
  rfl
theorem sub8973 (p : Pattern) : d348 (change p 10000 none) = d348 p := by
  change (if p 246 then d12 (change p 10000 none) else d106 (change p 10000 none)) = d348 p
  rw [sub1, sub103]
  rfl
theorem sub8974 (p : Pattern) : d1965 (change p 10000 none) = d1965 p := by
  change (if p 225 then d348 (change p 10000 none) else d1964 (change p 10000 none)) = d1965 p
  rw [sub8973, sub8928]
  rfl
theorem sub8975 (p : Pattern) : d1966 (change p 10000 none) = d1966 p := by
  change (if p 224 then d1965 (change p 10000 none) else d1962 (change p 10000 none)) = d1966 p
  rw [sub8974, sub8972]
  rfl
theorem sub8976 (p : Pattern) : d3007 (change p 10000 none) = d3007 p := by
  change (if p 204 then d1966 (change p 10000 none) else d107 (change p 10000 none)) = d3007 p
  rw [sub8975, sub104]
  rfl
theorem sub8977 (p : Pattern) : d3008 (change p 10000 none) = d3008 p := by
  change (if p 182 then d12 (change p 10000 none) else d3007 (change p 10000 none)) = d3008 p
  rw [sub1, sub8976]
  rfl
theorem sub8978 (p : Pattern) : d3009 (change p 10000 none) = d3009 p := by
  change (if p 163 then d3008 (change p 10000 none) else d3006 (change p 10000 none)) = d3009 p
  rw [sub8977, sub8969]
  rfl
theorem sub8979 (p : Pattern) : d3010 (change p 10000 none) = d3010 p := by
  change (if p 162 then d3009 (change p 10000 none) else d3005 (change p 10000 none)) = d3010 p
  rw [sub8978, sub8968]
  rfl
theorem sub8980 (p : Pattern) : d3011 (change p 10000 none) = d3011 p := by
  change (if p 163 then d12 (change p 10000 none) else d2940 (change p 10000 none)) = d3011 p
  rw [sub1, sub8848]
  rfl
theorem sub8981 (p : Pattern) : d3012 (change p 10000 none) = d3012 p := by
  change (if p 162 then d3011 (change p 10000 none) else d3009 (change p 10000 none)) = d3012 p
  rw [sub8980, sub8978]
  rfl
theorem sub8982 (p : Pattern) : d3013 (change p 10000 none) = d3013 p := by
  change (if p 161 then d3012 (change p 10000 none) else d3010 (change p 10000 none)) = d3013 p
  rw [sub8981, sub8979]
  rfl
theorem sub8983 (p : Pattern) : d3014 (change p 10000 none) = d3014 p := by
  change (if p 160 then d3013 (change p 10000 none) else d3001 (change p 10000 none)) = d3014 p
  rw [sub8982, sub8942]
  rfl
theorem sub8984 (p : Pattern) : d2124 (change p 10000 none) = d2124 p := by
  change (if p 225 then d1895 (change p 10000 none) else d116 (change p 10000 none)) = d2124 p
  rw [sub8954, sub114]
  rfl
theorem sub8985 (p : Pattern) : d2125 (change p 10000 none) = d2125 p := by
  change (if p 224 then d1895 (change p 10000 none) else d2124 (change p 10000 none)) = d2125 p
  rw [sub8954, sub8984]
  rfl
theorem sub8986 (p : Pattern) : d3015 (change p 10000 none) = d3015 p := by
  change (if p 204 then d2125 (change p 10000 none) else d116 (change p 10000 none)) = d3015 p
  rw [sub8985, sub114]
  rfl
theorem sub8987 (p : Pattern) : d1918 (change p 10000 none) = d1918 p := by
  change (if p 247 then d5 (change p 10000 none) else d3 (change p 10000 none)) = d1918 p
  rw [sub102, sub112]
  rfl
theorem sub8988 (p : Pattern) : d1919 (change p 10000 none) = d1919 p := by
  change (if p 246 then d106 (change p 10000 none) else d1918 (change p 10000 none)) = d1919 p
  rw [sub103, sub8987]
  rfl
theorem sub8989 (p : Pattern) : d1920 (change p 10000 none) = d1920 p := by
  change (if p 225 then d1919 (change p 10000 none) else d116 (change p 10000 none)) = d1920 p
  rw [sub8988, sub114]
  rfl
theorem sub8990 (p : Pattern) : d1921 (change p 10000 none) = d1921 p := by
  change (if p 224 then d1919 (change p 10000 none) else d1920 (change p 10000 none)) = d1921 p
  rw [sub8988, sub8989]
  rfl
theorem sub8991 (p : Pattern) : d1922 (change p 10000 none) = d1922 p := by
  change (if p 204 then d12 (change p 10000 none) else d1921 (change p 10000 none)) = d1922 p
  rw [sub1, sub8990]
  rfl
theorem sub8992 (p : Pattern) : d3016 (change p 10000 none) = d3016 p := by
  change (if p 182 then d1922 (change p 10000 none) else d3015 (change p 10000 none)) = d3016 p
  rw [sub8991, sub8986]
  rfl
theorem sub8993 (p : Pattern) : d3017 (change p 10000 none) = d3017 p := by
  change (if p 163 then d3016 (change p 10000 none) else d2994 (change p 10000 none)) = d3017 p
  rw [sub8992, sub8926]
  rfl
theorem sub8994 (p : Pattern) : d3018 (change p 10000 none) = d3018 p := by
  change (if p 163 then d2928 (change p 10000 none) else d2996 (change p 10000 none)) = d3018 p
  rw [sub8836, sub8937]
  rfl
theorem sub8995 (p : Pattern) : d3019 (change p 10000 none) = d3019 p := by
  change (if p 162 then d3018 (change p 10000 none) else d3017 (change p 10000 none)) = d3019 p
  rw [sub8994, sub8993]
  rfl
theorem sub8996 (p : Pattern) : d3020 (change p 10000 none) = d3020 p := by
  change (if p 163 then d2931 (change p 10000 none) else d2996 (change p 10000 none)) = d3020 p
  rw [sub8839, sub8937]
  rfl
theorem sub8997 (p : Pattern) : d3021 (change p 10000 none) = d3021 p := by
  change (if p 162 then d12 (change p 10000 none) else d3020 (change p 10000 none)) = d3021 p
  rw [sub1, sub8996]
  rfl
theorem sub8998 (p : Pattern) : d3022 (change p 10000 none) = d3022 p := by
  change (if p 161 then d3021 (change p 10000 none) else d3019 (change p 10000 none)) = d3022 p
  rw [sub8997, sub8995]
  rfl
theorem sub8999 (p : Pattern) : d3023 (change p 10000 none) = d3023 p := by
  change (if p 204 then d1898 (change p 10000 none) else d116 (change p 10000 none)) = d3023 p
  rw [sub8957, sub114]
  rfl
end NetHack.Sokoban22Refined85
