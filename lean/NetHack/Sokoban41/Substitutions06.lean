/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions05
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s900 (pattern : Ten) : d43 (change pattern 7 3) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 7 3) else d6 (change pattern 7 3)) = d43 pattern
  rw [s890, s899]
  rfl
theorem s901 (pattern : Ten) : d50 (change pattern 7 3) = d50 pattern := by
  change (if pattern.i then d43 (change pattern 7 3) else d44 (change pattern 7 3)) = d50 pattern
  rw [s900, s898]
  rfl
theorem s902 (pattern : Ten) : d127 (change pattern 7 3) = d127 pattern := by
  change (if pattern.g then d20 (change pattern 7 3) else d50 (change pattern 7 3)) = d127 pattern
  rw [s896, s901]
  rfl
theorem s903 (pattern : Ten) : d129 (change pattern 7 3) = d129 pattern := by
  change (if pattern.c then d127 (change pattern 7 3) else d126 (change pattern 7 3)) = d129 pattern
  rw [s902, s897]
  rfl
theorem s904 (pattern : Ten) : d131 (change pattern 7 3) = d131 pattern := by
  change (if pattern.e then d10 (change pattern 7 3) else d129 (change pattern 7 3)) = d131 pattern
  rw [s890, s903]
  rfl
theorem s905 (pattern : Ten) : d132 (change pattern 7 3) = d131 pattern := by
  change d131 (change pattern 7 3) = d131 pattern
  exact s904 pattern
theorem s906 (pattern : Ten) : d1 (change pattern 7 3) = d1 pattern := by
  rfl
theorem s907 (pattern : Ten) : d171 (change pattern 7 3) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 7 3) else d0 (change pattern 7 3)) = d171 pattern
  rw [s906, s886]
  rfl
theorem s908 (pattern : Ten) : d3 (change pattern 7 3) = d3 pattern := by
  rfl
theorem s909 (pattern : Ten) : d172 (change pattern 7 3) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 7 3) else d2 (change pattern 7 3)) = d172 pattern
  rw [s908, s887]
  rfl
theorem s910 (pattern : Ten) : d174 (change pattern 7 3) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 7 3) else d171 (change pattern 7 3)) = d174 pattern
  rw [s909, s907]
  rfl
theorem s911 (pattern : Ten) : d5 (change pattern 7 3) = d5 pattern := by
  rfl
theorem s912 (pattern : Ten) : d193 (change pattern 7 3) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 7 3) else d4 (change pattern 7 3)) = d193 pattern
  rw [s911, s889]
  rfl
theorem s913 (pattern : Ten) : d197 (change pattern 7 3) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 7 3) else d193 (change pattern 7 3)) = d197 pattern
  rw [s890, s912]
  rfl
theorem s914 (pattern : Ten) : d202 (change pattern 7 3) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 7 3) else d174 (change pattern 7 3)) = d202 pattern
  rw [s913, s910]
  rfl
theorem s915 (pattern : Ten) : d282 (change pattern 7 3) = d282 pattern := by
  change (if pattern.g then d10 (change pattern 7 3) else d202 (change pattern 7 3)) = d282 pattern
  rw [s890, s914]
  rfl
theorem s916 (pattern : Ten) : d199 (change pattern 7 3) = d199 pattern := by
  change (if pattern.j then d193 (change pattern 7 3) else d172 (change pattern 7 3)) = d199 pattern
  rw [s912, s909]
  rfl
theorem s917 (pattern : Ten) : d7 (change pattern 7 3) = d7 pattern := by
  rfl
theorem s918 (pattern : Ten) : d194 (change pattern 7 3) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 7 3) else d6 (change pattern 7 3)) = d194 pattern
  rw [s917, s899]
  rfl
theorem s919 (pattern : Ten) : d198 (change pattern 7 3) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 7 3) else d194 (change pattern 7 3)) = d198 pattern
  rw [s890, s918]
  rfl
theorem s920 (pattern : Ten) : d204 (change pattern 7 3) = d204 pattern := by
  change (if pattern.i then d198 (change pattern 7 3) else d199 (change pattern 7 3)) = d204 pattern
  rw [s919, s916]
  rfl
theorem s921 (pattern : Ten) : d283 (change pattern 7 3) = d283 pattern := by
  change (if pattern.g then d10 (change pattern 7 3) else d204 (change pattern 7 3)) = d283 pattern
  rw [s890, s920]
  rfl
theorem s922 (pattern : Ten) : d285 (change pattern 7 3) = d285 pattern := by
  change (if pattern.c then d283 (change pattern 7 3) else d282 (change pattern 7 3)) = d285 pattern
  rw [s921, s915]
  rfl
theorem s923 (pattern : Ten) : d287 (change pattern 7 3) = d287 pattern := by
  change (if pattern.e then d10 (change pattern 7 3) else d285 (change pattern 7 3)) = d287 pattern
  rw [s890, s922]
  rfl
theorem s924 (pattern : Ten) : d288 (change pattern 7 3) = d287 pattern := by
  change d287 (change pattern 7 3) = d287 pattern
  exact s923 pattern
theorem s925 (pattern : Ten) : d4 (change pattern 7 8) = d4 pattern := by
  rfl
theorem s926 (pattern : Ten) : d10 (change pattern 7 8) = d10 pattern := by
  rfl
theorem s927 (pattern : Ten) : d42 (change pattern 7 8) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 7 8) else d4 (change pattern 7 8)) = d42 pattern
  rw [s926, s925]
  rfl
theorem s928 (pattern : Ten) : d48 (change pattern 7 8) = d42 pattern := by
  change d42 (change pattern 7 8) = d42 pattern
  exact s927 pattern
theorem s929 (pattern : Ten) : d124 (change pattern 7 8) = d42 pattern := by
  change d48 (change pattern 7 8) = d42 pattern
  exact s928 pattern
theorem s930 (pattern : Ten) : d125 (change pattern 7 8) = d42 pattern := by
  change (if pattern.g then d48 (change pattern 7 8) else d124 (change pattern 7 8)) = d42 pattern
  rw [s928, s929]
  simp only [ite_self]
theorem s931 (pattern : Ten) : d128 (change pattern 7 8) = d42 pattern := by
  change (if pattern.c then d48 (change pattern 7 8) else d125 (change pattern 7 8)) = d42 pattern
  rw [s928, s930]
  simp only [ite_self]
theorem s932 (pattern : Ten) : d20 (change pattern 7 8) = d10 pattern := by
  change d10 (change pattern 7 8) = d10 pattern
  exact s926 pattern
theorem s933 (pattern : Ten) : d126 (change pattern 7 8) = d524 pattern := by
  change (if pattern.g then d20 (change pattern 7 8) else d48 (change pattern 7 8)) = d524 pattern
  rw [s932, s928]
  rfl
theorem s934 (pattern : Ten) : d6 (change pattern 7 8) = d6 pattern := by
  rfl
theorem s935 (pattern : Ten) : d43 (change pattern 7 8) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 7 8) else d6 (change pattern 7 8)) = d43 pattern
  rw [s926, s934]
  rfl
theorem s936 (pattern : Ten) : d50 (change pattern 7 8) = d43 pattern := by
  change d43 (change pattern 7 8) = d43 pattern
  exact s935 pattern
theorem s937 (pattern : Ten) : d127 (change pattern 7 8) = d525 pattern := by
  change (if pattern.g then d20 (change pattern 7 8) else d50 (change pattern 7 8)) = d525 pattern
  rw [s932, s936]
  rfl
theorem s938 (pattern : Ten) : d129 (change pattern 7 8) = d526 pattern := by
  change (if pattern.c then d127 (change pattern 7 8) else d126 (change pattern 7 8)) = d526 pattern
  rw [s937, s933]
  rfl
theorem s939 (pattern : Ten) : d130 (change pattern 7 8) = d527 pattern := by
  change (if pattern.e then d129 (change pattern 7 8) else d128 (change pattern 7 8)) = d527 pattern
  rw [s938, s931]
  rfl
theorem s940 (pattern : Ten) : d131 (change pattern 7 8) = d528 pattern := by
  change (if pattern.e then d10 (change pattern 7 8) else d129 (change pattern 7 8)) = d528 pattern
  rw [s926, s938]
  rfl
theorem s941 (pattern : Ten) : d132 (change pattern 7 8) = d529 pattern := by
  change (if pattern.d then d131 (change pattern 7 8) else d130 (change pattern 7 8)) = d529 pattern
  rw [s940, s939]
  rfl
theorem s942 (pattern : Ten) : d5 (change pattern 7 8) = d5 pattern := by
  rfl
theorem s943 (pattern : Ten) : d193 (change pattern 7 8) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 7 8) else d4 (change pattern 7 8)) = d193 pattern
  rw [s942, s925]
  rfl
theorem s944 (pattern : Ten) : d197 (change pattern 7 8) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 7 8) else d193 (change pattern 7 8)) = d197 pattern
  rw [s926, s943]
  rfl
theorem s945 (pattern : Ten) : d202 (change pattern 7 8) = d197 pattern := by
  change d197 (change pattern 7 8) = d197 pattern
  exact s944 pattern
theorem s946 (pattern : Ten) : d280 (change pattern 7 8) = d197 pattern := by
  change d202 (change pattern 7 8) = d197 pattern
  exact s945 pattern
theorem s947 (pattern : Ten) : d281 (change pattern 7 8) = d197 pattern := by
  change (if pattern.g then d202 (change pattern 7 8) else d280 (change pattern 7 8)) = d197 pattern
  rw [s945, s946]
  simp only [ite_self]
theorem s948 (pattern : Ten) : d284 (change pattern 7 8) = d197 pattern := by
  change (if pattern.c then d202 (change pattern 7 8) else d281 (change pattern 7 8)) = d197 pattern
  rw [s945, s947]
  simp only [ite_self]
theorem s949 (pattern : Ten) : d282 (change pattern 7 8) = d531 pattern := by
  change (if pattern.g then d10 (change pattern 7 8) else d202 (change pattern 7 8)) = d531 pattern
  rw [s926, s945]
  rfl
theorem s950 (pattern : Ten) : d7 (change pattern 7 8) = d7 pattern := by
  rfl
theorem s951 (pattern : Ten) : d194 (change pattern 7 8) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 7 8) else d6 (change pattern 7 8)) = d194 pattern
  rw [s950, s934]
  rfl
theorem s952 (pattern : Ten) : d198 (change pattern 7 8) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 7 8) else d194 (change pattern 7 8)) = d198 pattern
  rw [s926, s951]
  rfl
theorem s953 (pattern : Ten) : d204 (change pattern 7 8) = d198 pattern := by
  change d198 (change pattern 7 8) = d198 pattern
  exact s952 pattern
theorem s954 (pattern : Ten) : d283 (change pattern 7 8) = d532 pattern := by
  change (if pattern.g then d10 (change pattern 7 8) else d204 (change pattern 7 8)) = d532 pattern
  rw [s926, s953]
  rfl
theorem s955 (pattern : Ten) : d285 (change pattern 7 8) = d533 pattern := by
  change (if pattern.c then d283 (change pattern 7 8) else d282 (change pattern 7 8)) = d533 pattern
  rw [s954, s949]
  rfl
theorem s956 (pattern : Ten) : d286 (change pattern 7 8) = d534 pattern := by
  change (if pattern.e then d285 (change pattern 7 8) else d284 (change pattern 7 8)) = d534 pattern
  rw [s955, s948]
  rfl
theorem s957 (pattern : Ten) : d287 (change pattern 7 8) = d535 pattern := by
  change (if pattern.e then d10 (change pattern 7 8) else d285 (change pattern 7 8)) = d535 pattern
  rw [s926, s955]
  rfl
theorem s958 (pattern : Ten) : d288 (change pattern 7 8) = d536 pattern := by
  change (if pattern.d then d287 (change pattern 7 8) else d286 (change pattern 7 8)) = d536 pattern
  rw [s957, s956]
  rfl
theorem s959 (pattern : Ten) : d0 (change pattern 3 4) = d0 pattern := by
  rfl
theorem s960 (pattern : Ten) : d2 (change pattern 3 4) = d2 pattern := by
  rfl
theorem s961 (pattern : Ten) : d15 (change pattern 3 4) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 3 4) else d0 (change pattern 3 4)) = d15 pattern
  rw [s960, s959]
  rfl
theorem s962 (pattern : Ten) : d4 (change pattern 3 4) = d4 pattern := by
  rfl
theorem s963 (pattern : Ten) : d10 (change pattern 3 4) = d10 pattern := by
  rfl
theorem s964 (pattern : Ten) : d42 (change pattern 3 4) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 3 4) else d4 (change pattern 3 4)) = d42 pattern
  rw [s963, s962]
  rfl
theorem s965 (pattern : Ten) : d48 (change pattern 3 4) = d48 pattern := by
  change (if pattern.i then d42 (change pattern 3 4) else d15 (change pattern 3 4)) = d48 pattern
  rw [s964, s961]
  rfl
theorem s966 (pattern : Ten) : d6 (change pattern 3 4) = d6 pattern := by
  rfl
theorem s967 (pattern : Ten) : d43 (change pattern 3 4) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 3 4) else d6 (change pattern 3 4)) = d43 pattern
  rw [s963, s966]
  rfl
theorem s968 (pattern : Ten) : d49 (change pattern 3 4) = d49 pattern := by
  change (if pattern.i then d10 (change pattern 3 4) else d43 (change pattern 3 4)) = d49 pattern
  rw [s963, s967]
  rfl
theorem s969 (pattern : Ten) : d54 (change pattern 3 4) = d54 pattern := by
  change (if pattern.h then d49 (change pattern 3 4) else d48 (change pattern 3 4)) = d54 pattern
  rw [s968, s965]
  rfl
theorem s970 (pattern : Ten) : d9 (change pattern 3 4) = d9 pattern := by
  rfl
theorem s971 (pattern : Ten) : d11 (change pattern 3 4) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 3 4) else d9 (change pattern 3 4)) = d11 pattern
  rw [s963, s970]
  rfl
theorem s972 (pattern : Ten) : d14 (change pattern 3 4) = d14 pattern := by
  change (if pattern.j then d10 (change pattern 3 4) else d11 (change pattern 3 4)) = d14 pattern
  rw [s963, s971]
  rfl
theorem s973 (pattern : Ten) : d20 (change pattern 3 4) = d20 pattern := by
  change (if pattern.i then d10 (change pattern 3 4) else d14 (change pattern 3 4)) = d20 pattern
  rw [s963, s972]
  rfl
theorem s974 (pattern : Ten) : d27 (change pattern 3 4) = d27 pattern := by
  change (if pattern.h then d10 (change pattern 3 4) else d20 (change pattern 3 4)) = d27 pattern
  rw [s963, s973]
  rfl
theorem s975 (pattern : Ten) : d58 (change pattern 3 4) = d58 pattern := by
  change (if pattern.g then d27 (change pattern 3 4) else d54 (change pattern 3 4)) = d58 pattern
  rw [s974, s969]
  rfl
theorem s976 (pattern : Ten) : d44 (change pattern 3 4) = d44 pattern := by
  change (if pattern.j then d4 (change pattern 3 4) else d2 (change pattern 3 4)) = d44 pattern
  rw [s962, s960]
  rfl
theorem s977 (pattern : Ten) : d50 (change pattern 3 4) = d50 pattern := by
  change (if pattern.i then d43 (change pattern 3 4) else d44 (change pattern 3 4)) = d50 pattern
  rw [s967, s976]
  rfl
theorem s978 (pattern : Ten) : d8 (change pattern 3 4) = d8 pattern := by
  rfl
theorem s979 (pattern : Ten) : d45 (change pattern 3 4) = d45 pattern := by
  change (if pattern.j then d10 (change pattern 3 4) else d8 (change pattern 3 4)) = d45 pattern
  rw [s963, s978]
  rfl
theorem s980 (pattern : Ten) : d51 (change pattern 3 4) = d51 pattern := by
  change (if pattern.i then d10 (change pattern 3 4) else d45 (change pattern 3 4)) = d51 pattern
  rw [s963, s979]
  rfl
theorem s981 (pattern : Ten) : d55 (change pattern 3 4) = d55 pattern := by
  change (if pattern.h then d51 (change pattern 3 4) else d50 (change pattern 3 4)) = d55 pattern
  rw [s980, s977]
  rfl
theorem s982 (pattern : Ten) : d59 (change pattern 3 4) = d59 pattern := by
  change (if pattern.g then d27 (change pattern 3 4) else d55 (change pattern 3 4)) = d59 pattern
  rw [s974, s981]
  rfl
theorem s983 (pattern : Ten) : d62 (change pattern 3 4) = d62 pattern := by
  change (if pattern.c then d59 (change pattern 3 4) else d58 (change pattern 3 4)) = d62 pattern
  rw [s982, s975]
  rfl
theorem s984 (pattern : Ten) : d64 (change pattern 3 4) = d62 pattern := by
  change d62 (change pattern 3 4) = d62 pattern
  exact s983 pattern
theorem s985 (pattern : Ten) : d133 (change pattern 3 4) = d62 pattern := by
  change d64 (change pattern 3 4) = d62 pattern
  exact s984 pattern
theorem s986 (pattern : Ten) : d1 (change pattern 3 4) = d1 pattern := by
  rfl
theorem s987 (pattern : Ten) : d171 (change pattern 3 4) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 3 4) else d0 (change pattern 3 4)) = d171 pattern
  rw [s986, s959]
  rfl
theorem s988 (pattern : Ten) : d3 (change pattern 3 4) = d3 pattern := by
  rfl
theorem s989 (pattern : Ten) : d172 (change pattern 3 4) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 3 4) else d2 (change pattern 3 4)) = d172 pattern
  rw [s988, s960]
  rfl
theorem s990 (pattern : Ten) : d174 (change pattern 3 4) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 3 4) else d171 (change pattern 3 4)) = d174 pattern
  rw [s989, s987]
  rfl
theorem s991 (pattern : Ten) : d5 (change pattern 3 4) = d5 pattern := by
  rfl
theorem s992 (pattern : Ten) : d193 (change pattern 3 4) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 3 4) else d4 (change pattern 3 4)) = d193 pattern
  rw [s991, s962]
  rfl
theorem s993 (pattern : Ten) : d197 (change pattern 3 4) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 3 4) else d193 (change pattern 3 4)) = d197 pattern
  rw [s963, s992]
  rfl
theorem s994 (pattern : Ten) : d202 (change pattern 3 4) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 3 4) else d174 (change pattern 3 4)) = d202 pattern
  rw [s993, s990]
  rfl
theorem s995 (pattern : Ten) : d7 (change pattern 3 4) = d7 pattern := by
  rfl
theorem s996 (pattern : Ten) : d194 (change pattern 3 4) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 3 4) else d6 (change pattern 3 4)) = d194 pattern
  rw [s995, s966]
  rfl
theorem s997 (pattern : Ten) : d198 (change pattern 3 4) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 3 4) else d194 (change pattern 3 4)) = d198 pattern
  rw [s963, s996]
  rfl
theorem s998 (pattern : Ten) : d203 (change pattern 3 4) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 3 4) else d198 (change pattern 3 4)) = d203 pattern
  rw [s963, s997]
  rfl
theorem s999 (pattern : Ten) : d207 (change pattern 3 4) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 3 4) else d202 (change pattern 3 4)) = d207 pattern
  rw [s998, s994]
  rfl
theorem s1000 (pattern : Ten) : d211 (change pattern 3 4) = d211 pattern := by
  change (if pattern.g then d10 (change pattern 3 4) else d207 (change pattern 3 4)) = d211 pattern
  rw [s963, s999]
  rfl
theorem s1001 (pattern : Ten) : d199 (change pattern 3 4) = d199 pattern := by
  change (if pattern.j then d193 (change pattern 3 4) else d172 (change pattern 3 4)) = d199 pattern
  rw [s992, s989]
  rfl
theorem s1002 (pattern : Ten) : d204 (change pattern 3 4) = d204 pattern := by
  change (if pattern.i then d198 (change pattern 3 4) else d199 (change pattern 3 4)) = d204 pattern
  rw [s997, s1001]
  rfl
theorem s1003 (pattern : Ten) : d195 (change pattern 3 4) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 3 4) else d8 (change pattern 3 4)) = d195 pattern
  rw [s970, s978]
  rfl
theorem s1004 (pattern : Ten) : d200 (change pattern 3 4) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 3 4) else d195 (change pattern 3 4)) = d200 pattern
  rw [s963, s1003]
  rfl
theorem s1005 (pattern : Ten) : d205 (change pattern 3 4) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 3 4) else d200 (change pattern 3 4)) = d205 pattern
  rw [s963, s1004]
  rfl
theorem s1006 (pattern : Ten) : d208 (change pattern 3 4) = d208 pattern := by
  change (if pattern.h then d205 (change pattern 3 4) else d204 (change pattern 3 4)) = d208 pattern
  rw [s1005, s1002]
  rfl
theorem s1007 (pattern : Ten) : d212 (change pattern 3 4) = d212 pattern := by
  change (if pattern.g then d10 (change pattern 3 4) else d208 (change pattern 3 4)) = d212 pattern
  rw [s963, s1006]
  rfl
theorem s1008 (pattern : Ten) : d215 (change pattern 3 4) = d215 pattern := by
  change (if pattern.c then d212 (change pattern 3 4) else d211 (change pattern 3 4)) = d215 pattern
  rw [s1007, s1000]
  rfl
theorem s1009 (pattern : Ten) : d218 (change pattern 3 4) = d215 pattern := by
  change d215 (change pattern 3 4) = d215 pattern
  exact s1008 pattern
theorem s1010 (pattern : Ten) : d289 (change pattern 3 4) = d215 pattern := by
  change d218 (change pattern 3 4) = d215 pattern
  exact s1009 pattern
theorem s1011 (pattern : Ten) : d6 (change pattern 3 7) = d6 pattern := by
  rfl
theorem s1012 (pattern : Ten) : d10 (change pattern 3 7) = d10 pattern := by
  rfl
theorem s1013 (pattern : Ten) : d43 (change pattern 3 7) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 3 7) else d6 (change pattern 3 7)) = d43 pattern
  rw [s1012, s1011]
  rfl
theorem s1014 (pattern : Ten) : d49 (change pattern 3 7) = d49 pattern := by
  change (if pattern.i then d10 (change pattern 3 7) else d43 (change pattern 3 7)) = d49 pattern
  rw [s1012, s1013]
  rfl
theorem s1015 (pattern : Ten) : d54 (change pattern 3 7) = d49 pattern := by
  change d49 (change pattern 3 7) = d49 pattern
  exact s1014 pattern
theorem s1016 (pattern : Ten) : d27 (change pattern 3 7) = d10 pattern := by
  change d10 (change pattern 3 7) = d10 pattern
  exact s1012 pattern
theorem s1017 (pattern : Ten) : d58 (change pattern 3 7) = d544 pattern := by
  change (if pattern.g then d27 (change pattern 3 7) else d54 (change pattern 3 7)) = d544 pattern
  rw [s1016, s1015]
  rfl
theorem s1018 (pattern : Ten) : d8 (change pattern 3 7) = d8 pattern := by
  rfl
theorem s1019 (pattern : Ten) : d45 (change pattern 3 7) = d45 pattern := by
  change (if pattern.j then d10 (change pattern 3 7) else d8 (change pattern 3 7)) = d45 pattern
  rw [s1012, s1018]
  rfl
theorem s1020 (pattern : Ten) : d51 (change pattern 3 7) = d51 pattern := by
  change (if pattern.i then d10 (change pattern 3 7) else d45 (change pattern 3 7)) = d51 pattern
  rw [s1012, s1019]
  rfl
theorem s1021 (pattern : Ten) : d55 (change pattern 3 7) = d51 pattern := by
  change d51 (change pattern 3 7) = d51 pattern
  exact s1020 pattern
theorem s1022 (pattern : Ten) : d59 (change pattern 3 7) = d545 pattern := by
  change (if pattern.g then d27 (change pattern 3 7) else d55 (change pattern 3 7)) = d545 pattern
  rw [s1016, s1021]
  rfl
theorem s1023 (pattern : Ten) : d62 (change pattern 3 7) = d546 pattern := by
  change (if pattern.c then d59 (change pattern 3 7) else d58 (change pattern 3 7)) = d546 pattern
  rw [s1022, s1017]
  rfl
theorem s1024 (pattern : Ten) : d64 (change pattern 3 7) = d547 pattern := by
  change (if pattern.e then d62 (change pattern 3 7) else d54 (change pattern 3 7)) = d547 pattern
  rw [s1023, s1015]
  rfl
theorem s1025 (pattern : Ten) : d133 (change pattern 3 7) = d547 pattern := by
  change d64 (change pattern 3 7) = d547 pattern
  exact s1024 pattern
theorem s1026 (pattern : Ten) : d7 (change pattern 3 7) = d7 pattern := by
  rfl
theorem s1027 (pattern : Ten) : d194 (change pattern 3 7) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 3 7) else d6 (change pattern 3 7)) = d194 pattern
  rw [s1026, s1011]
  rfl
theorem s1028 (pattern : Ten) : d198 (change pattern 3 7) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 3 7) else d194 (change pattern 3 7)) = d198 pattern
  rw [s1012, s1027]
  rfl
theorem s1029 (pattern : Ten) : d203 (change pattern 3 7) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 3 7) else d198 (change pattern 3 7)) = d203 pattern
  rw [s1012, s1028]
  rfl
theorem s1030 (pattern : Ten) : d207 (change pattern 3 7) = d203 pattern := by
  change d203 (change pattern 3 7) = d203 pattern
  exact s1029 pattern
theorem s1031 (pattern : Ten) : d211 (change pattern 3 7) = d549 pattern := by
  change (if pattern.g then d10 (change pattern 3 7) else d207 (change pattern 3 7)) = d549 pattern
  rw [s1012, s1030]
  rfl
theorem s1032 (pattern : Ten) : d9 (change pattern 3 7) = d9 pattern := by
  rfl
theorem s1033 (pattern : Ten) : d195 (change pattern 3 7) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 3 7) else d8 (change pattern 3 7)) = d195 pattern
  rw [s1032, s1018]
  rfl
theorem s1034 (pattern : Ten) : d200 (change pattern 3 7) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 3 7) else d195 (change pattern 3 7)) = d200 pattern
  rw [s1012, s1033]
  rfl
theorem s1035 (pattern : Ten) : d205 (change pattern 3 7) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 3 7) else d200 (change pattern 3 7)) = d205 pattern
  rw [s1012, s1034]
  rfl
theorem s1036 (pattern : Ten) : d208 (change pattern 3 7) = d205 pattern := by
  change d205 (change pattern 3 7) = d205 pattern
  exact s1035 pattern
theorem s1037 (pattern : Ten) : d212 (change pattern 3 7) = d550 pattern := by
  change (if pattern.g then d10 (change pattern 3 7) else d208 (change pattern 3 7)) = d550 pattern
  rw [s1012, s1036]
  rfl
theorem s1038 (pattern : Ten) : d215 (change pattern 3 7) = d551 pattern := by
  change (if pattern.c then d212 (change pattern 3 7) else d211 (change pattern 3 7)) = d551 pattern
  rw [s1037, s1031]
  rfl
theorem s1039 (pattern : Ten) : d218 (change pattern 3 7) = d552 pattern := by
  change (if pattern.e then d215 (change pattern 3 7) else d207 (change pattern 3 7)) = d552 pattern
  rw [s1038, s1030]
  rfl
theorem s1040 (pattern : Ten) : d289 (change pattern 3 7) = d552 pattern := by
  change d218 (change pattern 3 7) = d552 pattern
  exact s1039 pattern
theorem s1041 (pattern : Ten) : d0 (change pattern 4 2) = d0 pattern := by
  rfl
theorem s1042 (pattern : Ten) : d2 (change pattern 4 2) = d2 pattern := by
  rfl
theorem s1043 (pattern : Ten) : d15 (change pattern 4 2) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 4 2) else d0 (change pattern 4 2)) = d15 pattern
  rw [s1042, s1041]
  rfl
theorem s1044 (pattern : Ten) : d4 (change pattern 4 2) = d4 pattern := by
  rfl
theorem s1045 (pattern : Ten) : d10 (change pattern 4 2) = d10 pattern := by
  rfl
theorem s1046 (pattern : Ten) : d42 (change pattern 4 2) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 4 2) else d4 (change pattern 4 2)) = d42 pattern
  rw [s1045, s1044]
  rfl
theorem s1047 (pattern : Ten) : d48 (change pattern 4 2) = d48 pattern := by
  change (if pattern.i then d42 (change pattern 4 2) else d15 (change pattern 4 2)) = d48 pattern
  rw [s1046, s1043]
  rfl
theorem s1048 (pattern : Ten) : d6 (change pattern 4 2) = d6 pattern := by
  rfl
theorem s1049 (pattern : Ten) : d43 (change pattern 4 2) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 4 2) else d6 (change pattern 4 2)) = d43 pattern
  rw [s1045, s1048]
  rfl
end NetHack.Sokoban41.Diagram
