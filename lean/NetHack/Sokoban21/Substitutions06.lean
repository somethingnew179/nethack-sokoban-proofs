/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions05
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s900 (pattern : Twelve) : d237 (change pattern 7 12) = d0 pattern := by
  change d0 (change pattern 7 12) = d0 pattern
  exact s899 pattern
theorem s901 (pattern : Twelve) : d1 (change pattern 7 12) = d1 pattern := by
  rfl
theorem s902 (pattern : Twelve) : d7 (change pattern 7 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 7 12) else d0 (change pattern 7 12)) = d7 pattern
  rw [s901, s899]
  rfl
theorem s903 (pattern : Twelve) : d17 (change pattern 7 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 7 12) else d0 (change pattern 7 12)) = d17 pattern
  rw [s902, s899]
  rfl
theorem s904 (pattern : Twelve) : d27 (change pattern 7 12) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 7 12) else d17 (change pattern 7 12)) = d27 pattern
  rw [s901, s903]
  rfl
theorem s905 (pattern : Twelve) : d940 (change pattern 7 12) = d27 pattern := by
  change d27 (change pattern 7 12) = d27 pattern
  exact s904 pattern
theorem s906 (pattern : Twelve) : d947 (change pattern 7 12) = d1902 pattern := by
  change (if pattern.f then d940 (change pattern 7 12) else d237 (change pattern 7 12)) = d1902 pattern
  rw [s905, s900]
  rfl
theorem s907 (pattern : Twelve) : d941 (change pattern 7 12) = d17 pattern := by
  change d17 (change pattern 7 12) = d17 pattern
  exact s903 pattern
theorem s908 (pattern : Twelve) : d2 (change pattern 7 12) = d2 pattern := by
  rfl
theorem s909 (pattern : Twelve) : d10 (change pattern 7 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 7 12) else d0 (change pattern 7 12)) = d10 pattern
  rw [s908, s899]
  rfl
theorem s910 (pattern : Twelve) : d3 (change pattern 7 12) = d3 pattern := by
  rfl
theorem s911 (pattern : Twelve) : d11 (change pattern 7 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 7 12) else d1 (change pattern 7 12)) = d11 pattern
  rw [s910, s901]
  rfl
theorem s912 (pattern : Twelve) : d19 (change pattern 7 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 7 12) else d10 (change pattern 7 12)) = d19 pattern
  rw [s911, s909]
  rfl
theorem s913 (pattern : Twelve) : d4 (change pattern 7 12) = d4 pattern := by
  rfl
theorem s914 (pattern : Twelve) : d16 (change pattern 7 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 7 12) else d2 (change pattern 7 12)) = d16 pattern
  rw [s913, s908]
  rfl
theorem s915 (pattern : Twelve) : d5 (change pattern 7 12) = d5 pattern := by
  rfl
theorem s916 (pattern : Twelve) : d12 (change pattern 7 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 7 12) else d3 (change pattern 7 12)) = d12 pattern
  rw [s915, s910]
  rfl
theorem s917 (pattern : Twelve) : d25 (change pattern 7 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 7 12) else d16 (change pattern 7 12)) = d25 pattern
  rw [s916, s914]
  rfl
theorem s918 (pattern : Twelve) : d817 (change pattern 7 12) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 7 12) else d19 (change pattern 7 12)) = d817 pattern
  rw [s917, s912]
  rfl
theorem s919 (pattern : Twelve) : d942 (change pattern 7 12) = d817 pattern := by
  change d817 (change pattern 7 12) = d817 pattern
  exact s918 pattern
theorem s920 (pattern : Twelve) : d948 (change pattern 7 12) = d1903 pattern := by
  change (if pattern.f then d942 (change pattern 7 12) else d941 (change pattern 7 12)) = d1903 pattern
  rw [s919, s907]
  rfl
theorem s921 (pattern : Twelve) : d955 (change pattern 7 12) = d1904 pattern := by
  change (if pattern.e then d948 (change pattern 7 12) else d947 (change pattern 7 12)) = d1904 pattern
  rw [s920, s906]
  rfl
theorem s922 (pattern : Twelve) : d30 (change pattern 7 12) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 7 12) else d0 (change pattern 7 12)) = d30 pattern
  rw [s908, s899]
  rfl
theorem s923 (pattern : Twelve) : d240 (change pattern 7 12) = d30 pattern := by
  change d30 (change pattern 7 12) = d30 pattern
  exact s922 pattern
theorem s924 (pattern : Twelve) : d9 (change pattern 7 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 7 12) else d2 (change pattern 7 12)) = d9 pattern
  rw [s910, s908]
  rfl
theorem s925 (pattern : Twelve) : d23 (change pattern 7 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 7 12) else d2 (change pattern 7 12)) = d23 pattern
  rw [s924, s908]
  rfl
theorem s926 (pattern : Twelve) : d34 (change pattern 7 12) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 7 12) else d17 (change pattern 7 12)) = d34 pattern
  rw [s925, s903]
  rfl
theorem s927 (pattern : Twelve) : d241 (change pattern 7 12) = d34 pattern := by
  change d34 (change pattern 7 12) = d34 pattern
  exact s926 pattern
theorem s928 (pattern : Twelve) : d259 (change pattern 7 12) = d1905 pattern := by
  change (if pattern.f then d241 (change pattern 7 12) else d240 (change pattern 7 12)) = d1905 pattern
  rw [s927, s923]
  rfl
theorem s929 (pattern : Twelve) : d949 (change pattern 7 12) = d1906 pattern := by
  change (if pattern.f then d942 (change pattern 7 12) else d241 (change pattern 7 12)) = d1906 pattern
  rw [s919, s927]
  rfl
theorem s930 (pattern : Twelve) : d956 (change pattern 7 12) = d1907 pattern := by
  change (if pattern.e then d949 (change pattern 7 12) else d259 (change pattern 7 12)) = d1907 pattern
  rw [s929, s928]
  rfl
theorem s931 (pattern : Twelve) : d963 (change pattern 7 12) = d1908 pattern := by
  change (if pattern.j then d956 (change pattern 7 12) else d955 (change pattern 7 12)) = d1908 pattern
  rw [s930, s921]
  rfl
theorem s932 (pattern : Twelve) : d244 (change pattern 7 12) = d0 pattern := by
  change d0 (change pattern 7 12) = d0 pattern
  exact s899 pattern
theorem s933 (pattern : Twelve) : d943 (change pattern 7 12) = d27 pattern := by
  change d27 (change pattern 7 12) = d27 pattern
  exact s904 pattern
theorem s934 (pattern : Twelve) : d950 (change pattern 7 12) = d1902 pattern := by
  change (if pattern.f then d943 (change pattern 7 12) else d244 (change pattern 7 12)) = d1902 pattern
  rw [s933, s932]
  rfl
theorem s935 (pattern : Twelve) : d944 (change pattern 7 12) = d17 pattern := by
  change d17 (change pattern 7 12) = d17 pattern
  exact s903 pattern
theorem s936 (pattern : Twelve) : d951 (change pattern 7 12) = d1903 pattern := by
  change (if pattern.f then d942 (change pattern 7 12) else d944 (change pattern 7 12)) = d1903 pattern
  rw [s919, s935]
  rfl
theorem s937 (pattern : Twelve) : d957 (change pattern 7 12) = d1904 pattern := by
  change (if pattern.e then d951 (change pattern 7 12) else d950 (change pattern 7 12)) = d1904 pattern
  rw [s936, s934]
  rfl
theorem s938 (pattern : Twelve) : d246 (change pattern 7 12) = d30 pattern := by
  change d30 (change pattern 7 12) = d30 pattern
  exact s922 pattern
theorem s939 (pattern : Twelve) : d263 (change pattern 7 12) = d1905 pattern := by
  change (if pattern.f then d241 (change pattern 7 12) else d246 (change pattern 7 12)) = d1905 pattern
  rw [s927, s938]
  rfl
theorem s940 (pattern : Twelve) : d958 (change pattern 7 12) = d1907 pattern := by
  change (if pattern.e then d949 (change pattern 7 12) else d263 (change pattern 7 12)) = d1907 pattern
  rw [s929, s939]
  rfl
theorem s941 (pattern : Twelve) : d964 (change pattern 7 12) = d1908 pattern := by
  change (if pattern.j then d958 (change pattern 7 12) else d957 (change pattern 7 12)) = d1908 pattern
  rw [s940, s937]
  rfl
theorem s942 (pattern : Twelve) : d970 (change pattern 7 12) = d1908 pattern := by
  change (if pattern.d then d964 (change pattern 7 12) else d963 (change pattern 7 12)) = d1908 pattern
  rw [s941, s931]
  simp only [ite_self]
theorem s943 (pattern : Twelve) : d248 (change pattern 7 12) = d30 pattern := by
  change d30 (change pattern 7 12) = d30 pattern
  exact s922 pattern
theorem s944 (pattern : Twelve) : d265 (change pattern 7 12) = d1905 pattern := by
  change (if pattern.f then d241 (change pattern 7 12) else d248 (change pattern 7 12)) = d1905 pattern
  rw [s927, s943]
  rfl
theorem s945 (pattern : Twelve) : d959 (change pattern 7 12) = d1907 pattern := by
  change (if pattern.e then d949 (change pattern 7 12) else d265 (change pattern 7 12)) = d1907 pattern
  rw [s929, s944]
  rfl
theorem s946 (pattern : Twelve) : d38 (change pattern 7 12) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 7 12) else d2 (change pattern 7 12)) = d38 pattern
  rw [s913, s908]
  rfl
theorem s947 (pattern : Twelve) : d250 (change pattern 7 12) = d38 pattern := by
  change d38 (change pattern 7 12) = d38 pattern
  exact s946 pattern
theorem s948 (pattern : Twelve) : d15 (change pattern 7 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 7 12) else d4 (change pattern 7 12)) = d15 pattern
  rw [s915, s913]
  rfl
theorem s949 (pattern : Twelve) : d24 (change pattern 7 12) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 7 12) else d4 (change pattern 7 12)) = d24 pattern
  rw [s948, s913]
  rfl
theorem s950 (pattern : Twelve) : d41 (change pattern 7 12) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 7 12) else d23 (change pattern 7 12)) = d41 pattern
  rw [s949, s925]
  rfl
theorem s951 (pattern : Twelve) : d251 (change pattern 7 12) = d41 pattern := by
  change d41 (change pattern 7 12) = d41 pattern
  exact s950 pattern
theorem s952 (pattern : Twelve) : d267 (change pattern 7 12) = d1909 pattern := by
  change (if pattern.f then d251 (change pattern 7 12) else d250 (change pattern 7 12)) = d1909 pattern
  rw [s951, s947]
  rfl
theorem s953 (pattern : Twelve) : d6 (change pattern 7 12) = d6 pattern := by
  rfl
theorem s954 (pattern : Twelve) : d13 (change pattern 7 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 7 12) else d4 (change pattern 7 12)) = d13 pattern
  rw [s953, s913]
  rfl
theorem s955 (pattern : Twelve) : d14 (change pattern 7 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 7 12) else d5 (change pattern 7 12)) = d14 pattern
  rw [s953, s915]
  rfl
theorem s956 (pattern : Twelve) : d21 (change pattern 7 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 7 12) else d13 (change pattern 7 12)) = d21 pattern
  rw [s955, s954]
  rfl
theorem s957 (pattern : Twelve) : d821 (change pattern 7 12) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 7 12) else d25 (change pattern 7 12)) = d821 pattern
  rw [s956, s917]
  rfl
theorem s958 (pattern : Twelve) : d945 (change pattern 7 12) = d821 pattern := by
  change d821 (change pattern 7 12) = d821 pattern
  exact s957 pattern
theorem s959 (pattern : Twelve) : d952 (change pattern 7 12) = d1910 pattern := by
  change (if pattern.f then d945 (change pattern 7 12) else d251 (change pattern 7 12)) = d1910 pattern
  rw [s958, s951]
  rfl
theorem s960 (pattern : Twelve) : d960 (change pattern 7 12) = d1911 pattern := by
  change (if pattern.e then d952 (change pattern 7 12) else d267 (change pattern 7 12)) = d1911 pattern
  rw [s959, s952]
  rfl
theorem s961 (pattern : Twelve) : d965 (change pattern 7 12) = d1912 pattern := by
  change (if pattern.j then d960 (change pattern 7 12) else d959 (change pattern 7 12)) = d1912 pattern
  rw [s960, s945]
  rfl
theorem s962 (pattern : Twelve) : d966 (change pattern 7 12) = d1913 pattern := by
  change (if pattern.j then d6 (change pattern 7 12) else d958 (change pattern 7 12)) = d1913 pattern
  rw [s953, s940]
  rfl
theorem s963 (pattern : Twelve) : d971 (change pattern 7 12) = d1914 pattern := by
  change (if pattern.d then d966 (change pattern 7 12) else d965 (change pattern 7 12)) = d1914 pattern
  rw [s962, s961]
  rfl
theorem s964 (pattern : Twelve) : d973 (change pattern 7 12) = d1915 pattern := by
  change (if pattern.c then d971 (change pattern 7 12) else d970 (change pattern 7 12)) = d1915 pattern
  rw [s963, s942]
  rfl
theorem s965 (pattern : Twelve) : d253 (change pattern 7 12) = d0 pattern := by
  change d0 (change pattern 7 12) = d0 pattern
  exact s899 pattern
theorem s966 (pattern : Twelve) : d953 (change pattern 7 12) = d1902 pattern := by
  change (if pattern.f then d943 (change pattern 7 12) else d253 (change pattern 7 12)) = d1902 pattern
  rw [s933, s965]
  rfl
theorem s967 (pattern : Twelve) : d823 (change pattern 7 12) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 7 12) else d17 (change pattern 7 12)) = d823 pattern
  rw [s908, s903]
  rfl
theorem s968 (pattern : Twelve) : d946 (change pattern 7 12) = d823 pattern := by
  change d823 (change pattern 7 12) = d823 pattern
  exact s967 pattern
theorem s969 (pattern : Twelve) : d954 (change pattern 7 12) = d1916 pattern := by
  change (if pattern.f then d942 (change pattern 7 12) else d946 (change pattern 7 12)) = d1916 pattern
  rw [s919, s968]
  rfl
theorem s970 (pattern : Twelve) : d961 (change pattern 7 12) = d1917 pattern := by
  change (if pattern.e then d954 (change pattern 7 12) else d953 (change pattern 7 12)) = d1917 pattern
  rw [s969, s966]
  rfl
theorem s971 (pattern : Twelve) : d967 (change pattern 7 12) = d1918 pattern := by
  change (if pattern.j then d958 (change pattern 7 12) else d961 (change pattern 7 12)) = d1918 pattern
  rw [s940, s970]
  rfl
theorem s972 (pattern : Twelve) : d968 (change pattern 7 12) = d1912 pattern := by
  change (if pattern.j then d960 (change pattern 7 12) else d958 (change pattern 7 12)) = d1912 pattern
  rw [s960, s940]
  rfl
theorem s973 (pattern : Twelve) : d972 (change pattern 7 12) = d1914 pattern := by
  change (if pattern.d then d966 (change pattern 7 12) else d968 (change pattern 7 12)) = d1914 pattern
  rw [s962, s972]
  rfl
theorem s974 (pattern : Twelve) : d974 (change pattern 7 12) = d1919 pattern := by
  change (if pattern.c then d972 (change pattern 7 12) else d967 (change pattern 7 12)) = d1919 pattern
  rw [s973, s971]
  rfl
theorem s975 (pattern : Twelve) : d976 (change pattern 7 12) = d1920 pattern := by
  change (if pattern.g then d974 (change pattern 7 12) else d973 (change pattern 7 12)) = d1920 pattern
  rw [s974, s964]
  rfl
theorem s976 (pattern : Twelve) : d962 (change pattern 7 12) = d1904 pattern := by
  change (if pattern.e then d951 (change pattern 7 12) else d953 (change pattern 7 12)) = d1904 pattern
  rw [s936, s966]
  rfl
theorem s977 (pattern : Twelve) : d969 (change pattern 7 12) = d1908 pattern := by
  change (if pattern.j then d958 (change pattern 7 12) else d962 (change pattern 7 12)) = d1908 pattern
  rw [s940, s976]
  rfl
theorem s978 (pattern : Twelve) : d975 (change pattern 7 12) = d1915 pattern := by
  change (if pattern.c then d972 (change pattern 7 12) else d969 (change pattern 7 12)) = d1915 pattern
  rw [s973, s977]
  rfl
theorem s979 (pattern : Twelve) : d977 (change pattern 7 12) = d1920 pattern := by
  change (if pattern.g then d974 (change pattern 7 12) else d975 (change pattern 7 12)) = d1920 pattern
  rw [s974, s978]
  rfl
theorem s980 (pattern : Twelve) : d978 (change pattern 7 12) = d1920 pattern := by
  change (if pattern.b then d977 (change pattern 7 12) else d976 (change pattern 7 12)) = d1920 pattern
  rw [s979, s975]
  simp only [ite_self]
theorem s981 (pattern : Twelve) : d979 (change pattern 7 12) = d1920 pattern := by
  change (if pattern.a then d977 (change pattern 7 12) else d978 (change pattern 7 12)) = d1920 pattern
  rw [s979, s980]
  simp only [ite_self]
theorem s982 (pattern : Twelve) : d8 (change pattern 7 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 7 12) else d1 (change pattern 7 12)) = d8 pattern
  rw [s908, s901]
  rfl
theorem s983 (pattern : Twelve) : d1275 (change pattern 7 12) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 7 12) else d7 (change pattern 7 12)) = d1275 pattern
  rw [s982, s902]
  rfl
theorem s984 (pattern : Twelve) : d872 (change pattern 7 12) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 7 12) else d1 (change pattern 7 12)) = d872 pattern
  rw [s982, s901]
  rfl
theorem s985 (pattern : Twelve) : d1278 (change pattern 7 12) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 7 12) else d1275 (change pattern 7 12)) = d1278 pattern
  rw [s984, s983]
  rfl
theorem s986 (pattern : Twelve) : d1380 (change pattern 7 12) = d1278 pattern := by
  change d1278 (change pattern 7 12) = d1278 pattern
  exact s985 pattern
theorem s987 (pattern : Twelve) : d1385 (change pattern 7 12) = d1921 pattern := by
  change (if pattern.f then d1380 (change pattern 7 12) else d941 (change pattern 7 12)) = d1921 pattern
  rw [s986, s907]
  rfl
theorem s988 (pattern : Twelve) : d1381 (change pattern 7 12) = d19 pattern := by
  change d19 (change pattern 7 12) = d19 pattern
  exact s912 pattern
theorem s989 (pattern : Twelve) : d1386 (change pattern 7 12) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 7 12) else d1381 (change pattern 7 12)) = d1294 pattern
  rw [s953, s988]
  rfl
theorem s990 (pattern : Twelve) : d1393 (change pattern 7 12) = d1922 pattern := by
  change (if pattern.e then d1386 (change pattern 7 12) else d1385 (change pattern 7 12)) = d1922 pattern
  rw [s989, s987]
  rfl
theorem s991 (pattern : Twelve) : d117 (change pattern 7 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 7 12) else d3 (change pattern 7 12)) = d117 pattern
  rw [s913, s910]
  rfl
theorem s992 (pattern : Twelve) : d1276 (change pattern 7 12) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 7 12) else d9 (change pattern 7 12)) = d1276 pattern
  rw [s991, s924]
  rfl
theorem s993 (pattern : Twelve) : d1279 (change pattern 7 12) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 7 12) else d1275 (change pattern 7 12)) = d1279 pattern
  rw [s992, s983]
  rfl
theorem s994 (pattern : Twelve) : d1382 (change pattern 7 12) = d1279 pattern := by
  change d1279 (change pattern 7 12) = d1279 pattern
  exact s993 pattern
theorem s995 (pattern : Twelve) : d1387 (change pattern 7 12) = d1923 pattern := by
  change (if pattern.f then d1382 (change pattern 7 12) else d241 (change pattern 7 12)) = d1923 pattern
  rw [s994, s927]
  rfl
theorem s996 (pattern : Twelve) : d1388 (change pattern 7 12) = d1298 pattern := by
  change (if pattern.f then d6 (change pattern 7 12) else d942 (change pattern 7 12)) = d1298 pattern
  rw [s953, s919]
  rfl
theorem s997 (pattern : Twelve) : d1394 (change pattern 7 12) = d1924 pattern := by
  change (if pattern.e then d1388 (change pattern 7 12) else d1387 (change pattern 7 12)) = d1924 pattern
  rw [s996, s995]
  rfl
theorem s998 (pattern : Twelve) : d1398 (change pattern 7 12) = d1925 pattern := by
  change (if pattern.j then d1394 (change pattern 7 12) else d1393 (change pattern 7 12)) = d1925 pattern
  rw [s997, s990]
  rfl
theorem s999 (pattern : Twelve) : d1389 (change pattern 7 12) = d1921 pattern := by
  change (if pattern.f then d1380 (change pattern 7 12) else d944 (change pattern 7 12)) = d1921 pattern
  rw [s986, s935]
  rfl
theorem s1000 (pattern : Twelve) : d1395 (change pattern 7 12) = d1922 pattern := by
  change (if pattern.e then d1386 (change pattern 7 12) else d1389 (change pattern 7 12)) = d1922 pattern
  rw [s989, s999]
  rfl
theorem s1001 (pattern : Twelve) : d1399 (change pattern 7 12) = d1925 pattern := by
  change (if pattern.j then d1394 (change pattern 7 12) else d1395 (change pattern 7 12)) = d1925 pattern
  rw [s997, s1000]
  rfl
theorem s1002 (pattern : Twelve) : d1403 (change pattern 7 12) = d1925 pattern := by
  change (if pattern.d then d1399 (change pattern 7 12) else d1398 (change pattern 7 12)) = d1925 pattern
  rw [s1001, s998]
  simp only [ite_self]
theorem s1003 (pattern : Twelve) : d1277 (change pattern 7 12) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 7 12) else d15 (change pattern 7 12)) = d1277 pattern
  rw [s955, s948]
  rfl
theorem s1004 (pattern : Twelve) : d1282 (change pattern 7 12) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 7 12) else d1276 (change pattern 7 12)) = d1282 pattern
  rw [s1003, s992]
  rfl
theorem s1005 (pattern : Twelve) : d1383 (change pattern 7 12) = d1282 pattern := by
  change d1282 (change pattern 7 12) = d1282 pattern
  exact s1004 pattern
theorem s1006 (pattern : Twelve) : d1390 (change pattern 7 12) = d1926 pattern := by
  change (if pattern.f then d1383 (change pattern 7 12) else d251 (change pattern 7 12)) = d1926 pattern
  rw [s1005, s951]
  rfl
theorem s1007 (pattern : Twelve) : d1391 (change pattern 7 12) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 7 12) else d945 (change pattern 7 12)) = d1653 pattern
  rw [s953, s958]
  rfl
theorem s1008 (pattern : Twelve) : d1396 (change pattern 7 12) = d1927 pattern := by
  change (if pattern.e then d1391 (change pattern 7 12) else d1390 (change pattern 7 12)) = d1927 pattern
  rw [s1007, s1006]
  rfl
theorem s1009 (pattern : Twelve) : d1400 (change pattern 7 12) = d1928 pattern := by
  change (if pattern.j then d1396 (change pattern 7 12) else d1394 (change pattern 7 12)) = d1928 pattern
  rw [s1008, s997]
  rfl
theorem s1010 (pattern : Twelve) : d1401 (change pattern 7 12) = d1929 pattern := by
  change (if pattern.j then d6 (change pattern 7 12) else d1394 (change pattern 7 12)) = d1929 pattern
  rw [s953, s997]
  rfl
theorem s1011 (pattern : Twelve) : d1404 (change pattern 7 12) = d1930 pattern := by
  change (if pattern.d then d1401 (change pattern 7 12) else d1400 (change pattern 7 12)) = d1930 pattern
  rw [s1010, s1009]
  rfl
theorem s1012 (pattern : Twelve) : d1405 (change pattern 7 12) = d1931 pattern := by
  change (if pattern.c then d1404 (change pattern 7 12) else d1403 (change pattern 7 12)) = d1931 pattern
  rw [s1011, s1002]
  rfl
theorem s1013 (pattern : Twelve) : d1283 (change pattern 7 12) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 7 12) else d19 (change pattern 7 12)) = d1283 pattern
  rw [s925, s912]
  rfl
theorem s1014 (pattern : Twelve) : d1384 (change pattern 7 12) = d1283 pattern := by
  change d1283 (change pattern 7 12) = d1283 pattern
  exact s1013 pattern
theorem s1015 (pattern : Twelve) : d1392 (change pattern 7 12) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 7 12) else d1384 (change pattern 7 12)) = d1301 pattern
  rw [s953, s1014]
  rfl
theorem s1016 (pattern : Twelve) : d1397 (change pattern 7 12) = d1932 pattern := by
  change (if pattern.e then d1392 (change pattern 7 12) else d1389 (change pattern 7 12)) = d1932 pattern
  rw [s1015, s999]
  rfl
theorem s1017 (pattern : Twelve) : d1402 (change pattern 7 12) = d1933 pattern := by
  change (if pattern.j then d1394 (change pattern 7 12) else d1397 (change pattern 7 12)) = d1933 pattern
  rw [s997, s1016]
  rfl
theorem s1018 (pattern : Twelve) : d1406 (change pattern 7 12) = d1934 pattern := by
  change (if pattern.c then d1404 (change pattern 7 12) else d1402 (change pattern 7 12)) = d1934 pattern
  rw [s1011, s1017]
  rfl
theorem s1019 (pattern : Twelve) : d1408 (change pattern 7 12) = d1935 pattern := by
  change (if pattern.g then d1406 (change pattern 7 12) else d1405 (change pattern 7 12)) = d1935 pattern
  rw [s1018, s1012]
  rfl
theorem s1020 (pattern : Twelve) : d1407 (change pattern 7 12) = d1931 pattern := by
  change (if pattern.c then d1404 (change pattern 7 12) else d1399 (change pattern 7 12)) = d1931 pattern
  rw [s1011, s1001]
  rfl
theorem s1021 (pattern : Twelve) : d1409 (change pattern 7 12) = d1935 pattern := by
  change (if pattern.g then d1406 (change pattern 7 12) else d1407 (change pattern 7 12)) = d1935 pattern
  rw [s1018, s1020]
  rfl
theorem s1022 (pattern : Twelve) : d1410 (change pattern 7 12) = d1935 pattern := by
  change (if pattern.b then d1409 (change pattern 7 12) else d1408 (change pattern 7 12)) = d1935 pattern
  rw [s1021, s1019]
  simp only [ite_self]
theorem s1023 (pattern : Twelve) : d1411 (change pattern 7 12) = d1935 pattern := by
  change (if pattern.a then d1409 (change pattern 7 12) else d1410 (change pattern 7 12)) = d1935 pattern
  rw [s1021, s1022]
  simp only [ite_self]
theorem s1024 (pattern : Twelve) : d1324 (change pattern 7 12) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 7 12) else d11 (change pattern 7 12)) = d1324 pattern
  rw [s914, s911]
  rfl
theorem s1025 (pattern : Twelve) : d1689 (change pattern 7 12) = d1324 pattern := by
  change d1324 (change pattern 7 12) = d1324 pattern
  exact s1024 pattern
theorem s1026 (pattern : Twelve) : d1693 (change pattern 7 12) = d1649 pattern := by
  change (if pattern.f then d1689 (change pattern 7 12) else d1381 (change pattern 7 12)) = d1649 pattern
  rw [s1025, s988]
  rfl
theorem s1027 (pattern : Twelve) : d1690 (change pattern 7 12) = d25 pattern := by
  change d25 (change pattern 7 12) = d25 pattern
  exact s917 pattern
theorem s1028 (pattern : Twelve) : d1694 (change pattern 7 12) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 7 12) else d1690 (change pattern 7 12)) = d1650 pattern
  rw [s953, s1027]
  rfl
theorem s1029 (pattern : Twelve) : d1697 (change pattern 7 12) = d1656 pattern := by
  change (if pattern.e then d1694 (change pattern 7 12) else d1693 (change pattern 7 12)) = d1656 pattern
  rw [s1028, s1026]
  rfl
theorem s1030 (pattern : Twelve) : d20 (change pattern 7 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 7 12) else d12 (change pattern 7 12)) = d20 pattern
  rw [s954, s916]
  rfl
theorem s1031 (pattern : Twelve) : d1644 (change pattern 7 12) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 7 12) else d1324 (change pattern 7 12)) = d1644 pattern
  rw [s1030, s1024]
  rfl
theorem s1032 (pattern : Twelve) : d1691 (change pattern 7 12) = d1644 pattern := by
  change d1644 (change pattern 7 12) = d1644 pattern
  exact s1031 pattern
theorem s1033 (pattern : Twelve) : d1695 (change pattern 7 12) = d1652 pattern := by
  change (if pattern.f then d1691 (change pattern 7 12) else d942 (change pattern 7 12)) = d1652 pattern
  rw [s1032, s919]
  rfl
theorem s1034 (pattern : Twelve) : d1698 (change pattern 7 12) = d1658 pattern := by
  change (if pattern.e then d1391 (change pattern 7 12) else d1695 (change pattern 7 12)) = d1658 pattern
  rw [s1007, s1033]
  rfl
theorem s1035 (pattern : Twelve) : d1700 (change pattern 7 12) = d1936 pattern := by
  change (if pattern.j then d1698 (change pattern 7 12) else d1697 (change pattern 7 12)) = d1936 pattern
  rw [s1034, s1029]
  rfl
theorem s1036 (pattern : Twelve) : d22 (change pattern 7 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 7 12) else d14 (change pattern 7 12)) = d22 pattern
  rw [s953, s955]
  rfl
theorem s1037 (pattern : Twelve) : d1646 (change pattern 7 12) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 7 12) else d20 (change pattern 7 12)) = d1646 pattern
  rw [s1036, s1030]
  rfl
theorem s1038 (pattern : Twelve) : d1692 (change pattern 7 12) = d1646 pattern := by
  change d1646 (change pattern 7 12) = d1646 pattern
  exact s1037 pattern
theorem s1039 (pattern : Twelve) : d1696 (change pattern 7 12) = d1816 pattern := by
  change (if pattern.f then d1692 (change pattern 7 12) else d945 (change pattern 7 12)) = d1816 pattern
  rw [s1038, s958]
  rfl
theorem s1040 (pattern : Twelve) : d822 (change pattern 7 12) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 7 12) else d21 (change pattern 7 12)) = d822 pattern
  rw [s953, s956]
  rfl
theorem s1041 (pattern : Twelve) : d1252 (change pattern 7 12) = d822 pattern := by
  change d822 (change pattern 7 12) = d822 pattern
  exact s1040 pattern
theorem s1042 (pattern : Twelve) : d1626 (change pattern 7 12) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 7 12) else d1252 (change pattern 7 12)) = d1655 pattern
  rw [s953, s1041]
  rfl
theorem s1043 (pattern : Twelve) : d1699 (change pattern 7 12) = d1819 pattern := by
  change (if pattern.e then d1626 (change pattern 7 12) else d1696 (change pattern 7 12)) = d1819 pattern
  rw [s1042, s1039]
  rfl
theorem s1044 (pattern : Twelve) : d1701 (change pattern 7 12) = d1937 pattern := by
  change (if pattern.j then d1699 (change pattern 7 12) else d1698 (change pattern 7 12)) = d1937 pattern
  rw [s1043, s1034]
  rfl
theorem s1045 (pattern : Twelve) : d1702 (change pattern 7 12) = d1938 pattern := by
  change (if pattern.j then d6 (change pattern 7 12) else d1698 (change pattern 7 12)) = d1938 pattern
  rw [s953, s1034]
  rfl
theorem s1046 (pattern : Twelve) : d1703 (change pattern 7 12) = d1939 pattern := by
  change (if pattern.d then d1702 (change pattern 7 12) else d1701 (change pattern 7 12)) = d1939 pattern
  rw [s1045, s1044]
  rfl
theorem s1047 (pattern : Twelve) : d1704 (change pattern 7 12) = d1940 pattern := by
  change (if pattern.c then d1703 (change pattern 7 12) else d1700 (change pattern 7 12)) = d1940 pattern
  rw [s1046, s1035]
  rfl
theorem s1048 (pattern : Twelve) : d0 (change pattern 7 8) = d0 pattern := by
  rfl
theorem s1049 (pattern : Twelve) : d235 (change pattern 7 8) = d0 pattern := by
  change d0 (change pattern 7 8) = d0 pattern
  exact s1048 pattern
end NetHack.Sokoban21.Diagram
