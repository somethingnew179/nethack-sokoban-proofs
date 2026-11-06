/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions12
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s1950 (pattern : Twelve) : d351 (change pattern 2 3) = d2267 pattern := by
  change (if pattern.a then d349 (change pattern 2 3) else d350 (change pattern 2 3)) = d2267 pattern
  rw [s1948, s1949]
  simp only [ite_self]
theorem s1951 (pattern : Twelve) : d814 (change pattern 2 3) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 2 3) else d7 (change pattern 2 3)) = d814 pattern
  rw [s1901, s1903]
  rfl
theorem s1952 (pattern : Twelve) : d816 (change pattern 2 3) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 2 3) else d814 (change pattern 2 3)) = d816 pattern
  rw [s1901, s1951]
  rfl
theorem s1953 (pattern : Twelve) : d824 (change pattern 2 3) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 2 3) else d27 (change pattern 2 3)) = d824 pattern
  rw [s1952, s1905]
  rfl
theorem s1954 (pattern : Twelve) : d838 (change pattern 2 3) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 2 3) else d0 (change pattern 2 3)) = d838 pattern
  rw [s1953, s1900]
  rfl
theorem s1955 (pattern : Twelve) : d4 (change pattern 2 3) = d4 pattern := by
  rfl
theorem s1956 (pattern : Twelve) : d16 (change pattern 2 3) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 2 3) else d2 (change pattern 2 3)) = d16 pattern
  rw [s1955, s1908]
  rfl
theorem s1957 (pattern : Twelve) : d5 (change pattern 2 3) = d5 pattern := by
  rfl
theorem s1958 (pattern : Twelve) : d12 (change pattern 2 3) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 2 3) else d3 (change pattern 2 3)) = d12 pattern
  rw [s1957, s1909]
  rfl
theorem s1959 (pattern : Twelve) : d25 (change pattern 2 3) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 2 3) else d16 (change pattern 2 3)) = d25 pattern
  rw [s1958, s1956]
  rfl
theorem s1960 (pattern : Twelve) : d817 (change pattern 2 3) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 2 3) else d19 (change pattern 2 3)) = d817 pattern
  rw [s1959, s1915]
  rfl
theorem s1961 (pattern : Twelve) : d42 (change pattern 2 3) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d25 (change pattern 2 3)) = d42 pattern
  rw [s1916, s1959]
  rfl
theorem s1962 (pattern : Twelve) : d825 (change pattern 2 3) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 2 3) else d817 (change pattern 2 3)) = d825 pattern
  rw [s1961, s1960]
  rfl
theorem s1963 (pattern : Twelve) : d839 (change pattern 2 3) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 2 3) else d17 (change pattern 2 3)) = d839 pattern
  rw [s1962, s1904]
  rfl
theorem s1964 (pattern : Twelve) : d853 (change pattern 2 3) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 2 3) else d838 (change pattern 2 3)) = d853 pattern
  rw [s1963, s1954]
  rfl
theorem s1965 (pattern : Twelve) : d818 (change pattern 2 3) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d814 (change pattern 2 3)) = d818 pattern
  rw [s1916, s1951]
  rfl
theorem s1966 (pattern : Twelve) : d826 (change pattern 2 3) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 2 3) else d34 (change pattern 2 3)) = d826 pattern
  rw [s1965, s1912]
  rfl
theorem s1967 (pattern : Twelve) : d840 (change pattern 2 3) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 2 3) else d56 (change pattern 2 3)) = d840 pattern
  rw [s1966, s1923]
  rfl
theorem s1968 (pattern : Twelve) : d827 (change pattern 2 3) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 2 3) else d34 (change pattern 2 3)) = d827 pattern
  rw [s1924, s1912]
  rfl
theorem s1969 (pattern : Twelve) : d841 (change pattern 2 3) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 2 3) else d827 (change pattern 2 3)) = d841 pattern
  rw [s1962, s1968]
  rfl
theorem s1970 (pattern : Twelve) : d854 (change pattern 2 3) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 2 3) else d840 (change pattern 2 3)) = d854 pattern
  rw [s1969, s1967]
  rfl
theorem s1971 (pattern : Twelve) : d861 (change pattern 2 3) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 2 3) else d853 (change pattern 2 3)) = d861 pattern
  rw [s1970, s1964]
  rfl
theorem s1972 (pattern : Twelve) : d1011 (change pattern 2 3) = d861 pattern := by
  change d861 (change pattern 2 3) = d861 pattern
  exact s1971 pattern
theorem s1973 (pattern : Twelve) : d823 (change pattern 2 3) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 2 3) else d17 (change pattern 2 3)) = d823 pattern
  rw [s1908, s1904]
  rfl
theorem s1974 (pattern : Twelve) : d846 (change pattern 2 3) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 2 3) else d823 (change pattern 2 3)) = d846 pattern
  rw [s1962, s1973]
  rfl
theorem s1975 (pattern : Twelve) : d857 (change pattern 2 3) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 2 3) else d838 (change pattern 2 3)) = d857 pattern
  rw [s1974, s1954]
  rfl
theorem s1976 (pattern : Twelve) : d832 (change pattern 2 3) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 2 3) else d34 (change pattern 2 3)) = d832 pattern
  rw [s1934, s1912]
  rfl
theorem s1977 (pattern : Twelve) : d847 (change pattern 2 3) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 2 3) else d56 (change pattern 2 3)) = d847 pattern
  rw [s1976, s1923]
  rfl
theorem s1978 (pattern : Twelve) : d833 (change pattern 2 3) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 2 3) else d34 (change pattern 2 3)) = d833 pattern
  rw [s1937, s1912]
  rfl
theorem s1979 (pattern : Twelve) : d848 (change pattern 2 3) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 2 3) else d833 (change pattern 2 3)) = d848 pattern
  rw [s1962, s1978]
  rfl
theorem s1980 (pattern : Twelve) : d858 (change pattern 2 3) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 2 3) else d847 (change pattern 2 3)) = d858 pattern
  rw [s1979, s1977]
  rfl
theorem s1981 (pattern : Twelve) : d864 (change pattern 2 3) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 2 3) else d857 (change pattern 2 3)) = d864 pattern
  rw [s1980, s1975]
  rfl
theorem s1982 (pattern : Twelve) : d1012 (change pattern 2 3) = d864 pattern := by
  change d864 (change pattern 2 3) = d864 pattern
  exact s1981 pattern
theorem s1983 (pattern : Twelve) : d1014 (change pattern 2 3) = d2268 pattern := by
  change (if pattern.g then d1012 (change pattern 2 3) else d1011 (change pattern 2 3)) = d2268 pattern
  rw [s1982, s1972]
  rfl
theorem s1984 (pattern : Twelve) : d1013 (change pattern 2 3) = d861 pattern := by
  change d861 (change pattern 2 3) = d861 pattern
  exact s1971 pattern
theorem s1985 (pattern : Twelve) : d1015 (change pattern 2 3) = d2268 pattern := by
  change (if pattern.g then d1012 (change pattern 2 3) else d1013 (change pattern 2 3)) = d2268 pattern
  rw [s1982, s1984]
  rfl
theorem s1986 (pattern : Twelve) : d1016 (change pattern 2 3) = d2268 pattern := by
  change (if pattern.b then d1015 (change pattern 2 3) else d1014 (change pattern 2 3)) = d2268 pattern
  rw [s1985, s1983]
  simp only [ite_self]
theorem s1987 (pattern : Twelve) : d1017 (change pattern 2 3) = d2268 pattern := by
  change (if pattern.a then d1015 (change pattern 2 3) else d1016 (change pattern 2 3)) = d2268 pattern
  rw [s1985, s1986]
  simp only [ite_self]
theorem s1988 (pattern : Twelve) : d8 (change pattern 2 3) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 2 3) else d1 (change pattern 2 3)) = d8 pattern
  rw [s1908, s1901]
  rfl
theorem s1989 (pattern : Twelve) : d1275 (change pattern 2 3) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 2 3) else d7 (change pattern 2 3)) = d1275 pattern
  rw [s1988, s1903]
  rfl
theorem s1990 (pattern : Twelve) : d872 (change pattern 2 3) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 2 3) else d1 (change pattern 2 3)) = d872 pattern
  rw [s1988, s1901]
  rfl
theorem s1991 (pattern : Twelve) : d1278 (change pattern 2 3) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 2 3) else d1275 (change pattern 2 3)) = d1278 pattern
  rw [s1990, s1989]
  rfl
theorem s1992 (pattern : Twelve) : d1284 (change pattern 2 3) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 2 3) else d1278 (change pattern 2 3)) = d1284 pattern
  rw [s1990, s1991]
  rfl
theorem s1993 (pattern : Twelve) : d1293 (change pattern 2 3) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 2 3) else d17 (change pattern 2 3)) = d1293 pattern
  rw [s1992, s1904]
  rfl
theorem s1994 (pattern : Twelve) : d1294 (change pattern 2 3) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 2 3) else d19 (change pattern 2 3)) = d1294 pattern
  rw [s1916, s1915]
  rfl
theorem s1995 (pattern : Twelve) : d1305 (change pattern 2 3) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 2 3) else d1293 (change pattern 2 3)) = d1305 pattern
  rw [s1994, s1993]
  rfl
theorem s1996 (pattern : Twelve) : d117 (change pattern 2 3) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 2 3) else d3 (change pattern 2 3)) = d117 pattern
  rw [s1955, s1909]
  rfl
theorem s1997 (pattern : Twelve) : d1276 (change pattern 2 3) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 2 3) else d9 (change pattern 2 3)) = d1276 pattern
  rw [s1996, s1910]
  rfl
theorem s1998 (pattern : Twelve) : d1279 (change pattern 2 3) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 2 3) else d1275 (change pattern 2 3)) = d1279 pattern
  rw [s1997, s1989]
  rfl
theorem s1999 (pattern : Twelve) : d1280 (change pattern 2 3) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d872 (change pattern 2 3)) = d1280 pattern
  rw [s1916, s1990]
  rfl
theorem s2000 (pattern : Twelve) : d1285 (change pattern 2 3) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 2 3) else d1279 (change pattern 2 3)) = d1285 pattern
  rw [s1999, s1998]
  rfl
theorem s2001 (pattern : Twelve) : d1295 (change pattern 2 3) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 2 3) else d827 (change pattern 2 3)) = d1295 pattern
  rw [s2000, s1968]
  rfl
theorem s2002 (pattern : Twelve) : d1286 (change pattern 2 3) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 2 3) else d817 (change pattern 2 3)) = d1286 pattern
  rw [s1917, s1960]
  rfl
theorem s2003 (pattern : Twelve) : d1296 (change pattern 2 3) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 2 3) else d1286 (change pattern 2 3)) = d1296 pattern
  rw [s1916, s2002]
  rfl
theorem s2004 (pattern : Twelve) : d1306 (change pattern 2 3) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 2 3) else d1295 (change pattern 2 3)) = d1306 pattern
  rw [s2003, s2001]
  rfl
theorem s2005 (pattern : Twelve) : d1313 (change pattern 2 3) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 2 3) else d1305 (change pattern 2 3)) = d1313 pattern
  rw [s2004, s1995]
  rfl
theorem s2006 (pattern : Twelve) : d1428 (change pattern 2 3) = d1313 pattern := by
  change d1313 (change pattern 2 3) = d1313 pattern
  exact s2005 pattern
theorem s2007 (pattern : Twelve) : d1283 (change pattern 2 3) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 2 3) else d19 (change pattern 2 3)) = d1283 pattern
  rw [s1911, s1915]
  rfl
theorem s2008 (pattern : Twelve) : d1301 (change pattern 2 3) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 2 3) else d1283 (change pattern 2 3)) = d1301 pattern
  rw [s1916, s2007]
  rfl
theorem s2009 (pattern : Twelve) : d1309 (change pattern 2 3) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 2 3) else d1293 (change pattern 2 3)) = d1309 pattern
  rw [s2008, s1993]
  rfl
theorem s2010 (pattern : Twelve) : d1290 (change pattern 2 3) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 2 3) else d817 (change pattern 2 3)) = d1290 pattern
  rw [s1939, s1960]
  rfl
theorem s2011 (pattern : Twelve) : d1302 (change pattern 2 3) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 2 3) else d1290 (change pattern 2 3)) = d1302 pattern
  rw [s1916, s2010]
  rfl
theorem s2012 (pattern : Twelve) : d1310 (change pattern 2 3) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 2 3) else d1295 (change pattern 2 3)) = d1310 pattern
  rw [s2011, s2001]
  rfl
theorem s2013 (pattern : Twelve) : d1316 (change pattern 2 3) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 2 3) else d1309 (change pattern 2 3)) = d1316 pattern
  rw [s2012, s2009]
  rfl
theorem s2014 (pattern : Twelve) : d1429 (change pattern 2 3) = d1316 pattern := by
  change d1316 (change pattern 2 3) = d1316 pattern
  exact s2013 pattern
theorem s2015 (pattern : Twelve) : d1431 (change pattern 2 3) = d2269 pattern := by
  change (if pattern.g then d1429 (change pattern 2 3) else d1428 (change pattern 2 3)) = d2269 pattern
  rw [s2014, s2006]
  rfl
theorem s2016 (pattern : Twelve) : d1430 (change pattern 2 3) = d1313 pattern := by
  change d1313 (change pattern 2 3) = d1313 pattern
  exact s2005 pattern
theorem s2017 (pattern : Twelve) : d1432 (change pattern 2 3) = d2269 pattern := by
  change (if pattern.g then d1429 (change pattern 2 3) else d1430 (change pattern 2 3)) = d2269 pattern
  rw [s2014, s2016]
  rfl
theorem s2018 (pattern : Twelve) : d1433 (change pattern 2 3) = d2269 pattern := by
  change (if pattern.b then d1432 (change pattern 2 3) else d1431 (change pattern 2 3)) = d2269 pattern
  rw [s2017, s2015]
  simp only [ite_self]
theorem s2019 (pattern : Twelve) : d1434 (change pattern 2 3) = d2269 pattern := by
  change (if pattern.a then d1432 (change pattern 2 3) else d1433 (change pattern 2 3)) = d2269 pattern
  rw [s2017, s2018]
  simp only [ite_self]
theorem s2020 (pattern : Twelve) : d1324 (change pattern 2 3) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 2 3) else d11 (change pattern 2 3)) = d1324 pattern
  rw [s1956, s1914]
  rfl
theorem s2021 (pattern : Twelve) : d1649 (change pattern 2 3) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 2 3) else d19 (change pattern 2 3)) = d1649 pattern
  rw [s2020, s1915]
  rfl
theorem s2022 (pattern : Twelve) : d1650 (change pattern 2 3) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 2 3) else d25 (change pattern 2 3)) = d1650 pattern
  rw [s1916, s1959]
  rfl
theorem s2023 (pattern : Twelve) : d1656 (change pattern 2 3) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 2 3) else d1649 (change pattern 2 3)) = d1656 pattern
  rw [s2022, s2021]
  rfl
theorem s2024 (pattern : Twelve) : d13 (change pattern 2 3) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 2 3) else d4 (change pattern 2 3)) = d13 pattern
  rw [s1916, s1955]
  rfl
theorem s2025 (pattern : Twelve) : d20 (change pattern 2 3) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 2 3) else d12 (change pattern 2 3)) = d20 pattern
  rw [s2024, s1958]
  rfl
theorem s2026 (pattern : Twelve) : d1644 (change pattern 2 3) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 2 3) else d1324 (change pattern 2 3)) = d1644 pattern
  rw [s2025, s2020]
  rfl
theorem s2027 (pattern : Twelve) : d1645 (change pattern 2 3) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d1324 (change pattern 2 3)) = d1645 pattern
  rw [s1916, s2020]
  rfl
theorem s2028 (pattern : Twelve) : d1647 (change pattern 2 3) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 2 3) else d1644 (change pattern 2 3)) = d1647 pattern
  rw [s2027, s2026]
  rfl
theorem s2029 (pattern : Twelve) : d1651 (change pattern 2 3) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 2 3) else d1286 (change pattern 2 3)) = d1651 pattern
  rw [s2028, s2002]
  rfl
theorem s2030 (pattern : Twelve) : d14 (change pattern 2 3) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 2 3) else d5 (change pattern 2 3)) = d14 pattern
  rw [s1916, s1957]
  rfl
theorem s2031 (pattern : Twelve) : d21 (change pattern 2 3) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 2 3) else d13 (change pattern 2 3)) = d21 pattern
  rw [s2030, s2024]
  rfl
theorem s2032 (pattern : Twelve) : d821 (change pattern 2 3) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 2 3) else d25 (change pattern 2 3)) = d821 pattern
  rw [s2031, s1959]
  rfl
theorem s2033 (pattern : Twelve) : d1289 (change pattern 2 3) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 2 3) else d821 (change pattern 2 3)) = d1289 pattern
  rw [s1961, s2032]
  rfl
theorem s2034 (pattern : Twelve) : d1300 (change pattern 2 3) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 2 3) else d1289 (change pattern 2 3)) = d1300 pattern
  rw [s1916, s2033]
  rfl
theorem s2035 (pattern : Twelve) : d1657 (change pattern 2 3) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 2 3) else d1651 (change pattern 2 3)) = d1657 pattern
  rw [s2034, s2029]
  rfl
theorem s2036 (pattern : Twelve) : d1660 (change pattern 2 3) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 2 3) else d1656 (change pattern 2 3)) = d1660 pattern
  rw [s2035, s2023]
  rfl
theorem s2037 (pattern : Twelve) : d1714 (change pattern 2 3) = d1660 pattern := by
  change d1660 (change pattern 2 3) = d1660 pattern
  exact s2036 pattern
theorem s2038 (pattern : Twelve) : d0 (change pattern 2 9) = d0 pattern := by
  rfl
theorem s2039 (pattern : Twelve) : d2 (change pattern 2 9) = d2 pattern := by
  rfl
theorem s2040 (pattern : Twelve) : d30 (change pattern 2 9) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 2 9) else d0 (change pattern 2 9)) = d30 pattern
  rw [s2039, s2038]
  rfl
theorem s2041 (pattern : Twelve) : d3 (change pattern 2 9) = d3 pattern := by
  rfl
theorem s2042 (pattern : Twelve) : d5 (change pattern 2 9) = d5 pattern := by
  rfl
theorem s2043 (pattern : Twelve) : d12 (change pattern 2 9) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 2 9) else d3 (change pattern 2 9)) = d12 pattern
  rw [s2042, s2041]
  rfl
theorem s2044 (pattern : Twelve) : d4 (change pattern 2 9) = d4 pattern := by
  rfl
theorem s2045 (pattern : Twelve) : d6 (change pattern 2 9) = d6 pattern := by
  rfl
theorem s2046 (pattern : Twelve) : d13 (change pattern 2 9) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 2 9) else d4 (change pattern 2 9)) = d13 pattern
  rw [s2045, s2044]
  rfl
theorem s2047 (pattern : Twelve) : d20 (change pattern 2 9) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 2 9) else d12 (change pattern 2 9)) = d20 pattern
  rw [s2046, s2043]
  rfl
theorem s2048 (pattern : Twelve) : d31 (change pattern 2 9) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 2 9) else d0 (change pattern 2 9)) = d31 pattern
  rw [s2047, s2038]
  rfl
theorem s2049 (pattern : Twelve) : d52 (change pattern 2 9) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 2 9) else d30 (change pattern 2 9)) = d52 pattern
  rw [s2048, s2040]
  rfl
theorem s2050 (pattern : Twelve) : d1 (change pattern 2 9) = d1 pattern := by
  rfl
theorem s2051 (pattern : Twelve) : d7 (change pattern 2 9) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 2 9) else d0 (change pattern 2 9)) = d7 pattern
  rw [s2050, s2038]
  rfl
theorem s2052 (pattern : Twelve) : d17 (change pattern 2 9) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 2 9) else d0 (change pattern 2 9)) = d17 pattern
  rw [s2051, s2038]
  rfl
theorem s2053 (pattern : Twelve) : d14 (change pattern 2 9) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 2 9) else d5 (change pattern 2 9)) = d14 pattern
  rw [s2045, s2042]
  rfl
theorem s2054 (pattern : Twelve) : d21 (change pattern 2 9) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 2 9) else d13 (change pattern 2 9)) = d21 pattern
  rw [s2053, s2046]
  rfl
theorem s2055 (pattern : Twelve) : d32 (change pattern 2 9) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 2 9) else d17 (change pattern 2 9)) = d32 pattern
  rw [s2054, s2052]
  rfl
theorem s2056 (pattern : Twelve) : d53 (change pattern 2 9) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 2 9) else d30 (change pattern 2 9)) = d53 pattern
  rw [s2055, s2040]
  rfl
theorem s2057 (pattern : Twelve) : d74 (change pattern 2 9) = d74 pattern := by
  change (if pattern.f then d53 (change pattern 2 9) else d52 (change pattern 2 9)) = d74 pattern
  rw [s2056, s2049]
  rfl
theorem s2058 (pattern : Twelve) : d22 (change pattern 2 9) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 2 9) else d14 (change pattern 2 9)) = d22 pattern
  rw [s2045, s2053]
  rfl
theorem s2059 (pattern : Twelve) : d33 (change pattern 2 9) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 2 9) else d0 (change pattern 2 9)) = d33 pattern
  rw [s2058, s2038]
  rfl
theorem s2060 (pattern : Twelve) : d54 (change pattern 2 9) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 2 9) else d30 (change pattern 2 9)) = d54 pattern
  rw [s2059, s2040]
  rfl
theorem s2061 (pattern : Twelve) : d9 (change pattern 2 9) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 2 9) else d2 (change pattern 2 9)) = d9 pattern
  rw [s2041, s2039]
  rfl
theorem s2062 (pattern : Twelve) : d23 (change pattern 2 9) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 2 9) else d2 (change pattern 2 9)) = d23 pattern
  rw [s2061, s2039]
  rfl
theorem s2063 (pattern : Twelve) : d34 (change pattern 2 9) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 2 9) else d17 (change pattern 2 9)) = d34 pattern
  rw [s2062, s2052]
  rfl
theorem s2064 (pattern : Twelve) : d10 (change pattern 2 9) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 2 9) else d0 (change pattern 2 9)) = d10 pattern
  rw [s2039, s2038]
  rfl
theorem s2065 (pattern : Twelve) : d11 (change pattern 2 9) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 2 9) else d1 (change pattern 2 9)) = d11 pattern
  rw [s2041, s2050]
  rfl
theorem s2066 (pattern : Twelve) : d19 (change pattern 2 9) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 2 9) else d10 (change pattern 2 9)) = d19 pattern
  rw [s2065, s2064]
  rfl
theorem s2067 (pattern : Twelve) : d29 (change pattern 2 9) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d19 (change pattern 2 9)) = d29 pattern
  rw [s2045, s2066]
  rfl
theorem s2068 (pattern : Twelve) : d55 (change pattern 2 9) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 2 9) else d34 (change pattern 2 9)) = d55 pattern
  rw [s2067, s2063]
  rfl
theorem s2069 (pattern : Twelve) : d75 (change pattern 2 9) = d75 pattern := by
  change (if pattern.f then d55 (change pattern 2 9) else d54 (change pattern 2 9)) = d75 pattern
  rw [s2068, s2060]
  rfl
theorem s2070 (pattern : Twelve) : d92 (change pattern 2 9) = d92 pattern := by
  change (if pattern.e then d75 (change pattern 2 9) else d74 (change pattern 2 9)) = d92 pattern
  rw [s2069, s2057]
  rfl
theorem s2071 (pattern : Twelve) : d102 (change pattern 2 9) = d92 pattern := by
  change d92 (change pattern 2 9) = d92 pattern
  exact s2070 pattern
theorem s2072 (pattern : Twelve) : d35 (change pattern 2 9) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d0 (change pattern 2 9)) = d35 pattern
  rw [s2045, s2038]
  rfl
theorem s2073 (pattern : Twelve) : d56 (change pattern 2 9) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 2 9) else d30 (change pattern 2 9)) = d56 pattern
  rw [s2072, s2040]
  rfl
theorem s2074 (pattern : Twelve) : d36 (change pattern 2 9) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d17 (change pattern 2 9)) = d36 pattern
  rw [s2045, s2052]
  rfl
theorem s2075 (pattern : Twelve) : d57 (change pattern 2 9) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 2 9) else d30 (change pattern 2 9)) = d57 pattern
  rw [s2074, s2040]
  rfl
theorem s2076 (pattern : Twelve) : d77 (change pattern 2 9) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 2 9) else d56 (change pattern 2 9)) = d77 pattern
  rw [s2075, s2073]
  rfl
theorem s2077 (pattern : Twelve) : d78 (change pattern 2 9) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 2 9) else d56 (change pattern 2 9)) = d78 pattern
  rw [s2068, s2073]
  rfl
theorem s2078 (pattern : Twelve) : d94 (change pattern 2 9) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 2 9) else d77 (change pattern 2 9)) = d94 pattern
  rw [s2077, s2076]
  rfl
theorem s2079 (pattern : Twelve) : d103 (change pattern 2 9) = d94 pattern := by
  change d94 (change pattern 2 9) = d94 pattern
  exact s2078 pattern
theorem s2080 (pattern : Twelve) : d110 (change pattern 2 9) = d2271 pattern := by
  change (if pattern.d then d103 (change pattern 2 9) else d102 (change pattern 2 9)) = d2271 pattern
  rw [s2079, s2071]
  rfl
theorem s2081 (pattern : Twelve) : d345 (change pattern 2 9) = d2271 pattern := by
  change d110 (change pattern 2 9) = d2271 pattern
  exact s2080 pattern
theorem s2082 (pattern : Twelve) : d43 (change pattern 2 9) = d43 pattern := by
  change (if pattern.i then d21 (change pattern 2 9) else d1 (change pattern 2 9)) = d43 pattern
  rw [s2054, s2050]
  rfl
theorem s2083 (pattern : Twelve) : d62 (change pattern 2 9) = d62 pattern := by
  change (if pattern.h then d43 (change pattern 2 9) else d30 (change pattern 2 9)) = d62 pattern
  rw [s2082, s2040]
  rfl
theorem s2084 (pattern : Twelve) : d83 (change pattern 2 9) = d83 pattern := by
  change (if pattern.f then d62 (change pattern 2 9) else d52 (change pattern 2 9)) = d83 pattern
  rw [s2083, s2049]
  rfl
theorem s2085 (pattern : Twelve) : d44 (change pattern 2 9) = d44 pattern := by
  change (if pattern.i then d22 (change pattern 2 9) else d2 (change pattern 2 9)) = d44 pattern
  rw [s2058, s2039]
  rfl
theorem s2086 (pattern : Twelve) : d63 (change pattern 2 9) = d63 pattern := by
  change (if pattern.h then d44 (change pattern 2 9) else d30 (change pattern 2 9)) = d63 pattern
  rw [s2085, s2040]
  rfl
theorem s2087 (pattern : Twelve) : d40 (change pattern 2 9) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d23 (change pattern 2 9)) = d40 pattern
  rw [s2045, s2062]
  rfl
theorem s2088 (pattern : Twelve) : d64 (change pattern 2 9) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 2 9) else d34 (change pattern 2 9)) = d64 pattern
  rw [s2087, s2063]
  rfl
theorem s2089 (pattern : Twelve) : d84 (change pattern 2 9) = d84 pattern := by
  change (if pattern.f then d64 (change pattern 2 9) else d63 (change pattern 2 9)) = d84 pattern
  rw [s2088, s2086]
  rfl
theorem s2090 (pattern : Twelve) : d98 (change pattern 2 9) = d98 pattern := by
  change (if pattern.e then d84 (change pattern 2 9) else d83 (change pattern 2 9)) = d98 pattern
  rw [s2089, s2084]
  rfl
theorem s2091 (pattern : Twelve) : d106 (change pattern 2 9) = d98 pattern := by
  change d98 (change pattern 2 9) = d98 pattern
  exact s2090 pattern
theorem s2092 (pattern : Twelve) : d45 (change pattern 2 9) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d1 (change pattern 2 9)) = d45 pattern
  rw [s2045, s2050]
  rfl
theorem s2093 (pattern : Twelve) : d65 (change pattern 2 9) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 2 9) else d30 (change pattern 2 9)) = d65 pattern
  rw [s2092, s2040]
  rfl
theorem s2094 (pattern : Twelve) : d85 (change pattern 2 9) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 2 9) else d56 (change pattern 2 9)) = d85 pattern
  rw [s2093, s2073]
  rfl
theorem s2095 (pattern : Twelve) : d39 (change pattern 2 9) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d2 (change pattern 2 9)) = d39 pattern
  rw [s2045, s2039]
  rfl
theorem s2096 (pattern : Twelve) : d66 (change pattern 2 9) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 2 9) else d30 (change pattern 2 9)) = d66 pattern
  rw [s2095, s2040]
  rfl
theorem s2097 (pattern : Twelve) : d86 (change pattern 2 9) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 2 9) else d66 (change pattern 2 9)) = d86 pattern
  rw [s2088, s2096]
  rfl
theorem s2098 (pattern : Twelve) : d99 (change pattern 2 9) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 2 9) else d85 (change pattern 2 9)) = d99 pattern
  rw [s2097, s2094]
  rfl
theorem s2099 (pattern : Twelve) : d107 (change pattern 2 9) = d99 pattern := by
  change d99 (change pattern 2 9) = d99 pattern
  exact s2098 pattern
end NetHack.Sokoban21.Diagram
