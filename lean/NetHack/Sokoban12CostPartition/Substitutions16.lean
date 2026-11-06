/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1920 (p : Pattern) : d5 (change p 159 (some 133)) = d5 p := by
  rfl
theorem sub1921 (p : Pattern) : d58 (change p 159 (some 133)) = d58 p := by
  change (if p 271 then d5 (change p 159 (some 133)) else d4 (change p 159 (some 133))) = d58 p
  rw [sub1920, sub1906]
  rfl
theorem sub1922 (p : Pattern) : d59 (change p 159 (some 133)) = d59 p := by
  change (if p 193 then d58 (change p 159 (some 133)) else d9 (change p 159 (some 133))) = d59 p
  rw [sub1921, sub1916]
  rfl
theorem sub1923 (p : Pattern) : d60 (change p 159 (some 133)) = d60 p := by
  change (if p 192 then d59 (change p 159 (some 133)) else d9 (change p 159 (some 133))) = d60 p
  rw [sub1922, sub1916]
  rfl
theorem sub1924 (p : Pattern) : d61 (change p 159 (some 133)) = d61 p := by
  change (if p 186 then d60 (change p 159 (some 133)) else d11 (change p 159 (some 133))) = d61 p
  rw [sub1923, sub1918]
  rfl
theorem sub1925 (p : Pattern) : d62 (change p 159 (some 133)) = d62 p := by
  change (if p 168 then d61 (change p 159 (some 133)) else d56 (change p 159 (some 133))) = d62 p
  rw [sub1924, sub1909]
  rfl
theorem sub1926 (p : Pattern) : d63 (change p 159 (some 133)) = d63 p := by
  change (if p 160 then d62 (change p 159 (some 133)) else d12 (change p 159 (some 133))) = d63 p
  rw [sub1925, sub1919]
  rfl
theorem sub1927 (p : Pattern) : d116 (change p 159 (some 133)) = d63 p := by
  change d63 (change p 159 (some 133)) = d63 p
  exact sub1926 p
theorem sub1928 (p : Pattern) : d65 (change p 159 (some 133)) = d65 p := by
  change (if p 168 then d60 (change p 159 (some 133)) else d55 (change p 159 (some 133))) = d65 p
  rw [sub1923, sub1908]
  rfl
theorem sub1929 (p : Pattern) : d339 (change p 159 (some 133)) = d69 p := by
  change (if p 158 then d65 (change p 159 (some 133)) else d116 (change p 159 (some 133))) = d69 p
  rw [sub1928, sub1927]
  rfl
theorem sub1930 (p : Pattern) : d340 (change p 159 (some 133)) = d70 p := by
  change (if p 141 then d339 (change p 159 (some 133)) else d338 (change p 159 (some 133))) = d70 p
  rw [sub1929, sub1912]
  rfl
theorem sub1931 (p : Pattern) : d106 (change p 159 (some 133)) = d106 p := by
  change (if p 160 then d55 (change p 159 (some 133)) else d7 (change p 159 (some 133))) = d106 p
  rw [sub1908, sub1905]
  rfl
theorem sub1932 (p : Pattern) : d107 (change p 159 (some 133)) = d106 p := by
  change d106 (change p 159 (some 133)) = d106 p
  exact sub1931 p
theorem sub1933 (p : Pattern) : d211 (change p 159 (some 133)) = d229 p := by
  change (if p 158 then d55 (change p 159 (some 133)) else d107 (change p 159 (some 133))) = d229 p
  rw [sub1908, sub1932]
  rfl
theorem sub1934 (p : Pattern) : d109 (change p 159 (some 133)) = d109 p := by
  change (if p 160 then d65 (change p 159 (some 133)) else d12 (change p 159 (some 133))) = d109 p
  rw [sub1928, sub1919]
  rfl
theorem sub1935 (p : Pattern) : d110 (change p 159 (some 133)) = d109 p := by
  change d109 (change p 159 (some 133)) = d109 p
  exact sub1934 p
theorem sub1936 (p : Pattern) : d212 (change p 159 (some 133)) = d230 p := by
  change (if p 158 then d65 (change p 159 (some 133)) else d110 (change p 159 (some 133))) = d230 p
  rw [sub1928, sub1935]
  rfl
theorem sub1937 (p : Pattern) : d213 (change p 159 (some 133)) = d231 p := by
  change (if p 141 then d212 (change p 159 (some 133)) else d211 (change p 159 (some 133))) = d231 p
  rw [sub1936, sub1933]
  rfl
theorem sub1938 (p : Pattern) : d341 (change p 159 (some 133)) = d232 p := by
  change (if p 134 then d213 (change p 159 (some 133)) else d340 (change p 159 (some 133))) = d232 p
  rw [sub1937, sub1930]
  rfl
theorem sub1939 (p : Pattern) : d342 (change p 159 (some 133)) = d232 p := by
  change d341 (change p 159 (some 133)) = d232 p
  exact sub1938 p
theorem sub1940 (p : Pattern) : d66 (change p 159 (some 133)) = d66 p := by
  change (if p 141 then d65 (change p 159 (some 133)) else d55 (change p 159 (some 133))) = d66 p
  rw [sub1928, sub1908]
  rfl
theorem sub1941 (p : Pattern) : d343 (change p 159 (some 133)) = d66 p := by
  change d66 (change p 159 (some 133)) = d66 p
  exact sub1940 p
theorem sub1942 (p : Pattern) : d344 (change p 159 (some 133)) = d1155 p := by
  change (if p 132 then d343 (change p 159 (some 133)) else d342 (change p 159 (some 133))) = d1155 p
  rw [sub1941, sub1939]
  rfl
theorem sub1943 (p : Pattern) : d119 (change p 159 (some 133)) = d119 p := by
  change (if p 187 then d55 (change p 159 (some 133)) else d7 (change p 159 (some 133))) = d119 p
  rw [sub1908, sub1905]
  rfl
theorem sub1944 (p : Pattern) : d137 (change p 159 (some 133)) = d137 p := by
  change (if p 186 then d55 (change p 159 (some 133)) else d119 (change p 159 (some 133))) = d137 p
  rw [sub1908, sub1943]
  rfl
theorem sub1945 (p : Pattern) : d138 (change p 159 (some 133)) = d138 p := by
  change (if p 160 then d137 (change p 159 (some 133)) else d7 (change p 159 (some 133))) = d138 p
  rw [sub1944, sub1905]
  rfl
theorem sub1946 (p : Pattern) : d346 (change p 159 (some 133)) = d138 p := by
  change d138 (change p 159 (some 133)) = d138 p
  exact sub1945 p
theorem sub1947 (p : Pattern) : d347 (change p 159 (some 133)) = d803 p := by
  change (if p 158 then d55 (change p 159 (some 133)) else d346 (change p 159 (some 133))) = d803 p
  rw [sub1908, sub1946]
  rfl
theorem sub1948 (p : Pattern) : d125 (change p 159 (some 133)) = d125 p := by
  change (if p 187 then d60 (change p 159 (some 133)) else d11 (change p 159 (some 133))) = d125 p
  rw [sub1923, sub1918]
  rfl
theorem sub1949 (p : Pattern) : d143 (change p 159 (some 133)) = d143 p := by
  change (if p 186 then d60 (change p 159 (some 133)) else d125 (change p 159 (some 133))) = d143 p
  rw [sub1923, sub1948]
  rfl
theorem sub1950 (p : Pattern) : d144 (change p 159 (some 133)) = d144 p := by
  change (if p 168 then d143 (change p 159 (some 133)) else d137 (change p 159 (some 133))) = d144 p
  rw [sub1949, sub1944]
  rfl
theorem sub1951 (p : Pattern) : d145 (change p 159 (some 133)) = d145 p := by
  change (if p 160 then d144 (change p 159 (some 133)) else d12 (change p 159 (some 133))) = d145 p
  rw [sub1950, sub1919]
  rfl
theorem sub1952 (p : Pattern) : d348 (change p 159 (some 133)) = d145 p := by
  change d145 (change p 159 (some 133)) = d145 p
  exact sub1951 p
theorem sub1953 (p : Pattern) : d349 (change p 159 (some 133)) = d804 p := by
  change (if p 158 then d65 (change p 159 (some 133)) else d348 (change p 159 (some 133))) = d804 p
  rw [sub1928, sub1952]
  rfl
theorem sub1954 (p : Pattern) : d350 (change p 159 (some 133)) = d805 p := by
  change (if p 141 then d349 (change p 159 (some 133)) else d347 (change p 159 (some 133))) = d805 p
  rw [sub1953, sub1947]
  rfl
theorem sub1955 (p : Pattern) : d351 (change p 159 (some 133)) = d806 p := by
  change (if p 134 then d66 (change p 159 (some 133)) else d350 (change p 159 (some 133))) = d806 p
  rw [sub1940, sub1954]
  rfl
theorem sub1956 (p : Pattern) : d352 (change p 159 (some 133)) = d806 p := by
  change d351 (change p 159 (some 133)) = d806 p
  exact sub1955 p
theorem sub1957 (p : Pattern) : d354 (change p 159 (some 133)) = d66 p := by
  change d66 (change p 159 (some 133)) = d66 p
  exact sub1940 p
theorem sub1958 (p : Pattern) : d355 (change p 159 (some 133)) = d1156 p := by
  change (if p 132 then d354 (change p 159 (some 133)) else d352 (change p 159 (some 133))) = d1156 p
  rw [sub1957, sub1956]
  rfl
theorem sub1959 (p : Pattern) : d356 (change p 159 (some 133)) = d1157 p := by
  change (if p 108 then d355 (change p 159 (some 133)) else d344 (change p 159 (some 133))) = d1157 p
  rw [sub1958, sub1942]
  rfl
theorem sub1960 (p : Pattern) : d0 (change p 186 (some 187)) = d0 p := by
  rfl
theorem sub1961 (p : Pattern) : d2 (change p 186 (some 187)) = d2 p := by
  rfl
theorem sub1962 (p : Pattern) : d6 (change p 186 (some 187)) = d6 p := by
  change (if p 193 then d2 (change p 186 (some 187)) else d0 (change p 186 (some 187))) = d6 p
  rw [sub1961, sub1960]
  rfl
theorem sub1963 (p : Pattern) : d7 (change p 186 (some 187)) = d7 p := by
  change (if p 192 then d6 (change p 186 (some 187)) else d0 (change p 186 (some 187))) = d7 p
  rw [sub1962, sub1960]
  rfl
theorem sub1964 (p : Pattern) : d56 (change p 186 (some 187)) = d7 p := by
  change d7 (change p 186 (some 187)) = d7 p
  exact sub1963 p
theorem sub1965 (p : Pattern) : d1 (change p 186 (some 187)) = d1 p := by
  rfl
theorem sub1966 (p : Pattern) : d8 (change p 186 (some 187)) = d8 p := by
  change (if p 271 then d1 (change p 186 (some 187)) else d0 (change p 186 (some 187))) = d8 p
  rw [sub1965, sub1960]
  rfl
theorem sub1967 (p : Pattern) : d3 (change p 186 (some 187)) = d3 p := by
  rfl
theorem sub1968 (p : Pattern) : d9 (change p 186 (some 187)) = d9 p := by
  change (if p 271 then d3 (change p 186 (some 187)) else d2 (change p 186 (some 187))) = d9 p
  rw [sub1967, sub1961]
  rfl
theorem sub1969 (p : Pattern) : d10 (change p 186 (some 187)) = d10 p := by
  change (if p 193 then d9 (change p 186 (some 187)) else d8 (change p 186 (some 187))) = d10 p
  rw [sub1968, sub1966]
  rfl
theorem sub1970 (p : Pattern) : d11 (change p 186 (some 187)) = d11 p := by
  change (if p 192 then d10 (change p 186 (some 187)) else d8 (change p 186 (some 187))) = d11 p
  rw [sub1969, sub1966]
  rfl
theorem sub1971 (p : Pattern) : d61 (change p 186 (some 187)) = d11 p := by
  change d11 (change p 186 (some 187)) = d11 p
  exact sub1970 p
theorem sub1972 (p : Pattern) : d62 (change p 186 (some 187)) = d12 p := by
  change (if p 168 then d61 (change p 186 (some 187)) else d56 (change p 186 (some 187))) = d12 p
  rw [sub1971, sub1964]
  rfl
theorem sub1973 (p : Pattern) : d451 (change p 186 (some 187)) = d13 p := by
  change (if p 141 then d62 (change p 186 (some 187)) else d56 (change p 186 (some 187))) = d13 p
  rw [sub1972, sub1964]
  rfl
theorem sub1974 (p : Pattern) : d4 (change p 186 (some 187)) = d4 p := by
  rfl
theorem sub1975 (p : Pattern) : d54 (change p 186 (some 187)) = d54 p := by
  change (if p 193 then d4 (change p 186 (some 187)) else d2 (change p 186 (some 187))) = d54 p
  rw [sub1974, sub1961]
  rfl
theorem sub1976 (p : Pattern) : d55 (change p 186 (some 187)) = d55 p := by
  change (if p 192 then d54 (change p 186 (some 187)) else d2 (change p 186 (some 187))) = d55 p
  rw [sub1975, sub1961]
  rfl
theorem sub1977 (p : Pattern) : d452 (change p 186 (some 187)) = d106 p := by
  change (if p 160 then d55 (change p 186 (some 187)) else d56 (change p 186 (some 187))) = d106 p
  rw [sub1976, sub1964]
  rfl
theorem sub1978 (p : Pattern) : d5 (change p 186 (some 187)) = d5 p := by
  rfl
theorem sub1979 (p : Pattern) : d58 (change p 186 (some 187)) = d58 p := by
  change (if p 271 then d5 (change p 186 (some 187)) else d4 (change p 186 (some 187))) = d58 p
  rw [sub1978, sub1974]
  rfl
theorem sub1980 (p : Pattern) : d59 (change p 186 (some 187)) = d59 p := by
  change (if p 193 then d58 (change p 186 (some 187)) else d9 (change p 186 (some 187))) = d59 p
  rw [sub1979, sub1968]
  rfl
theorem sub1981 (p : Pattern) : d60 (change p 186 (some 187)) = d60 p := by
  change (if p 192 then d59 (change p 186 (some 187)) else d9 (change p 186 (some 187))) = d60 p
  rw [sub1980, sub1968]
  rfl
theorem sub1982 (p : Pattern) : d65 (change p 186 (some 187)) = d65 p := by
  change (if p 168 then d60 (change p 186 (some 187)) else d55 (change p 186 (some 187))) = d65 p
  rw [sub1981, sub1976]
  rfl
theorem sub1983 (p : Pattern) : d453 (change p 186 (some 187)) = d109 p := by
  change (if p 160 then d65 (change p 186 (some 187)) else d62 (change p 186 (some 187))) = d109 p
  rw [sub1982, sub1972]
  rfl
theorem sub1984 (p : Pattern) : d454 (change p 186 (some 187)) = d227 p := by
  change (if p 141 then d453 (change p 186 (some 187)) else d452 (change p 186 (some 187))) = d227 p
  rw [sub1983, sub1977]
  rfl
theorem sub1985 (p : Pattern) : d455 (change p 186 (some 187)) = d1018 p := by
  change (if p 134 then d454 (change p 186 (some 187)) else d451 (change p 186 (some 187))) = d1018 p
  rw [sub1984, sub1973]
  rfl
theorem sub1986 (p : Pattern) : d456 (change p 186 (some 187)) = d832 p := by
  change (if p 158 then d55 (change p 186 (some 187)) else d56 (change p 186 (some 187))) = d832 p
  rw [sub1976, sub1964]
  rfl
theorem sub1987 (p : Pattern) : d457 (change p 186 (some 187)) = d833 p := by
  change (if p 158 then d65 (change p 186 (some 187)) else d62 (change p 186 (some 187))) = d833 p
  rw [sub1982, sub1972]
  rfl
theorem sub1988 (p : Pattern) : d458 (change p 186 (some 187)) = d834 p := by
  change (if p 141 then d457 (change p 186 (some 187)) else d456 (change p 186 (some 187))) = d834 p
  rw [sub1987, sub1986]
  rfl
theorem sub1989 (p : Pattern) : d459 (change p 186 (some 187)) = d229 p := by
  change (if p 158 then d55 (change p 186 (some 187)) else d452 (change p 186 (some 187))) = d229 p
  rw [sub1976, sub1977]
  rfl
theorem sub1990 (p : Pattern) : d460 (change p 186 (some 187)) = d230 p := by
  change (if p 158 then d65 (change p 186 (some 187)) else d453 (change p 186 (some 187))) = d230 p
  rw [sub1982, sub1983]
  rfl
theorem sub1991 (p : Pattern) : d461 (change p 186 (some 187)) = d231 p := by
  change (if p 141 then d460 (change p 186 (some 187)) else d459 (change p 186 (some 187))) = d231 p
  rw [sub1990, sub1989]
  rfl
theorem sub1992 (p : Pattern) : d462 (change p 186 (some 187)) = d1019 p := by
  change (if p 134 then d461 (change p 186 (some 187)) else d458 (change p 186 (some 187))) = d1019 p
  rw [sub1991, sub1988]
  rfl
theorem sub1993 (p : Pattern) : d463 (change p 186 (some 187)) = d1020 p := by
  change (if p 133 then d462 (change p 186 (some 187)) else d455 (change p 186 (some 187))) = d1020 p
  rw [sub1992, sub1985]
  rfl
theorem sub1994 (p : Pattern) : d66 (change p 186 (some 187)) = d66 p := by
  change (if p 141 then d65 (change p 186 (some 187)) else d55 (change p 186 (some 187))) = d66 p
  rw [sub1982, sub1976]
  rfl
theorem sub1995 (p : Pattern) : d464 (change p 186 (some 187)) = d1021 p := by
  change (if p 133 then d66 (change p 186 (some 187)) else d462 (change p 186 (some 187))) = d1021 p
  rw [sub1994, sub1992]
  rfl
theorem sub1996 (p : Pattern) : d465 (change p 186 (some 187)) = d1022 p := by
  change (if p 132 then d464 (change p 186 (some 187)) else d463 (change p 186 (some 187))) = d1022 p
  rw [sub1995, sub1993]
  rfl
theorem sub1997 (p : Pattern) : d119 (change p 186 (some 187)) = d55 p := by
  change d55 (change p 186 (some 187)) = d55 p
  exact sub1976 p
theorem sub1998 (p : Pattern) : d137 (change p 186 (some 187)) = d55 p := by
  change d119 (change p 186 (some 187)) = d55 p
  exact sub1997 p
theorem sub1999 (p : Pattern) : d466 (change p 186 (some 187)) = d106 p := by
  change (if p 160 then d137 (change p 186 (some 187)) else d56 (change p 186 (some 187))) = d106 p
  rw [sub1998, sub1964]
  rfl
theorem sub2000 (p : Pattern) : d467 (change p 186 (some 187)) = d1159 p := by
  change (if p 159 then d466 (change p 186 (some 187)) else d56 (change p 186 (some 187))) = d1159 p
  rw [sub1999, sub1964]
  rfl
theorem sub2001 (p : Pattern) : d468 (change p 186 (some 187)) = d1160 p := by
  change (if p 158 then d467 (change p 186 (some 187)) else d56 (change p 186 (some 187))) = d1160 p
  rw [sub2000, sub1964]
  rfl
theorem sub2002 (p : Pattern) : d125 (change p 186 (some 187)) = d60 p := by
  change d60 (change p 186 (some 187)) = d60 p
  exact sub1981 p
theorem sub2003 (p : Pattern) : d143 (change p 186 (some 187)) = d60 p := by
  change d125 (change p 186 (some 187)) = d60 p
  exact sub2002 p
theorem sub2004 (p : Pattern) : d144 (change p 186 (some 187)) = d65 p := by
  change (if p 168 then d143 (change p 186 (some 187)) else d137 (change p 186 (some 187))) = d65 p
  rw [sub2003, sub1998]
  rfl
theorem sub2005 (p : Pattern) : d469 (change p 186 (some 187)) = d109 p := by
  change (if p 160 then d144 (change p 186 (some 187)) else d62 (change p 186 (some 187))) = d109 p
  rw [sub2004, sub1972]
  rfl
theorem sub2006 (p : Pattern) : d470 (change p 186 (some 187)) = d1161 p := by
  change (if p 159 then d469 (change p 186 (some 187)) else d62 (change p 186 (some 187))) = d1161 p
  rw [sub2005, sub1972]
  rfl
theorem sub2007 (p : Pattern) : d471 (change p 186 (some 187)) = d1162 p := by
  change (if p 158 then d470 (change p 186 (some 187)) else d62 (change p 186 (some 187))) = d1162 p
  rw [sub2006, sub1972]
  rfl
theorem sub2008 (p : Pattern) : d472 (change p 186 (some 187)) = d1163 p := by
  change (if p 141 then d471 (change p 186 (some 187)) else d468 (change p 186 (some 187))) = d1163 p
  rw [sub2007, sub2001]
  rfl
theorem sub2009 (p : Pattern) : d473 (change p 186 (some 187)) = d1164 p := by
  change (if p 134 then d66 (change p 186 (some 187)) else d472 (change p 186 (some 187))) = d1164 p
  rw [sub1994, sub2008]
  rfl
theorem sub2010 (p : Pattern) : d474 (change p 186 (some 187)) = d229 p := by
  change (if p 158 then d55 (change p 186 (some 187)) else d466 (change p 186 (some 187))) = d229 p
  rw [sub1976, sub1999]
  rfl
theorem sub2011 (p : Pattern) : d475 (change p 186 (some 187)) = d230 p := by
  change (if p 158 then d65 (change p 186 (some 187)) else d469 (change p 186 (some 187))) = d230 p
  rw [sub1982, sub2005]
  rfl
theorem sub2012 (p : Pattern) : d476 (change p 186 (some 187)) = d231 p := by
  change (if p 141 then d475 (change p 186 (some 187)) else d474 (change p 186 (some 187))) = d231 p
  rw [sub2011, sub2010]
  rfl
theorem sub2013 (p : Pattern) : d477 (change p 186 (some 187)) = d370 p := by
  change (if p 134 then d66 (change p 186 (some 187)) else d476 (change p 186 (some 187))) = d370 p
  rw [sub1994, sub2012]
  rfl
theorem sub2014 (p : Pattern) : d478 (change p 186 (some 187)) = d1165 p := by
  change (if p 133 then d477 (change p 186 (some 187)) else d473 (change p 186 (some 187))) = d1165 p
  rw [sub2013, sub2009]
  rfl
theorem sub2015 (p : Pattern) : d479 (change p 186 (some 187)) = d1166 p := by
  change (if p 158 then d55 (change p 186 (some 187)) else d467 (change p 186 (some 187))) = d1166 p
  rw [sub1976, sub2000]
  rfl
theorem sub2016 (p : Pattern) : d480 (change p 186 (some 187)) = d1167 p := by
  change (if p 158 then d65 (change p 186 (some 187)) else d470 (change p 186 (some 187))) = d1167 p
  rw [sub1982, sub2006]
  rfl
theorem sub2017 (p : Pattern) : d481 (change p 186 (some 187)) = d1168 p := by
  change (if p 141 then d480 (change p 186 (some 187)) else d479 (change p 186 (some 187))) = d1168 p
  rw [sub2016, sub2015]
  rfl
theorem sub2018 (p : Pattern) : d482 (change p 186 (some 187)) = d1169 p := by
  change (if p 134 then d66 (change p 186 (some 187)) else d481 (change p 186 (some 187))) = d1169 p
  rw [sub1994, sub2017]
  rfl
theorem sub2019 (p : Pattern) : d483 (change p 186 (some 187)) = d1170 p := by
  change (if p 133 then d66 (change p 186 (some 187)) else d482 (change p 186 (some 187))) = d1170 p
  rw [sub1994, sub2018]
  rfl
theorem sub2020 (p : Pattern) : d484 (change p 186 (some 187)) = d1171 p := by
  change (if p 132 then d483 (change p 186 (some 187)) else d478 (change p 186 (some 187))) = d1171 p
  rw [sub2019, sub2014]
  rfl
theorem sub2021 (p : Pattern) : d485 (change p 186 (some 187)) = d1172 p := by
  change (if p 108 then d484 (change p 186 (some 187)) else d465 (change p 186 (some 187))) = d1172 p
  rw [sub2020, sub1996]
  rfl
theorem sub2022 (p : Pattern) : d0 (change p 160 (some 134)) = d0 p := by
  rfl
theorem sub2023 (p : Pattern) : d2 (change p 160 (some 134)) = d2 p := by
  rfl
theorem sub2024 (p : Pattern) : d6 (change p 160 (some 134)) = d6 p := by
  change (if p 193 then d2 (change p 160 (some 134)) else d0 (change p 160 (some 134))) = d6 p
  rw [sub2023, sub2022]
  rfl
theorem sub2025 (p : Pattern) : d7 (change p 160 (some 134)) = d7 p := by
  change (if p 192 then d6 (change p 160 (some 134)) else d0 (change p 160 (some 134))) = d7 p
  rw [sub2024, sub2022]
  rfl
theorem sub2026 (p : Pattern) : d106 (change p 160 (some 134)) = d7 p := by
  change d7 (change p 160 (some 134)) = d7 p
  exact sub2025 p
theorem sub2027 (p : Pattern) : d1 (change p 160 (some 134)) = d1 p := by
  rfl
theorem sub2028 (p : Pattern) : d8 (change p 160 (some 134)) = d8 p := by
  change (if p 271 then d1 (change p 160 (some 134)) else d0 (change p 160 (some 134))) = d8 p
  rw [sub2027, sub2022]
  rfl
theorem sub2029 (p : Pattern) : d3 (change p 160 (some 134)) = d3 p := by
  rfl
theorem sub2030 (p : Pattern) : d9 (change p 160 (some 134)) = d9 p := by
  change (if p 271 then d3 (change p 160 (some 134)) else d2 (change p 160 (some 134))) = d9 p
  rw [sub2029, sub2023]
  rfl
theorem sub2031 (p : Pattern) : d10 (change p 160 (some 134)) = d10 p := by
  change (if p 193 then d9 (change p 160 (some 134)) else d8 (change p 160 (some 134))) = d10 p
  rw [sub2030, sub2028]
  rfl
theorem sub2032 (p : Pattern) : d11 (change p 160 (some 134)) = d11 p := by
  change (if p 192 then d10 (change p 160 (some 134)) else d8 (change p 160 (some 134))) = d11 p
  rw [sub2031, sub2028]
  rfl
theorem sub2033 (p : Pattern) : d12 (change p 160 (some 134)) = d12 p := by
  change (if p 168 then d11 (change p 160 (some 134)) else d7 (change p 160 (some 134))) = d12 p
  rw [sub2032, sub2025]
  rfl
theorem sub2034 (p : Pattern) : d109 (change p 160 (some 134)) = d12 p := by
  change d12 (change p 160 (some 134)) = d12 p
  exact sub2033 p
theorem sub2035 (p : Pattern) : d227 (change p 160 (some 134)) = d13 p := by
  change (if p 141 then d109 (change p 160 (some 134)) else d106 (change p 160 (some 134))) = d13 p
  rw [sub2034, sub2026]
  rfl
theorem sub2036 (p : Pattern) : d4 (change p 160 (some 134)) = d4 p := by
  rfl
theorem sub2037 (p : Pattern) : d54 (change p 160 (some 134)) = d54 p := by
  change (if p 193 then d4 (change p 160 (some 134)) else d2 (change p 160 (some 134))) = d54 p
  rw [sub2036, sub2023]
  rfl
theorem sub2038 (p : Pattern) : d55 (change p 160 (some 134)) = d55 p := by
  change (if p 192 then d54 (change p 160 (some 134)) else d2 (change p 160 (some 134))) = d55 p
  rw [sub2037, sub2023]
  rfl
theorem sub2039 (p : Pattern) : d229 (change p 160 (some 134)) = d832 p := by
  change (if p 158 then d55 (change p 160 (some 134)) else d106 (change p 160 (some 134))) = d832 p
  rw [sub2038, sub2026]
  rfl
end NetHack.Sokoban12CostPartition
