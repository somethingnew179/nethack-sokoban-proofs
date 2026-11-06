/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1920 (p : Pattern) : d325 (change p 133 (some 132)) = d1163 p := by
  change (if p 106 then d324 (change p 133 (some 132)) else d314 (change p 133 (some 132))) = d1163 p
  rw [sub1919, sub1909]
  rfl
theorem sub1921 (p : Pattern) : d326 (change p 133 (some 132)) = d1164 p := by
  change (if p 86 then d325 (change p 133 (some 132)) else d321 (change p 133 (some 132))) = d1164 p
  rw [sub1920, sub1916]
  rfl
theorem sub1922 (p : Pattern) : d327 (change p 133 (some 132)) = d1165 p := by
  change (if p 80 then d326 (change p 133 (some 132)) else d316 (change p 133 (some 132))) = d1165 p
  rw [sub1921, sub1911]
  rfl
theorem sub1923 (p : Pattern) : d0 (change p 134 (some 133)) = d0 p := by
  rfl
theorem sub1924 (p : Pattern) : d2 (change p 134 (some 133)) = d2 p := by
  rfl
theorem sub1925 (p : Pattern) : d3 (change p 134 (some 133)) = d3 p := by
  change (if p 161 then d2 (change p 134 (some 133)) else d0 (change p 134 (some 133))) = d3 p
  rw [sub1924, sub1923]
  rfl
theorem sub1926 (p : Pattern) : d4 (change p 134 (some 133)) = d4 p := by
  change (if p 160 then d3 (change p 134 (some 133)) else d0 (change p 134 (some 133))) = d4 p
  rw [sub1925, sub1923]
  rfl
theorem sub1927 (p : Pattern) : d5 (change p 134 (some 133)) = d5 p := by
  change (if p 160 then d2 (change p 134 (some 133)) else d0 (change p 134 (some 133))) = d5 p
  rw [sub1924, sub1923]
  rfl
theorem sub1928 (p : Pattern) : d6 (change p 134 (some 133)) = d6 p := by
  change (if p 159 then d5 (change p 134 (some 133)) else d4 (change p 134 (some 133))) = d6 p
  rw [sub1927, sub1926]
  rfl
theorem sub1929 (p : Pattern) : d7 (change p 134 (some 133)) = d7 p := by
  change (if p 159 then d2 (change p 134 (some 133)) else d4 (change p 134 (some 133))) = d7 p
  rw [sub1924, sub1926]
  rfl
theorem sub1930 (p : Pattern) : d8 (change p 134 (some 133)) = d8 p := by
  change (if p 158 then d7 (change p 134 (some 133)) else d6 (change p 134 (some 133))) = d8 p
  rw [sub1929, sub1928]
  rfl
theorem sub1931 (p : Pattern) : d1 (change p 134 (some 133)) = d1 p := by
  rfl
theorem sub1932 (p : Pattern) : d9 (change p 134 (some 133)) = d9 p := by
  change (if p 161 then d2 (change p 134 (some 133)) else d1 (change p 134 (some 133))) = d9 p
  rw [sub1924, sub1931]
  rfl
theorem sub1933 (p : Pattern) : d10 (change p 134 (some 133)) = d10 p := by
  change (if p 160 then d9 (change p 134 (some 133)) else d1 (change p 134 (some 133))) = d10 p
  rw [sub1932, sub1931]
  rfl
theorem sub1934 (p : Pattern) : d11 (change p 134 (some 133)) = d11 p := by
  change (if p 160 then d2 (change p 134 (some 133)) else d1 (change p 134 (some 133))) = d11 p
  rw [sub1924, sub1931]
  rfl
theorem sub1935 (p : Pattern) : d12 (change p 134 (some 133)) = d12 p := by
  change (if p 159 then d11 (change p 134 (some 133)) else d10 (change p 134 (some 133))) = d12 p
  rw [sub1934, sub1933]
  rfl
theorem sub1936 (p : Pattern) : d13 (change p 134 (some 133)) = d13 p := by
  change (if p 159 then d2 (change p 134 (some 133)) else d10 (change p 134 (some 133))) = d13 p
  rw [sub1924, sub1933]
  rfl
theorem sub1937 (p : Pattern) : d14 (change p 134 (some 133)) = d14 p := by
  change (if p 158 then d13 (change p 134 (some 133)) else d12 (change p 134 (some 133))) = d14 p
  rw [sub1936, sub1935]
  rfl
theorem sub1938 (p : Pattern) : d15 (change p 134 (some 133)) = d15 p := by
  change (if p 139 then d14 (change p 134 (some 133)) else d8 (change p 134 (some 133))) = d15 p
  rw [sub1937, sub1930]
  rfl
theorem sub1939 (p : Pattern) : d16 (change p 134 (some 133)) = d16 p := by
  change (if p 138 then d15 (change p 134 (some 133)) else d8 (change p 134 (some 133))) = d16 p
  rw [sub1938, sub1930]
  rfl
theorem sub1940 (p : Pattern) : d328 (change p 134 (some 133)) = d16 p := by
  change d16 (change p 134 (some 133)) = d16 p
  exact sub1939 p
theorem sub1941 (p : Pattern) : d37 (change p 134 (some 133)) = d37 p := by
  change (if p 159 then d2 (change p 134 (some 133)) else d5 (change p 134 (some 133))) = d37 p
  rw [sub1924, sub1927]
  rfl
theorem sub1942 (p : Pattern) : d38 (change p 134 (some 133)) = d38 p := by
  change (if p 158 then d37 (change p 134 (some 133)) else d6 (change p 134 (some 133))) = d38 p
  rw [sub1941, sub1928]
  rfl
theorem sub1943 (p : Pattern) : d39 (change p 134 (some 133)) = d39 p := by
  change (if p 159 then d2 (change p 134 (some 133)) else d11 (change p 134 (some 133))) = d39 p
  rw [sub1924, sub1934]
  rfl
theorem sub1944 (p : Pattern) : d40 (change p 134 (some 133)) = d40 p := by
  change (if p 158 then d39 (change p 134 (some 133)) else d12 (change p 134 (some 133))) = d40 p
  rw [sub1943, sub1935]
  rfl
theorem sub1945 (p : Pattern) : d41 (change p 134 (some 133)) = d41 p := by
  change (if p 139 then d40 (change p 134 (some 133)) else d38 (change p 134 (some 133))) = d41 p
  rw [sub1944, sub1942]
  rfl
theorem sub1946 (p : Pattern) : d42 (change p 134 (some 133)) = d42 p := by
  change (if p 138 then d41 (change p 134 (some 133)) else d38 (change p 134 (some 133))) = d42 p
  rw [sub1945, sub1942]
  rfl
theorem sub1947 (p : Pattern) : d329 (change p 134 (some 133)) = d42 p := by
  change d42 (change p 134 (some 133)) = d42 p
  exact sub1946 p
theorem sub1948 (p : Pattern) : d330 (change p 134 (some 133)) = d42 p := by
  change d329 (change p 134 (some 133)) = d42 p
  exact sub1947 p
theorem sub1949 (p : Pattern) : d331 (change p 134 (some 133)) = d1255 p := by
  change (if p 132 then d330 (change p 134 (some 133)) else d328 (change p 134 (some 133))) = d1255 p
  rw [sub1948, sub1940]
  rfl
theorem sub1950 (p : Pattern) : d332 (change p 134 (some 133)) = d15 p := by
  change d15 (change p 134 (some 133)) = d15 p
  exact sub1938 p
theorem sub1951 (p : Pattern) : d333 (change p 134 (some 133)) = d41 p := by
  change d41 (change p 134 (some 133)) = d41 p
  exact sub1945 p
theorem sub1952 (p : Pattern) : d334 (change p 134 (some 133)) = d41 p := by
  change d333 (change p 134 (some 133)) = d41 p
  exact sub1951 p
theorem sub1953 (p : Pattern) : d335 (change p 134 (some 133)) = d1256 p := by
  change (if p 132 then d334 (change p 134 (some 133)) else d332 (change p 134 (some 133))) = d1256 p
  rw [sub1952, sub1950]
  rfl
theorem sub1954 (p : Pattern) : d52 (change p 134 (some 133)) = d52 p := by
  change (if p 139 then d2 (change p 134 (some 133)) else d8 (change p 134 (some 133))) = d52 p
  rw [sub1924, sub1930]
  rfl
theorem sub1955 (p : Pattern) : d53 (change p 134 (some 133)) = d53 p := by
  change (if p 138 then d52 (change p 134 (some 133)) else d15 (change p 134 (some 133))) = d53 p
  rw [sub1954, sub1938]
  rfl
theorem sub1956 (p : Pattern) : d336 (change p 134 (some 133)) = d53 p := by
  change d53 (change p 134 (some 133)) = d53 p
  exact sub1955 p
theorem sub1957 (p : Pattern) : d61 (change p 134 (some 133)) = d61 p := by
  change (if p 139 then d2 (change p 134 (some 133)) else d38 (change p 134 (some 133))) = d61 p
  rw [sub1924, sub1942]
  rfl
theorem sub1958 (p : Pattern) : d62 (change p 134 (some 133)) = d62 p := by
  change (if p 138 then d61 (change p 134 (some 133)) else d41 (change p 134 (some 133))) = d62 p
  rw [sub1957, sub1945]
  rfl
theorem sub1959 (p : Pattern) : d337 (change p 134 (some 133)) = d62 p := by
  change d62 (change p 134 (some 133)) = d62 p
  exact sub1958 p
theorem sub1960 (p : Pattern) : d338 (change p 134 (some 133)) = d62 p := by
  change d337 (change p 134 (some 133)) = d62 p
  exact sub1959 p
theorem sub1961 (p : Pattern) : d339 (change p 134 (some 133)) = d1257 p := by
  change (if p 132 then d338 (change p 134 (some 133)) else d336 (change p 134 (some 133))) = d1257 p
  rw [sub1960, sub1956]
  rfl
theorem sub1962 (p : Pattern) : d340 (change p 134 (some 133)) = d1258 p := by
  change (if p 113 then d339 (change p 134 (some 133)) else d335 (change p 134 (some 133))) = d1258 p
  rw [sub1961, sub1953]
  rfl
theorem sub1963 (p : Pattern) : d341 (change p 134 (some 133)) = d1259 p := by
  change (if p 112 then d340 (change p 134 (some 133)) else d331 (change p 134 (some 133))) = d1259 p
  rw [sub1962, sub1949]
  rfl
theorem sub1964 (p : Pattern) : d68 (change p 134 (some 133)) = d68 p := by
  change (if p 139 then d2 (change p 134 (some 133)) else d40 (change p 134 (some 133))) = d68 p
  rw [sub1924, sub1944]
  rfl
theorem sub1965 (p : Pattern) : d69 (change p 134 (some 133)) = d69 p := by
  change (if p 138 then d68 (change p 134 (some 133)) else d40 (change p 134 (some 133))) = d69 p
  rw [sub1964, sub1944]
  rfl
theorem sub1966 (p : Pattern) : d342 (change p 134 (some 133)) = d69 p := by
  change d69 (change p 134 (some 133)) = d69 p
  exact sub1965 p
theorem sub1967 (p : Pattern) : d343 (change p 134 (some 133)) = d69 p := by
  change d342 (change p 134 (some 133)) = d69 p
  exact sub1966 p
theorem sub1968 (p : Pattern) : d344 (change p 134 (some 133)) = d1260 p := by
  change (if p 132 then d343 (change p 134 (some 133)) else d328 (change p 134 (some 133))) = d1260 p
  rw [sub1967, sub1940]
  rfl
theorem sub1969 (p : Pattern) : d345 (change p 134 (some 133)) = d68 p := by
  change d68 (change p 134 (some 133)) = d68 p
  exact sub1964 p
theorem sub1970 (p : Pattern) : d346 (change p 134 (some 133)) = d68 p := by
  change d345 (change p 134 (some 133)) = d68 p
  exact sub1969 p
theorem sub1971 (p : Pattern) : d347 (change p 134 (some 133)) = d1261 p := by
  change (if p 132 then d346 (change p 134 (some 133)) else d328 (change p 134 (some 133))) = d1261 p
  rw [sub1970, sub1940]
  rfl
theorem sub1972 (p : Pattern) : d348 (change p 134 (some 133)) = d1262 p := by
  change (if p 113 then d347 (change p 134 (some 133)) else d344 (change p 134 (some 133))) = d1262 p
  rw [sub1971, sub1968]
  rfl
theorem sub1973 (p : Pattern) : d349 (change p 134 (some 133)) = d68 p := by
  change d345 (change p 134 (some 133)) = d68 p
  exact sub1969 p
theorem sub1974 (p : Pattern) : d350 (change p 134 (some 133)) = d1263 p := by
  change (if p 132 then d349 (change p 134 (some 133)) else d332 (change p 134 (some 133))) = d1263 p
  rw [sub1973, sub1950]
  rfl
theorem sub1975 (p : Pattern) : d351 (change p 134 (some 133)) = d68 p := by
  change d345 (change p 134 (some 133)) = d68 p
  exact sub1969 p
theorem sub1976 (p : Pattern) : d352 (change p 134 (some 133)) = d1264 p := by
  change (if p 132 then d351 (change p 134 (some 133)) else d336 (change p 134 (some 133))) = d1264 p
  rw [sub1975, sub1956]
  rfl
theorem sub1977 (p : Pattern) : d353 (change p 134 (some 133)) = d1265 p := by
  change (if p 113 then d352 (change p 134 (some 133)) else d350 (change p 134 (some 133))) = d1265 p
  rw [sub1976, sub1974]
  rfl
theorem sub1978 (p : Pattern) : d354 (change p 134 (some 133)) = d1266 p := by
  change (if p 112 then d353 (change p 134 (some 133)) else d348 (change p 134 (some 133))) = d1266 p
  rw [sub1977, sub1972]
  rfl
theorem sub1979 (p : Pattern) : d355 (change p 134 (some 133)) = d1267 p := by
  change (if p 106 then d354 (change p 134 (some 133)) else d341 (change p 134 (some 133))) = d1267 p
  rw [sub1978, sub1963]
  rfl
theorem sub1980 (p : Pattern) : d86 (change p 134 (some 133)) = d86 p := by
  change (if p 138 then d52 (change p 134 (some 133)) else d8 (change p 134 (some 133))) = d86 p
  rw [sub1954, sub1930]
  rfl
theorem sub1981 (p : Pattern) : d356 (change p 134 (some 133)) = d86 p := by
  change d86 (change p 134 (some 133)) = d86 p
  exact sub1980 p
theorem sub1982 (p : Pattern) : d92 (change p 134 (some 133)) = d92 p := by
  change (if p 138 then d61 (change p 134 (some 133)) else d38 (change p 134 (some 133))) = d92 p
  rw [sub1957, sub1942]
  rfl
theorem sub1983 (p : Pattern) : d357 (change p 134 (some 133)) = d92 p := by
  change d92 (change p 134 (some 133)) = d92 p
  exact sub1982 p
theorem sub1984 (p : Pattern) : d358 (change p 134 (some 133)) = d92 p := by
  change d357 (change p 134 (some 133)) = d92 p
  exact sub1983 p
theorem sub1985 (p : Pattern) : d359 (change p 134 (some 133)) = d1268 p := by
  change (if p 132 then d358 (change p 134 (some 133)) else d356 (change p 134 (some 133))) = d1268 p
  rw [sub1984, sub1981]
  rfl
theorem sub1986 (p : Pattern) : d360 (change p 134 (some 133)) = d1269 p := by
  change (if p 113 then d359 (change p 134 (some 133)) else d331 (change p 134 (some 133))) = d1269 p
  rw [sub1985, sub1949]
  rfl
theorem sub1987 (p : Pattern) : d97 (change p 134 (some 133)) = d97 p := by
  change (if p 139 then d2 (change p 134 (some 133)) else d14 (change p 134 (some 133))) = d97 p
  rw [sub1924, sub1937]
  rfl
theorem sub1988 (p : Pattern) : d98 (change p 134 (some 133)) = d98 p := by
  change (if p 138 then d97 (change p 134 (some 133)) else d14 (change p 134 (some 133))) = d98 p
  rw [sub1987, sub1937]
  rfl
theorem sub1989 (p : Pattern) : d361 (change p 134 (some 133)) = d98 p := by
  change d98 (change p 134 (some 133)) = d98 p
  exact sub1988 p
theorem sub1990 (p : Pattern) : d362 (change p 134 (some 133)) = d69 p := by
  change d342 (change p 134 (some 133)) = d69 p
  exact sub1966 p
theorem sub1991 (p : Pattern) : d363 (change p 134 (some 133)) = d1270 p := by
  change (if p 132 then d362 (change p 134 (some 133)) else d361 (change p 134 (some 133))) = d1270 p
  rw [sub1990, sub1989]
  rfl
theorem sub1992 (p : Pattern) : d364 (change p 134 (some 133)) = d1271 p := by
  change (if p 112 then d363 (change p 134 (some 133)) else d360 (change p 134 (some 133))) = d1271 p
  rw [sub1991, sub1986]
  rfl
theorem sub1993 (p : Pattern) : d365 (change p 134 (some 133)) = d68 p := by
  change d345 (change p 134 (some 133)) = d68 p
  exact sub1969 p
theorem sub1994 (p : Pattern) : d366 (change p 134 (some 133)) = d1272 p := by
  change (if p 132 then d365 (change p 134 (some 133)) else d356 (change p 134 (some 133))) = d1272 p
  rw [sub1993, sub1981]
  rfl
theorem sub1995 (p : Pattern) : d367 (change p 134 (some 133)) = d1273 p := by
  change (if p 113 then d366 (change p 134 (some 133)) else d347 (change p 134 (some 133))) = d1273 p
  rw [sub1994, sub1971]
  rfl
theorem sub1996 (p : Pattern) : d368 (change p 134 (some 133)) = d2 p := by
  change d2 (change p 134 (some 133)) = d2 p
  exact sub1924 p
theorem sub1997 (p : Pattern) : d369 (change p 134 (some 133)) = d1274 p := by
  change (if p 132 then d368 (change p 134 (some 133)) else d361 (change p 134 (some 133))) = d1274 p
  rw [sub1996, sub1989]
  rfl
theorem sub1998 (p : Pattern) : d370 (change p 134 (some 133)) = d97 p := by
  change d97 (change p 134 (some 133)) = d97 p
  exact sub1987 p
theorem sub1999 (p : Pattern) : d371 (change p 134 (some 133)) = d2 p := by
  change d2 (change p 134 (some 133)) = d2 p
  exact sub1924 p
theorem sub2000 (p : Pattern) : d372 (change p 134 (some 133)) = d1275 p := by
  change (if p 132 then d371 (change p 134 (some 133)) else d370 (change p 134 (some 133))) = d1275 p
  rw [sub1999, sub1998]
  rfl
theorem sub2001 (p : Pattern) : d373 (change p 134 (some 133)) = d1276 p := by
  change (if p 113 then d372 (change p 134 (some 133)) else d369 (change p 134 (some 133))) = d1276 p
  rw [sub2000, sub1997]
  rfl
theorem sub2002 (p : Pattern) : d374 (change p 134 (some 133)) = d1277 p := by
  change (if p 112 then d373 (change p 134 (some 133)) else d367 (change p 134 (some 133))) = d1277 p
  rw [sub2001, sub1995]
  rfl
theorem sub2003 (p : Pattern) : d375 (change p 134 (some 133)) = d1278 p := by
  change (if p 106 then d374 (change p 134 (some 133)) else d364 (change p 134 (some 133))) = d1278 p
  rw [sub2002, sub1992]
  rfl
theorem sub2004 (p : Pattern) : d376 (change p 134 (some 133)) = d1279 p := by
  change (if p 86 then d375 (change p 134 (some 133)) else d355 (change p 134 (some 133))) = d1279 p
  rw [sub2003, sub1979]
  rfl
theorem sub2005 (p : Pattern) : d377 (change p 134 (some 133)) = d1280 p := by
  change (if p 112 then d353 (change p 134 (some 133)) else d347 (change p 134 (some 133))) = d1280 p
  rw [sub1977, sub1971]
  rfl
theorem sub2006 (p : Pattern) : d378 (change p 134 (some 133)) = d1281 p := by
  change (if p 106 then d377 (change p 134 (some 133)) else d341 (change p 134 (some 133))) = d1281 p
  rw [sub2005, sub1963]
  rfl
theorem sub2007 (p : Pattern) : d379 (change p 134 (some 133)) = d68 p := by
  change d345 (change p 134 (some 133)) = d68 p
  exact sub1969 p
theorem sub2008 (p : Pattern) : d380 (change p 134 (some 133)) = d1282 p := by
  change (if p 132 then d379 (change p 134 (some 133)) else d370 (change p 134 (some 133))) = d1282 p
  rw [sub2007, sub1998]
  rfl
theorem sub2009 (p : Pattern) : d381 (change p 134 (some 133)) = d1283 p := by
  change (if p 113 then d380 (change p 134 (some 133)) else d363 (change p 134 (some 133))) = d1283 p
  rw [sub2008, sub1991]
  rfl
theorem sub2010 (p : Pattern) : d382 (change p 134 (some 133)) = d1284 p := by
  change (if p 112 then d381 (change p 134 (some 133)) else d360 (change p 134 (some 133))) = d1284 p
  rw [sub2009, sub1986]
  rfl
theorem sub2011 (p : Pattern) : d383 (change p 134 (some 133)) = d1285 p := by
  change (if p 113 then d352 (change p 134 (some 133)) else d347 (change p 134 (some 133))) = d1285 p
  rw [sub1976, sub1971]
  rfl
theorem sub2012 (p : Pattern) : d384 (change p 134 (some 133)) = d1286 p := by
  change (if p 113 then d2 (change p 134 (some 133)) else d372 (change p 134 (some 133))) = d1286 p
  rw [sub1924, sub2000]
  rfl
theorem sub2013 (p : Pattern) : d385 (change p 134 (some 133)) = d1287 p := by
  change (if p 112 then d384 (change p 134 (some 133)) else d383 (change p 134 (some 133))) = d1287 p
  rw [sub2012, sub2011]
  rfl
theorem sub2014 (p : Pattern) : d386 (change p 134 (some 133)) = d1288 p := by
  change (if p 106 then d385 (change p 134 (some 133)) else d382 (change p 134 (some 133))) = d1288 p
  rw [sub2013, sub2010]
  rfl
theorem sub2015 (p : Pattern) : d387 (change p 134 (some 133)) = d1289 p := by
  change (if p 86 then d386 (change p 134 (some 133)) else d378 (change p 134 (some 133))) = d1289 p
  rw [sub2014, sub2006]
  rfl
theorem sub2016 (p : Pattern) : d388 (change p 134 (some 133)) = d1290 p := by
  change (if p 80 then d387 (change p 134 (some 133)) else d376 (change p 134 (some 133))) = d1290 p
  rw [sub2015, sub2004]
  rfl
theorem sub2017 (p : Pattern) : d0 (change p 10000 (some 138)) = d0 p := by
  rfl
theorem sub2018 (p : Pattern) : d2 (change p 10000 (some 138)) = d2 p := by
  rfl
theorem sub2019 (p : Pattern) : d3 (change p 10000 (some 138)) = d3 p := by
  change (if p 161 then d2 (change p 10000 (some 138)) else d0 (change p 10000 (some 138))) = d3 p
  rw [sub2018, sub2017]
  rfl
theorem sub2020 (p : Pattern) : d4 (change p 10000 (some 138)) = d4 p := by
  change (if p 160 then d3 (change p 10000 (some 138)) else d0 (change p 10000 (some 138))) = d4 p
  rw [sub2019, sub2017]
  rfl
theorem sub2021 (p : Pattern) : d5 (change p 10000 (some 138)) = d5 p := by
  change (if p 160 then d2 (change p 10000 (some 138)) else d0 (change p 10000 (some 138))) = d5 p
  rw [sub2018, sub2017]
  rfl
theorem sub2022 (p : Pattern) : d6 (change p 10000 (some 138)) = d6 p := by
  change (if p 159 then d5 (change p 10000 (some 138)) else d4 (change p 10000 (some 138))) = d6 p
  rw [sub2021, sub2020]
  rfl
theorem sub2023 (p : Pattern) : d7 (change p 10000 (some 138)) = d7 p := by
  change (if p 159 then d2 (change p 10000 (some 138)) else d4 (change p 10000 (some 138))) = d7 p
  rw [sub2018, sub2020]
  rfl
theorem sub2024 (p : Pattern) : d8 (change p 10000 (some 138)) = d8 p := by
  change (if p 158 then d7 (change p 10000 (some 138)) else d6 (change p 10000 (some 138))) = d8 p
  rw [sub2023, sub2022]
  rfl
theorem sub2025 (p : Pattern) : d1 (change p 10000 (some 138)) = d1 p := by
  rfl
theorem sub2026 (p : Pattern) : d9 (change p 10000 (some 138)) = d9 p := by
  change (if p 161 then d2 (change p 10000 (some 138)) else d1 (change p 10000 (some 138))) = d9 p
  rw [sub2018, sub2025]
  rfl
theorem sub2027 (p : Pattern) : d10 (change p 10000 (some 138)) = d10 p := by
  change (if p 160 then d9 (change p 10000 (some 138)) else d1 (change p 10000 (some 138))) = d10 p
  rw [sub2026, sub2025]
  rfl
theorem sub2028 (p : Pattern) : d11 (change p 10000 (some 138)) = d11 p := by
  change (if p 160 then d2 (change p 10000 (some 138)) else d1 (change p 10000 (some 138))) = d11 p
  rw [sub2018, sub2025]
  rfl
theorem sub2029 (p : Pattern) : d12 (change p 10000 (some 138)) = d12 p := by
  change (if p 159 then d11 (change p 10000 (some 138)) else d10 (change p 10000 (some 138))) = d12 p
  rw [sub2028, sub2027]
  rfl
theorem sub2030 (p : Pattern) : d13 (change p 10000 (some 138)) = d13 p := by
  change (if p 159 then d2 (change p 10000 (some 138)) else d10 (change p 10000 (some 138))) = d13 p
  rw [sub2018, sub2027]
  rfl
theorem sub2031 (p : Pattern) : d14 (change p 10000 (some 138)) = d14 p := by
  change (if p 158 then d13 (change p 10000 (some 138)) else d12 (change p 10000 (some 138))) = d14 p
  rw [sub2030, sub2029]
  rfl
theorem sub2032 (p : Pattern) : d15 (change p 10000 (some 138)) = d15 p := by
  change (if p 139 then d14 (change p 10000 (some 138)) else d8 (change p 10000 (some 138))) = d15 p
  rw [sub2031, sub2024]
  rfl
theorem sub2033 (p : Pattern) : d16 (change p 10000 (some 138)) = d15 p := by
  change d15 (change p 10000 (some 138)) = d15 p
  exact sub2032 p
theorem sub2034 (p : Pattern) : d17 (change p 10000 (some 138)) = d17 p := by
  change (if p 160 then d2 (change p 10000 (some 138)) else d3 (change p 10000 (some 138))) = d17 p
  rw [sub2018, sub2019]
  rfl
theorem sub2035 (p : Pattern) : d18 (change p 10000 (some 138)) = d18 p := by
  change (if p 159 then d17 (change p 10000 (some 138)) else d4 (change p 10000 (some 138))) = d18 p
  rw [sub2034, sub2020]
  rfl
theorem sub2036 (p : Pattern) : d19 (change p 10000 (some 138)) = d19 p := by
  change (if p 159 then d2 (change p 10000 (some 138)) else d17 (change p 10000 (some 138))) = d19 p
  rw [sub2018, sub2034]
  rfl
theorem sub2037 (p : Pattern) : d20 (change p 10000 (some 138)) = d20 p := by
  change (if p 158 then d19 (change p 10000 (some 138)) else d18 (change p 10000 (some 138))) = d20 p
  rw [sub2036, sub2035]
  rfl
theorem sub2038 (p : Pattern) : d21 (change p 10000 (some 138)) = d21 p := by
  change (if p 160 then d2 (change p 10000 (some 138)) else d9 (change p 10000 (some 138))) = d21 p
  rw [sub2018, sub2026]
  rfl
theorem sub2039 (p : Pattern) : d22 (change p 10000 (some 138)) = d22 p := by
  change (if p 159 then d21 (change p 10000 (some 138)) else d10 (change p 10000 (some 138))) = d22 p
  rw [sub2038, sub2027]
  rfl
end NetHack.Sokoban32Refined
