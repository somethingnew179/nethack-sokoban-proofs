/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions62
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub7560 (p : Pattern) : d1925 (change p 204 none) = d5074 p := by
  change (if p 163 then d1754 (change p 204 none) else d1885 (change p 204 none)) = d5074 p
  rw [sub7365, sub7515]
  rfl
theorem sub7561 (p : Pattern) : d1926 (change p 204 none) = d5075 p := by
  change (if p 162 then d1925 (change p 204 none) else d1924 (change p 204 none)) = d5075 p
  rw [sub7560, sub7559]
  rfl
theorem sub7562 (p : Pattern) : d1927 (change p 204 none) = d5076 p := by
  change (if p 163 then d1756 (change p 204 none) else d1885 (change p 204 none)) = d5076 p
  rw [sub7368, sub7515]
  rfl
theorem sub7563 (p : Pattern) : d1928 (change p 204 none) = d5077 p := by
  change (if p 162 then d12 (change p 204 none) else d1927 (change p 204 none)) = d5077 p
  rw [sub7260, sub7562]
  rfl
theorem sub7564 (p : Pattern) : d1929 (change p 204 none) = d5078 p := by
  change (if p 161 then d1928 (change p 204 none) else d1926 (change p 204 none)) = d5078 p
  rw [sub7563, sub7561]
  rfl
theorem sub7565 (p : Pattern) : d1930 (change p 204 none) = d139 p := by
  change (if p 182 then d12 (change p 204 none) else d117 (change p 204 none)) = d139 p
  rw [sub7260, sub7552]
  rfl
theorem sub7566 (p : Pattern) : d1931 (change p 204 none) = d5079 p := by
  change (if p 163 then d1930 (change p 204 none) else d1907 (change p 204 none)) = d5079 p
  rw [sub7565, sub7540]
  rfl
theorem sub7567 (p : Pattern) : d1932 (change p 204 none) = d141 p := by
  change (if p 163 then d277 (change p 204 none) else d1910 (change p 204 none)) = d141 p
  rw [sub7376, sub7543]
  rfl
theorem sub7568 (p : Pattern) : d1933 (change p 204 none) = d5080 p := by
  change (if p 162 then d1932 (change p 204 none) else d1931 (change p 204 none)) = d5080 p
  rw [sub7567, sub7566]
  rfl
theorem sub7569 (p : Pattern) : d1934 (change p 204 none) = d143 p := by
  change (if p 163 then d538 (change p 204 none) else d1910 (change p 204 none)) = d143 p
  rw [sub7378, sub7543]
  rfl
theorem sub7570 (p : Pattern) : d1935 (change p 204 none) = d144 p := by
  change (if p 162 then d12 (change p 204 none) else d1934 (change p 204 none)) = d144 p
  rw [sub7260, sub7569]
  rfl
theorem sub7571 (p : Pattern) : d1936 (change p 204 none) = d5081 p := by
  change (if p 161 then d1935 (change p 204 none) else d1933 (change p 204 none)) = d5081 p
  rw [sub7570, sub7568]
  rfl
theorem sub7572 (p : Pattern) : d1937 (change p 204 none) = d5082 p := by
  change (if p 160 then d1936 (change p 204 none) else d1929 (change p 204 none)) = d5082 p
  rw [sub7571, sub7564]
  rfl
theorem sub7573 (p : Pattern) : d1938 (change p 204 none) = d5083 p := by
  change (if p 141 then d1937 (change p 204 none) else d1915 (change p 204 none)) = d5083 p
  rw [sub7572, sub7549]
  rfl
theorem sub7574 (p : Pattern) : d1939 (change p 204 none) = d1939 p := by
  change (if p 247 then d5 (change p 204 none) else d1 (change p 204 none)) = d1939 p
  rw [sub7504, sub7489]
  rfl
theorem sub7575 (p : Pattern) : d1940 (change p 204 none) = d1940 p := by
  change (if p 246 then d106 (change p 204 none) else d1939 (change p 204 none)) = d1940 p
  rw [sub7505, sub7574]
  rfl
theorem sub7576 (p : Pattern) : d1941 (change p 204 none) = d1941 p := by
  change (if p 225 then d1940 (change p 204 none) else d103 (change p 204 none)) = d1941 p
  rw [sub7575, sub7491]
  rfl
theorem sub7577 (p : Pattern) : d1942 (change p 204 none) = d1942 p := by
  change (if p 224 then d1940 (change p 204 none) else d1941 (change p 204 none)) = d1942 p
  rw [sub7575, sub7576]
  rfl
theorem sub7578 (p : Pattern) : d1943 (change p 204 none) = d1942 p := by
  change d1942 (change p 204 none) = d1942 p
  exact sub7577 p
theorem sub7579 (p : Pattern) : d1944 (change p 204 none) = d5084 p := by
  change (if p 182 then d1943 (change p 204 none) else d104 (change p 204 none)) = d5084 p
  rw [sub7578, sub7501]
  rfl
theorem sub7580 (p : Pattern) : d1945 (change p 204 none) = d1945 p := by
  change (if p 247 then d7 (change p 204 none) else d1 (change p 204 none)) = d1945 p
  rw [sub7508, sub7489]
  rfl
theorem sub7581 (p : Pattern) : d1946 (change p 204 none) = d1946 p := by
  change (if p 246 then d119 (change p 204 none) else d1945 (change p 204 none)) = d1946 p
  rw [sub7510, sub7580]
  rfl
theorem sub7582 (p : Pattern) : d1947 (change p 204 none) = d1947 p := by
  change (if p 225 then d1946 (change p 204 none) else d103 (change p 204 none)) = d1947 p
  rw [sub7581, sub7491]
  rfl
theorem sub7583 (p : Pattern) : d1948 (change p 204 none) = d1948 p := by
  change (if p 247 then d9 (change p 204 none) else d1 (change p 204 none)) = d1948 p
  rw [sub7291, sub7489]
  rfl
theorem sub7584 (p : Pattern) : d1949 (change p 204 none) = d1949 p := by
  change (if p 246 then d23 (change p 204 none) else d1948 (change p 204 none)) = d1949 p
  rw [sub7292, sub7583]
  rfl
theorem sub7585 (p : Pattern) : d1950 (change p 204 none) = d1950 p := by
  change (if p 225 then d1949 (change p 204 none) else d1940 (change p 204 none)) = d1950 p
  rw [sub7584, sub7575]
  rfl
theorem sub7586 (p : Pattern) : d1951 (change p 204 none) = d1951 p := by
  change (if p 224 then d1950 (change p 204 none) else d1947 (change p 204 none)) = d1951 p
  rw [sub7585, sub7582]
  rfl
theorem sub7587 (p : Pattern) : d1952 (change p 204 none) = d1951 p := by
  change d1951 (change p 204 none) = d1951 p
  exact sub7586 p
theorem sub7588 (p : Pattern) : d1953 (change p 204 none) = d5085 p := by
  change (if p 182 then d1952 (change p 204 none) else d104 (change p 204 none)) = d5085 p
  rw [sub7587, sub7501]
  rfl
theorem sub7589 (p : Pattern) : d1954 (change p 204 none) = d5086 p := by
  change (if p 163 then d1953 (change p 204 none) else d1944 (change p 204 none)) = d5086 p
  rw [sub7588, sub7579]
  rfl
theorem sub7590 (p : Pattern) : d1955 (change p 204 none) = d1955 p := by
  change (if p 246 then d57 (change p 204 none) else d102 (change p 204 none)) = d1955 p
  rw [sub7324, sub7490]
  rfl
theorem sub7591 (p : Pattern) : d1956 (change p 204 none) = d1956 p := by
  change (if p 225 then d1955 (change p 204 none) else d1940 (change p 204 none)) = d1956 p
  rw [sub7590, sub7575]
  rfl
theorem sub7592 (p : Pattern) : d1957 (change p 204 none) = d1957 p := by
  change (if p 224 then d1956 (change p 204 none) else d1947 (change p 204 none)) = d1957 p
  rw [sub7591, sub7582]
  rfl
theorem sub7593 (p : Pattern) : d1958 (change p 204 none) = d1957 p := by
  change d1957 (change p 204 none) = d1957 p
  exact sub7592 p
theorem sub7594 (p : Pattern) : d1959 (change p 204 none) = d5087 p := by
  change (if p 182 then d1958 (change p 204 none) else d104 (change p 204 none)) = d5087 p
  rw [sub7593, sub7501]
  rfl
theorem sub7595 (p : Pattern) : d1960 (change p 204 none) = d1960 p := by
  change (if p 247 then d11 (change p 204 none) else d5 (change p 204 none)) = d1960 p
  rw [sub7295, sub7504]
  rfl
theorem sub7596 (p : Pattern) : d1961 (change p 204 none) = d1961 p := by
  change (if p 246 then d39 (change p 204 none) else d1960 (change p 204 none)) = d1961 p
  rw [sub7297, sub7595]
  rfl
theorem sub7597 (p : Pattern) : d1962 (change p 204 none) = d1962 p := by
  change (if p 225 then d1961 (change p 204 none) else d107 (change p 204 none)) = d1962 p
  rw [sub7596, sub7506]
  rfl
theorem sub7598 (p : Pattern) : d1963 (change p 204 none) = d1963 p := by
  change (if p 247 then d9 (change p 204 none) else d5 (change p 204 none)) = d1963 p
  rw [sub7291, sub7504]
  rfl
theorem sub7599 (p : Pattern) : d1964 (change p 204 none) = d1964 p := by
  change (if p 246 then d23 (change p 204 none) else d1963 (change p 204 none)) = d1964 p
  rw [sub7292, sub7598]
  rfl
theorem sub7600 (p : Pattern) : d348 (change p 204 none) = d348 p := by
  change (if p 246 then d12 (change p 204 none) else d106 (change p 204 none)) = d348 p
  rw [sub7260, sub7505]
  rfl
theorem sub7601 (p : Pattern) : d1965 (change p 204 none) = d1965 p := by
  change (if p 225 then d348 (change p 204 none) else d1964 (change p 204 none)) = d1965 p
  rw [sub7600, sub7599]
  rfl
theorem sub7602 (p : Pattern) : d1966 (change p 204 none) = d1966 p := by
  change (if p 224 then d1965 (change p 204 none) else d1962 (change p 204 none)) = d1966 p
  rw [sub7601, sub7597]
  rfl
theorem sub7603 (p : Pattern) : d1967 (change p 204 none) = d1966 p := by
  change d1966 (change p 204 none) = d1966 p
  exact sub7602 p
theorem sub7604 (p : Pattern) : d1968 (change p 204 none) = d5088 p := by
  change (if p 182 then d1967 (change p 204 none) else d108 (change p 204 none)) = d5088 p
  rw [sub7603, sub7507]
  rfl
theorem sub7605 (p : Pattern) : d1969 (change p 204 none) = d5089 p := by
  change (if p 163 then d1968 (change p 204 none) else d1959 (change p 204 none)) = d5089 p
  rw [sub7604, sub7594]
  rfl
theorem sub7606 (p : Pattern) : d1970 (change p 204 none) = d5090 p := by
  change (if p 162 then d1969 (change p 204 none) else d1954 (change p 204 none)) = d5090 p
  rw [sub7605, sub7589]
  rfl
theorem sub7607 (p : Pattern) : d1971 (change p 204 none) = d5091 p := by
  change (if p 162 then d1888 (change p 204 none) else d1969 (change p 204 none)) = d5091 p
  rw [sub7518, sub7605]
  rfl
theorem sub7608 (p : Pattern) : d1972 (change p 204 none) = d5092 p := by
  change (if p 161 then d1971 (change p 204 none) else d1970 (change p 204 none)) = d5092 p
  rw [sub7607, sub7606]
  rfl
theorem sub7609 (p : Pattern) : d1973 (change p 204 none) = d5093 p := by
  change (if p 182 then d1899 (change p 204 none) else d117 (change p 204 none)) = d5093 p
  rw [sub7530, sub7552]
  rfl
theorem sub7610 (p : Pattern) : d121 (change p 204 none) = d120 p := by
  change d120 (change p 204 none) = d120 p
  exact sub7532 p
theorem sub7611 (p : Pattern) : d1974 (change p 204 none) = d5094 p := by
  change (if p 182 then d1906 (change p 204 none) else d121 (change p 204 none)) = d5094 p
  rw [sub7539, sub7610]
  rfl
theorem sub7612 (p : Pattern) : d1975 (change p 204 none) = d5095 p := by
  change (if p 163 then d1974 (change p 204 none) else d1973 (change p 204 none)) = d5095 p
  rw [sub7611, sub7609]
  rfl
theorem sub7613 (p : Pattern) : d1976 (change p 204 none) = d5096 p := by
  change (if p 162 then d12 (change p 204 none) else d1975 (change p 204 none)) = d5096 p
  rw [sub7260, sub7612]
  rfl
theorem sub7614 (p : Pattern) : d1977 (change p 204 none) = d5097 p := by
  change (if p 161 then d12 (change p 204 none) else d1976 (change p 204 none)) = d5097 p
  rw [sub7260, sub7613]
  rfl
theorem sub7615 (p : Pattern) : d1978 (change p 204 none) = d5098 p := by
  change (if p 160 then d1977 (change p 204 none) else d1972 (change p 204 none)) = d5098 p
  rw [sub7614, sub7608]
  rfl
theorem sub7616 (p : Pattern) : d1979 (change p 204 none) = d5099 p := by
  change (if p 163 then d1973 (change p 204 none) else d1953 (change p 204 none)) = d5099 p
  rw [sub7609, sub7588]
  rfl
theorem sub7617 (p : Pattern) : d1980 (change p 204 none) = d5100 p := by
  change (if p 163 then d1754 (change p 204 none) else d1968 (change p 204 none)) = d5100 p
  rw [sub7365, sub7604]
  rfl
theorem sub7618 (p : Pattern) : d1981 (change p 204 none) = d5101 p := by
  change (if p 162 then d1980 (change p 204 none) else d1979 (change p 204 none)) = d5101 p
  rw [sub7617, sub7616]
  rfl
theorem sub7619 (p : Pattern) : d1982 (change p 204 none) = d5102 p := by
  change (if p 163 then d1756 (change p 204 none) else d1968 (change p 204 none)) = d5102 p
  rw [sub7368, sub7604]
  rfl
theorem sub7620 (p : Pattern) : d1983 (change p 204 none) = d5103 p := by
  change (if p 162 then d12 (change p 204 none) else d1982 (change p 204 none)) = d5103 p
  rw [sub7260, sub7619]
  rfl
theorem sub7621 (p : Pattern) : d1984 (change p 204 none) = d5104 p := by
  change (if p 161 then d1983 (change p 204 none) else d1981 (change p 204 none)) = d5104 p
  rw [sub7620, sub7618]
  rfl
theorem sub7622 (p : Pattern) : d1985 (change p 204 none) = d5105 p := by
  change (if p 163 then d12 (change p 204 none) else d1974 (change p 204 none)) = d5105 p
  rw [sub7260, sub7611]
  rfl
theorem sub7623 (p : Pattern) : d1986 (change p 204 none) = d5106 p := by
  change (if p 162 then d12 (change p 204 none) else d1985 (change p 204 none)) = d5106 p
  rw [sub7260, sub7622]
  rfl
theorem sub7624 (p : Pattern) : d1987 (change p 204 none) = d5107 p := by
  change (if p 161 then d12 (change p 204 none) else d1986 (change p 204 none)) = d5107 p
  rw [sub7260, sub7623]
  rfl
theorem sub7625 (p : Pattern) : d1988 (change p 204 none) = d5108 p := by
  change (if p 160 then d1987 (change p 204 none) else d1984 (change p 204 none)) = d5108 p
  rw [sub7624, sub7621]
  rfl
theorem sub7626 (p : Pattern) : d1989 (change p 204 none) = d5109 p := by
  change (if p 141 then d1988 (change p 204 none) else d1978 (change p 204 none)) = d5109 p
  rw [sub7625, sub7615]
  rfl
theorem sub7627 (p : Pattern) : d1990 (change p 204 none) = d5110 p := by
  change (if p 138 then d1989 (change p 204 none) else d1938 (change p 204 none)) = d5110 p
  rw [sub7626, sub7573]
  rfl
theorem sub7628 (p : Pattern) : d1991 (change p 204 none) = d5111 p := by
  change (if p 162 then d12 (change p 204 none) else d1888 (change p 204 none)) = d5111 p
  rw [sub7260, sub7518]
  rfl
theorem sub7629 (p : Pattern) : d1992 (change p 204 none) = d5112 p := by
  change (if p 161 then d12 (change p 204 none) else d1991 (change p 204 none)) = d5112 p
  rw [sub7260, sub7628]
  rfl
theorem sub7630 (p : Pattern) : d1993 (change p 204 none) = d5113 p := by
  change (if p 160 then d12 (change p 204 none) else d1992 (change p 204 none)) = d5113 p
  rw [sub7260, sub7629]
  rfl
theorem sub7631 (p : Pattern) : d1994 (change p 204 none) = d5114 p := by
  change (if p 141 then d12 (change p 204 none) else d1993 (change p 204 none)) = d5114 p
  rw [sub7260, sub7630]
  rfl
theorem sub7632 (p : Pattern) : d1995 (change p 204 none) = d5115 p := by
  change (if p 138 then d1994 (change p 204 none) else d1989 (change p 204 none)) = d5115 p
  rw [sub7631, sub7626]
  rfl
theorem sub7633 (p : Pattern) : d1996 (change p 204 none) = d5116 p := by
  change (if p 116 then d1995 (change p 204 none) else d1990 (change p 204 none)) = d5116 p
  rw [sub7632, sub7627]
  rfl
theorem sub7634 (p : Pattern) : d1997 (change p 204 none) = d5062 p := by
  change (if p 162 then d1886 (change p 204 none) else d1878 (change p 204 none)) = d5062 p
  rw [sub7516, sub7502]
  rfl
theorem sub7635 (p : Pattern) : d1998 (change p 204 none) = d5065 p := by
  change (if p 161 then d1889 (change p 204 none) else d1997 (change p 204 none)) = d5065 p
  rw [sub7519, sub7634]
  rfl
theorem sub7636 (p : Pattern) : d1999 (change p 204 none) = d5071 p := by
  change (if p 160 then d1914 (change p 204 none) else d1998 (change p 204 none)) = d5071 p
  rw [sub7548, sub7635]
  rfl
theorem sub7637 (p : Pattern) : d2000 (change p 204 none) = d5073 p := by
  change (if p 163 then d1923 (change p 204 none) else d1878 (change p 204 none)) = d5073 p
  rw [sub7558, sub7502]
  rfl
theorem sub7638 (p : Pattern) : d2001 (change p 204 none) = d5075 p := by
  change (if p 162 then d1925 (change p 204 none) else d2000 (change p 204 none)) = d5075 p
  rw [sub7560, sub7637]
  rfl
theorem sub7639 (p : Pattern) : d2002 (change p 204 none) = d5078 p := by
  change (if p 161 then d1928 (change p 204 none) else d2001 (change p 204 none)) = d5078 p
  rw [sub7563, sub7638]
  rfl
theorem sub7640 (p : Pattern) : d2003 (change p 204 none) = d5082 p := by
  change (if p 160 then d1936 (change p 204 none) else d2002 (change p 204 none)) = d5082 p
  rw [sub7571, sub7639]
  rfl
theorem sub7641 (p : Pattern) : d2004 (change p 204 none) = d5083 p := by
  change (if p 141 then d2003 (change p 204 none) else d1999 (change p 204 none)) = d5083 p
  rw [sub7640, sub7636]
  rfl
theorem sub7642 (p : Pattern) : d2005 (change p 204 none) = d5110 p := by
  change (if p 138 then d1989 (change p 204 none) else d2004 (change p 204 none)) = d5110 p
  rw [sub7626, sub7641]
  rfl
theorem sub7643 (p : Pattern) : d2006 (change p 204 none) = d5117 p := by
  change (if p 138 then d12 (change p 204 none) else d1989 (change p 204 none)) = d5117 p
  rw [sub7260, sub7626]
  rfl
theorem sub7644 (p : Pattern) : d2007 (change p 204 none) = d5118 p := by
  change (if p 116 then d2006 (change p 204 none) else d2005 (change p 204 none)) = d5118 p
  rw [sub7643, sub7642]
  rfl
theorem sub7645 (p : Pattern) : d2008 (change p 204 none) = d5119 p := by
  change (if p 115 then d2007 (change p 204 none) else d1996 (change p 204 none)) = d5119 p
  rw [sub7644, sub7633]
  rfl
theorem sub7646 (p : Pattern) : d2009 (change p 204 none) = d5120 p := by
  change (if p 71 then d2008 (change p 204 none) else d1849 (change p 204 none)) = d5120 p
  rw [sub7645, sub7467]
  rfl
theorem sub7647 (p : Pattern) : d2010 (change p 204 none) = d5121 p := by
  change (if p 49 then d2009 (change p 204 none) else d1870 (change p 204 none)) = d5121 p
  rw [sub7646, sub7488]
  rfl
theorem sub7648 (p : Pattern) : d2011 (change p 204 none) = d2011 p := by
  change (if p 225 then d1795 (change p 204 none) else d18 (change p 204 none)) = d2011 p
  rw [sub7410, sub7279]
  rfl
theorem sub7649 (p : Pattern) : d2012 (change p 204 none) = d2012 p := by
  change (if p 224 then d1795 (change p 204 none) else d2011 (change p 204 none)) = d2012 p
  rw [sub7410, sub7648]
  rfl
theorem sub7650 (p : Pattern) : d2013 (change p 204 none) = d2012 p := by
  change d2012 (change p 204 none) = d2012 p
  exact sub7649 p
theorem sub7651 (p : Pattern) : d2014 (change p 204 none) = d5122 p := by
  change (if p 182 then d2013 (change p 204 none) else d19 (change p 204 none)) = d5122 p
  rw [sub7650, sub7280]
  rfl
theorem sub7652 (p : Pattern) : d2015 (change p 204 none) = d5123 p := by
  change (if p 163 then d2014 (change p 204 none) else d1774 (change p 204 none)) = d5123 p
  rw [sub7651, sub7389]
  rfl
theorem sub7653 (p : Pattern) : d2016 (change p 204 none) = d5124 p := by
  change (if p 162 then d2015 (change p 204 none) else d1774 (change p 204 none)) = d5124 p
  rw [sub7652, sub7389]
  rfl
theorem sub7654 (p : Pattern) : d2017 (change p 204 none) = d5125 p := by
  change (if p 162 then d1806 (change p 204 none) else d2015 (change p 204 none)) = d5125 p
  rw [sub7423, sub7652]
  rfl
theorem sub7655 (p : Pattern) : d2018 (change p 204 none) = d5126 p := by
  change (if p 161 then d2017 (change p 204 none) else d2016 (change p 204 none)) = d5126 p
  rw [sub7654, sub7653]
  rfl
theorem sub7656 (p : Pattern) : d2019 (change p 204 none) = d5127 p := by
  change (if p 182 then d1725 (change p 204 none) else d32 (change p 204 none)) = d5127 p
  rw [sub7328, sub7349]
  rfl
theorem sub7657 (p : Pattern) : d2020 (change p 204 none) = d5128 p := by
  change (if p 163 then d2019 (change p 204 none) else d1809 (change p 204 none)) = d5128 p
  rw [sub7656, sub7426]
  rfl
theorem sub7658 (p : Pattern) : d2021 (change p 204 none) = d5129 p := by
  change (if p 182 then d1730 (change p 204 none) else d32 (change p 204 none)) = d5129 p
  rw [sub7335, sub7349]
  rfl
theorem sub7659 (p : Pattern) : d2022 (change p 204 none) = d173 p := by
  change (if p 182 then d12 (change p 204 none) else d36 (change p 204 none)) = d173 p
  rw [sub7260, sub7427]
  rfl
theorem sub7660 (p : Pattern) : d2023 (change p 204 none) = d5130 p := by
  change (if p 163 then d2022 (change p 204 none) else d2021 (change p 204 none)) = d5130 p
  rw [sub7659, sub7658]
  rfl
theorem sub7661 (p : Pattern) : d2024 (change p 204 none) = d5131 p := by
  change (if p 162 then d2023 (change p 204 none) else d2020 (change p 204 none)) = d5131 p
  rw [sub7660, sub7657]
  rfl
theorem sub7662 (p : Pattern) : d2025 (change p 204 none) = d176 p := by
  change (if p 163 then d2022 (change p 204 none) else d1760 (change p 204 none)) = d176 p
  rw [sub7659, sub7372]
  rfl
theorem sub7663 (p : Pattern) : d2026 (change p 204 none) = d177 p := by
  change (if p 162 then d539 (change p 204 none) else d2025 (change p 204 none)) = d177 p
  rw [sub7379, sub7662]
  rfl
theorem sub7664 (p : Pattern) : d2027 (change p 204 none) = d5132 p := by
  change (if p 161 then d2026 (change p 204 none) else d2024 (change p 204 none)) = d5132 p
  rw [sub7663, sub7661]
  rfl
theorem sub7665 (p : Pattern) : d2028 (change p 204 none) = d5133 p := by
  change (if p 160 then d2027 (change p 204 none) else d2018 (change p 204 none)) = d5133 p
  rw [sub7664, sub7655]
  rfl
theorem sub7666 (p : Pattern) : d2029 (change p 204 none) = d2029 p := by
  change (if p 225 then d1714 (change p 204 none) else d31 (change p 204 none)) = d2029 p
  rw [sub7313, sub7306]
  rfl
theorem sub7667 (p : Pattern) : d2030 (change p 204 none) = d2030 p := by
  change (if p 224 then d1714 (change p 204 none) else d2029 (change p 204 none)) = d2030 p
  rw [sub7313, sub7666]
  rfl
theorem sub7668 (p : Pattern) : d2031 (change p 204 none) = d2030 p := by
  change d2030 (change p 204 none) = d2030 p
  exact sub7667 p
theorem sub7669 (p : Pattern) : d2032 (change p 204 none) = d5134 p := by
  change (if p 182 then d2031 (change p 204 none) else d32 (change p 204 none)) = d5134 p
  rw [sub7668, sub7349]
  rfl
theorem sub7670 (p : Pattern) : d2033 (change p 204 none) = d5135 p := by
  change (if p 163 then d2032 (change p 204 none) else d1774 (change p 204 none)) = d5135 p
  rw [sub7669, sub7389]
  rfl
theorem sub7671 (p : Pattern) : d2034 (change p 204 none) = d5136 p := by
  change (if p 163 then d1805 (change p 204 none) else d2014 (change p 204 none)) = d5136 p
  rw [sub7422, sub7651]
  rfl
theorem sub7672 (p : Pattern) : d2035 (change p 204 none) = d5137 p := by
  change (if p 162 then d2034 (change p 204 none) else d2033 (change p 204 none)) = d5137 p
  rw [sub7671, sub7670]
  rfl
theorem sub7673 (p : Pattern) : d2036 (change p 204 none) = d5138 p := by
  change (if p 163 then d1754 (change p 204 none) else d2014 (change p 204 none)) = d5138 p
  rw [sub7365, sub7651]
  rfl
theorem sub7674 (p : Pattern) : d2037 (change p 204 none) = d5139 p := by
  change (if p 162 then d1757 (change p 204 none) else d2036 (change p 204 none)) = d5139 p
  rw [sub7369, sub7673]
  rfl
theorem sub7675 (p : Pattern) : d2038 (change p 204 none) = d5140 p := by
  change (if p 161 then d2037 (change p 204 none) else d2035 (change p 204 none)) = d5140 p
  rw [sub7674, sub7672]
  rfl
theorem sub7676 (p : Pattern) : d2039 (change p 204 none) = d5141 p := by
  change (if p 163 then d1732 (change p 204 none) else d2019 (change p 204 none)) = d5141 p
  rw [sub7337, sub7656]
  rfl
theorem sub7677 (p : Pattern) : d2040 (change p 204 none) = d181 p := by
  change (if p 163 then d538 (change p 204 none) else d2022 (change p 204 none)) = d181 p
  rw [sub7378, sub7659]
  rfl
theorem sub7678 (p : Pattern) : d2041 (change p 204 none) = d5142 p := by
  change (if p 162 then d2040 (change p 204 none) else d2039 (change p 204 none)) = d5142 p
  rw [sub7677, sub7676]
  rfl
theorem sub7679 (p : Pattern) : d2042 (change p 204 none) = d183 p := by
  change (if p 163 then d12 (change p 204 none) else d2022 (change p 204 none)) = d183 p
  rw [sub7260, sub7659]
  rfl
end NetHack.Sokoban22Refined85
