/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions88
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub10680 (p : Pattern) : d1906 (change p 204 (some 182)) = d1905 p := by
  change d1905 (change p 204 (some 182)) = d1905 p
  exact sub10679 p
theorem sub10681 (p : Pattern) : d1907 (change p 204 (some 182)) = d1905 p := by
  change d1906 (change p 204 (some 182)) = d1905 p
  exact sub10680 p
theorem sub10682 (p : Pattern) : d1908 (change p 204 (some 182)) = d5911 p := by
  change (if p 163 then d1907 (change p 204 (some 182)) else d1900 (change p 204 (some 182))) = d5911 p
  rw [sub10681, sub10672]
  rfl
theorem sub10683 (p : Pattern) : d1909 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10684 (p : Pattern) : d1910 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10685 (p : Pattern) : d1911 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d1910 (change p 204 (some 182)) else d1909 (change p 204 (some 182))) = d12 p
  rw [sub10684, sub10683]
  simp only [ite_self]
theorem sub10686 (p : Pattern) : d1912 (change p 204 (some 182)) = d5912 p := by
  change (if p 162 then d1911 (change p 204 (some 182)) else d1908 (change p 204 (some 182))) = d5912 p
  rw [sub10685, sub10682]
  rfl
theorem sub10687 (p : Pattern) : d278 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d277 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10522]
  simp only [ite_self]
theorem sub10688 (p : Pattern) : d1913 (change p 204 (some 182)) = d12 p := by
  change (if p 162 then d278 (change p 204 (some 182)) else d1911 (change p 204 (some 182))) = d12 p
  rw [sub10687, sub10685]
  simp only [ite_self]
theorem sub10689 (p : Pattern) : d1914 (change p 204 (some 182)) = d5913 p := by
  change (if p 161 then d1913 (change p 204 (some 182)) else d1912 (change p 204 (some 182))) = d5913 p
  rw [sub10688, sub10686]
  rfl
theorem sub10690 (p : Pattern) : d1915 (change p 204 (some 182)) = d5914 p := by
  change (if p 160 then d1914 (change p 204 (some 182)) else d1890 (change p 204 (some 182))) = d5914 p
  rw [sub10689, sub10661]
  rfl
theorem sub10691 (p : Pattern) : d1917 (change p 204 (some 182)) = d1875 p := by
  change d1876 (change p 204 (some 182)) = d1875 p
  exact sub10642 p
theorem sub10692 (p : Pattern) : d1918 (change p 204 (some 182)) = d1918 p := by
  change (if p 247 then d5 (change p 204 (some 182)) else d3 (change p 204 (some 182))) = d1918 p
  rw [sub10646, sub10636]
  rfl
theorem sub10693 (p : Pattern) : d1919 (change p 204 (some 182)) = d1919 p := by
  change (if p 246 then d106 (change p 204 (some 182)) else d1918 (change p 204 (some 182))) = d1919 p
  rw [sub10647, sub10692]
  rfl
theorem sub10694 (p : Pattern) : d1920 (change p 204 (some 182)) = d1920 p := by
  change (if p 225 then d1919 (change p 204 (some 182)) else d116 (change p 204 (some 182))) = d1920 p
  rw [sub10693, sub10662]
  rfl
theorem sub10695 (p : Pattern) : d1921 (change p 204 (some 182)) = d1921 p := by
  change (if p 224 then d1919 (change p 204 (some 182)) else d1920 (change p 204 (some 182))) = d1921 p
  rw [sub10693, sub10694]
  rfl
theorem sub10696 (p : Pattern) : d1922 (change p 204 (some 182)) = d1921 p := by
  change d1921 (change p 204 (some 182)) = d1921 p
  exact sub10695 p
theorem sub10697 (p : Pattern) : d1923 (change p 204 (some 182)) = d1921 p := by
  change d1922 (change p 204 (some 182)) = d1921 p
  exact sub10696 p
theorem sub10698 (p : Pattern) : d1924 (change p 204 (some 182)) = d5915 p := by
  change (if p 163 then d1923 (change p 204 (some 182)) else d1917 (change p 204 (some 182))) = d5915 p
  rw [sub10697, sub10691]
  rfl
theorem sub10699 (p : Pattern) : d1925 (change p 204 (some 182)) = d5916 p := by
  change (if p 163 then d1754 (change p 204 (some 182)) else d1885 (change p 204 (some 182))) = d5916 p
  rw [sub10512, sub10656]
  rfl
theorem sub10700 (p : Pattern) : d1926 (change p 204 (some 182)) = d5917 p := by
  change (if p 162 then d1925 (change p 204 (some 182)) else d1924 (change p 204 (some 182))) = d5917 p
  rw [sub10699, sub10698]
  rfl
theorem sub10701 (p : Pattern) : d1927 (change p 204 (some 182)) = d5918 p := by
  change (if p 163 then d1756 (change p 204 (some 182)) else d1885 (change p 204 (some 182))) = d5918 p
  rw [sub10514, sub10656]
  rfl
theorem sub10702 (p : Pattern) : d1928 (change p 204 (some 182)) = d5919 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d1927 (change p 204 (some 182))) = d5919 p
  rw [sub10415, sub10701]
  rfl
theorem sub10703 (p : Pattern) : d1929 (change p 204 (some 182)) = d5920 p := by
  change (if p 161 then d1928 (change p 204 (some 182)) else d1926 (change p 204 (some 182))) = d5920 p
  rw [sub10702, sub10700]
  rfl
theorem sub10704 (p : Pattern) : d1930 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10705 (p : Pattern) : d1931 (change p 204 (some 182)) = d5921 p := by
  change (if p 163 then d1930 (change p 204 (some 182)) else d1907 (change p 204 (some 182))) = d5921 p
  rw [sub10704, sub10681]
  rfl
theorem sub10706 (p : Pattern) : d1932 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d277 (change p 204 (some 182)) else d1910 (change p 204 (some 182))) = d12 p
  rw [sub10522, sub10684]
  simp only [ite_self]
theorem sub10707 (p : Pattern) : d1933 (change p 204 (some 182)) = d5922 p := by
  change (if p 162 then d1932 (change p 204 (some 182)) else d1931 (change p 204 (some 182))) = d5922 p
  rw [sub10706, sub10705]
  rfl
theorem sub10708 (p : Pattern) : d1934 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d538 (change p 204 (some 182)) else d1910 (change p 204 (some 182))) = d12 p
  rw [sub10524, sub10684]
  simp only [ite_self]
theorem sub10709 (p : Pattern) : d1935 (change p 204 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d1934 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10708]
  simp only [ite_self]
theorem sub10710 (p : Pattern) : d1936 (change p 204 (some 182)) = d5923 p := by
  change (if p 161 then d1935 (change p 204 (some 182)) else d1933 (change p 204 (some 182))) = d5923 p
  rw [sub10709, sub10707]
  rfl
theorem sub10711 (p : Pattern) : d1937 (change p 204 (some 182)) = d5924 p := by
  change (if p 160 then d1936 (change p 204 (some 182)) else d1929 (change p 204 (some 182))) = d5924 p
  rw [sub10710, sub10703]
  rfl
theorem sub10712 (p : Pattern) : d1938 (change p 204 (some 182)) = d5925 p := by
  change (if p 141 then d1937 (change p 204 (some 182)) else d1915 (change p 204 (some 182))) = d5925 p
  rw [sub10711, sub10690]
  rfl
theorem sub10713 (p : Pattern) : d1939 (change p 204 (some 182)) = d1939 p := by
  change (if p 247 then d5 (change p 204 (some 182)) else d1 (change p 204 (some 182))) = d1939 p
  rw [sub10646, sub10633]
  rfl
theorem sub10714 (p : Pattern) : d1940 (change p 204 (some 182)) = d1940 p := by
  change (if p 246 then d106 (change p 204 (some 182)) else d1939 (change p 204 (some 182))) = d1940 p
  rw [sub10647, sub10713]
  rfl
theorem sub10715 (p : Pattern) : d1941 (change p 204 (some 182)) = d1941 p := by
  change (if p 225 then d1940 (change p 204 (some 182)) else d103 (change p 204 (some 182))) = d1941 p
  rw [sub10714, sub10635]
  rfl
theorem sub10716 (p : Pattern) : d1942 (change p 204 (some 182)) = d1942 p := by
  change (if p 224 then d1940 (change p 204 (some 182)) else d1941 (change p 204 (some 182))) = d1942 p
  rw [sub10714, sub10715]
  rfl
theorem sub10717 (p : Pattern) : d1943 (change p 204 (some 182)) = d1942 p := by
  change d1942 (change p 204 (some 182)) = d1942 p
  exact sub10716 p
theorem sub10718 (p : Pattern) : d1944 (change p 204 (some 182)) = d1942 p := by
  change d1943 (change p 204 (some 182)) = d1942 p
  exact sub10717 p
theorem sub10719 (p : Pattern) : d1945 (change p 204 (some 182)) = d1945 p := by
  change (if p 247 then d7 (change p 204 (some 182)) else d1 (change p 204 (some 182))) = d1945 p
  rw [sub10649, sub10633]
  rfl
theorem sub10720 (p : Pattern) : d1946 (change p 204 (some 182)) = d1946 p := by
  change (if p 246 then d119 (change p 204 (some 182)) else d1945 (change p 204 (some 182))) = d1946 p
  rw [sub10651, sub10719]
  rfl
theorem sub10721 (p : Pattern) : d1947 (change p 204 (some 182)) = d1947 p := by
  change (if p 225 then d1946 (change p 204 (some 182)) else d103 (change p 204 (some 182))) = d1947 p
  rw [sub10720, sub10635]
  rfl
theorem sub10722 (p : Pattern) : d1948 (change p 204 (some 182)) = d1948 p := by
  change (if p 247 then d9 (change p 204 (some 182)) else d1 (change p 204 (some 182))) = d1948 p
  rw [sub10442, sub10633]
  rfl
theorem sub10723 (p : Pattern) : d1949 (change p 204 (some 182)) = d1949 p := by
  change (if p 246 then d23 (change p 204 (some 182)) else d1948 (change p 204 (some 182))) = d1949 p
  rw [sub10443, sub10722]
  rfl
theorem sub10724 (p : Pattern) : d1950 (change p 204 (some 182)) = d1950 p := by
  change (if p 225 then d1949 (change p 204 (some 182)) else d1940 (change p 204 (some 182))) = d1950 p
  rw [sub10723, sub10714]
  rfl
theorem sub10725 (p : Pattern) : d1951 (change p 204 (some 182)) = d1951 p := by
  change (if p 224 then d1950 (change p 204 (some 182)) else d1947 (change p 204 (some 182))) = d1951 p
  rw [sub10724, sub10721]
  rfl
theorem sub10726 (p : Pattern) : d1952 (change p 204 (some 182)) = d1951 p := by
  change d1951 (change p 204 (some 182)) = d1951 p
  exact sub10725 p
theorem sub10727 (p : Pattern) : d1953 (change p 204 (some 182)) = d1951 p := by
  change d1952 (change p 204 (some 182)) = d1951 p
  exact sub10726 p
theorem sub10728 (p : Pattern) : d1954 (change p 204 (some 182)) = d5926 p := by
  change (if p 163 then d1953 (change p 204 (some 182)) else d1944 (change p 204 (some 182))) = d5926 p
  rw [sub10727, sub10718]
  rfl
theorem sub10729 (p : Pattern) : d1955 (change p 204 (some 182)) = d1955 p := by
  change (if p 246 then d57 (change p 204 (some 182)) else d102 (change p 204 (some 182))) = d1955 p
  rw [sub10474, sub10634]
  rfl
theorem sub10730 (p : Pattern) : d1956 (change p 204 (some 182)) = d1956 p := by
  change (if p 225 then d1955 (change p 204 (some 182)) else d1940 (change p 204 (some 182))) = d1956 p
  rw [sub10729, sub10714]
  rfl
theorem sub10731 (p : Pattern) : d1957 (change p 204 (some 182)) = d1957 p := by
  change (if p 224 then d1956 (change p 204 (some 182)) else d1947 (change p 204 (some 182))) = d1957 p
  rw [sub10730, sub10721]
  rfl
theorem sub10732 (p : Pattern) : d1958 (change p 204 (some 182)) = d1957 p := by
  change d1957 (change p 204 (some 182)) = d1957 p
  exact sub10731 p
theorem sub10733 (p : Pattern) : d1959 (change p 204 (some 182)) = d1957 p := by
  change d1958 (change p 204 (some 182)) = d1957 p
  exact sub10732 p
theorem sub10734 (p : Pattern) : d1960 (change p 204 (some 182)) = d1960 p := by
  change (if p 247 then d11 (change p 204 (some 182)) else d5 (change p 204 (some 182))) = d1960 p
  rw [sub10445, sub10646]
  rfl
theorem sub10735 (p : Pattern) : d1961 (change p 204 (some 182)) = d1961 p := by
  change (if p 246 then d39 (change p 204 (some 182)) else d1960 (change p 204 (some 182))) = d1961 p
  rw [sub10447, sub10734]
  rfl
theorem sub10736 (p : Pattern) : d1962 (change p 204 (some 182)) = d1962 p := by
  change (if p 225 then d1961 (change p 204 (some 182)) else d107 (change p 204 (some 182))) = d1962 p
  rw [sub10735, sub10648]
  rfl
theorem sub10737 (p : Pattern) : d1963 (change p 204 (some 182)) = d1963 p := by
  change (if p 247 then d9 (change p 204 (some 182)) else d5 (change p 204 (some 182))) = d1963 p
  rw [sub10442, sub10646]
  rfl
theorem sub10738 (p : Pattern) : d1964 (change p 204 (some 182)) = d1964 p := by
  change (if p 246 then d23 (change p 204 (some 182)) else d1963 (change p 204 (some 182))) = d1964 p
  rw [sub10443, sub10737]
  rfl
theorem sub10739 (p : Pattern) : d348 (change p 204 (some 182)) = d348 p := by
  change (if p 246 then d12 (change p 204 (some 182)) else d106 (change p 204 (some 182))) = d348 p
  rw [sub10415, sub10647]
  rfl
theorem sub10740 (p : Pattern) : d1965 (change p 204 (some 182)) = d1965 p := by
  change (if p 225 then d348 (change p 204 (some 182)) else d1964 (change p 204 (some 182))) = d1965 p
  rw [sub10739, sub10738]
  rfl
theorem sub10741 (p : Pattern) : d1966 (change p 204 (some 182)) = d1966 p := by
  change (if p 224 then d1965 (change p 204 (some 182)) else d1962 (change p 204 (some 182))) = d1966 p
  rw [sub10740, sub10736]
  rfl
theorem sub10742 (p : Pattern) : d1967 (change p 204 (some 182)) = d1966 p := by
  change d1966 (change p 204 (some 182)) = d1966 p
  exact sub10741 p
theorem sub10743 (p : Pattern) : d1968 (change p 204 (some 182)) = d1966 p := by
  change d1967 (change p 204 (some 182)) = d1966 p
  exact sub10742 p
theorem sub10744 (p : Pattern) : d1969 (change p 204 (some 182)) = d5927 p := by
  change (if p 163 then d1968 (change p 204 (some 182)) else d1959 (change p 204 (some 182))) = d5927 p
  rw [sub10743, sub10733]
  rfl
theorem sub10745 (p : Pattern) : d1970 (change p 204 (some 182)) = d5928 p := by
  change (if p 162 then d1969 (change p 204 (some 182)) else d1954 (change p 204 (some 182))) = d5928 p
  rw [sub10744, sub10728]
  rfl
theorem sub10746 (p : Pattern) : d1971 (change p 204 (some 182)) = d5929 p := by
  change (if p 162 then d1888 (change p 204 (some 182)) else d1969 (change p 204 (some 182))) = d5929 p
  rw [sub10659, sub10744]
  rfl
theorem sub10747 (p : Pattern) : d1972 (change p 204 (some 182)) = d5930 p := by
  change (if p 161 then d1971 (change p 204 (some 182)) else d1970 (change p 204 (some 182))) = d5930 p
  rw [sub10746, sub10745]
  rfl
theorem sub10748 (p : Pattern) : d1973 (change p 204 (some 182)) = d1898 p := by
  change d1899 (change p 204 (some 182)) = d1898 p
  exact sub10671 p
theorem sub10749 (p : Pattern) : d1974 (change p 204 (some 182)) = d1905 p := by
  change d1906 (change p 204 (some 182)) = d1905 p
  exact sub10680 p
theorem sub10750 (p : Pattern) : d1975 (change p 204 (some 182)) = d5911 p := by
  change (if p 163 then d1974 (change p 204 (some 182)) else d1973 (change p 204 (some 182))) = d5911 p
  rw [sub10749, sub10748]
  rfl
theorem sub10751 (p : Pattern) : d1976 (change p 204 (some 182)) = d5912 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d1975 (change p 204 (some 182))) = d5912 p
  rw [sub10415, sub10750]
  rfl
theorem sub10752 (p : Pattern) : d1977 (change p 204 (some 182)) = d5913 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d1976 (change p 204 (some 182))) = d5913 p
  rw [sub10415, sub10751]
  rfl
theorem sub10753 (p : Pattern) : d1978 (change p 204 (some 182)) = d5931 p := by
  change (if p 160 then d1977 (change p 204 (some 182)) else d1972 (change p 204 (some 182))) = d5931 p
  rw [sub10752, sub10747]
  rfl
theorem sub10754 (p : Pattern) : d1979 (change p 204 (some 182)) = d5932 p := by
  change (if p 163 then d1973 (change p 204 (some 182)) else d1953 (change p 204 (some 182))) = d5932 p
  rw [sub10748, sub10727]
  rfl
theorem sub10755 (p : Pattern) : d1980 (change p 204 (some 182)) = d5933 p := by
  change (if p 163 then d1754 (change p 204 (some 182)) else d1968 (change p 204 (some 182))) = d5933 p
  rw [sub10512, sub10743]
  rfl
theorem sub10756 (p : Pattern) : d1981 (change p 204 (some 182)) = d5934 p := by
  change (if p 162 then d1980 (change p 204 (some 182)) else d1979 (change p 204 (some 182))) = d5934 p
  rw [sub10755, sub10754]
  rfl
theorem sub10757 (p : Pattern) : d1982 (change p 204 (some 182)) = d5935 p := by
  change (if p 163 then d1756 (change p 204 (some 182)) else d1968 (change p 204 (some 182))) = d5935 p
  rw [sub10514, sub10743]
  rfl
theorem sub10758 (p : Pattern) : d1983 (change p 204 (some 182)) = d5936 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d1982 (change p 204 (some 182))) = d5936 p
  rw [sub10415, sub10757]
  rfl
theorem sub10759 (p : Pattern) : d1984 (change p 204 (some 182)) = d5937 p := by
  change (if p 161 then d1983 (change p 204 (some 182)) else d1981 (change p 204 (some 182))) = d5937 p
  rw [sub10758, sub10756]
  rfl
theorem sub10760 (p : Pattern) : d1985 (change p 204 (some 182)) = d5921 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d1974 (change p 204 (some 182))) = d5921 p
  rw [sub10415, sub10749]
  rfl
theorem sub10761 (p : Pattern) : d1986 (change p 204 (some 182)) = d5922 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d1985 (change p 204 (some 182))) = d5922 p
  rw [sub10415, sub10760]
  rfl
theorem sub10762 (p : Pattern) : d1987 (change p 204 (some 182)) = d5923 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d1986 (change p 204 (some 182))) = d5923 p
  rw [sub10415, sub10761]
  rfl
theorem sub10763 (p : Pattern) : d1988 (change p 204 (some 182)) = d5938 p := by
  change (if p 160 then d1987 (change p 204 (some 182)) else d1984 (change p 204 (some 182))) = d5938 p
  rw [sub10762, sub10759]
  rfl
theorem sub10764 (p : Pattern) : d1989 (change p 204 (some 182)) = d5939 p := by
  change (if p 141 then d1988 (change p 204 (some 182)) else d1978 (change p 204 (some 182))) = d5939 p
  rw [sub10763, sub10753]
  rfl
theorem sub10765 (p : Pattern) : d1990 (change p 204 (some 182)) = d5940 p := by
  change (if p 138 then d1989 (change p 204 (some 182)) else d1938 (change p 204 (some 182))) = d5940 p
  rw [sub10764, sub10712]
  rfl
theorem sub10766 (p : Pattern) : d1991 (change p 204 (some 182)) = d5941 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d1888 (change p 204 (some 182))) = d5941 p
  rw [sub10415, sub10659]
  rfl
theorem sub10767 (p : Pattern) : d1992 (change p 204 (some 182)) = d5942 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d1991 (change p 204 (some 182))) = d5942 p
  rw [sub10415, sub10766]
  rfl
theorem sub10768 (p : Pattern) : d1993 (change p 204 (some 182)) = d5943 p := by
  change (if p 160 then d12 (change p 204 (some 182)) else d1992 (change p 204 (some 182))) = d5943 p
  rw [sub10415, sub10767]
  rfl
theorem sub10769 (p : Pattern) : d1994 (change p 204 (some 182)) = d5944 p := by
  change (if p 141 then d12 (change p 204 (some 182)) else d1993 (change p 204 (some 182))) = d5944 p
  rw [sub10415, sub10768]
  rfl
theorem sub10770 (p : Pattern) : d1995 (change p 204 (some 182)) = d5945 p := by
  change (if p 138 then d1994 (change p 204 (some 182)) else d1989 (change p 204 (some 182))) = d5945 p
  rw [sub10769, sub10764]
  rfl
theorem sub10771 (p : Pattern) : d1996 (change p 204 (some 182)) = d5946 p := by
  change (if p 116 then d1995 (change p 204 (some 182)) else d1990 (change p 204 (some 182))) = d5946 p
  rw [sub10770, sub10765]
  rfl
theorem sub10772 (p : Pattern) : d1997 (change p 204 (some 182)) = d5907 p := by
  change (if p 162 then d1886 (change p 204 (some 182)) else d1878 (change p 204 (some 182))) = d5907 p
  rw [sub10657, sub10644]
  rfl
theorem sub10773 (p : Pattern) : d1998 (change p 204 (some 182)) = d5910 p := by
  change (if p 161 then d1889 (change p 204 (some 182)) else d1997 (change p 204 (some 182))) = d5910 p
  rw [sub10660, sub10772]
  rfl
theorem sub10774 (p : Pattern) : d1999 (change p 204 (some 182)) = d5914 p := by
  change (if p 160 then d1914 (change p 204 (some 182)) else d1998 (change p 204 (some 182))) = d5914 p
  rw [sub10689, sub10773]
  rfl
theorem sub10775 (p : Pattern) : d2000 (change p 204 (some 182)) = d5915 p := by
  change (if p 163 then d1923 (change p 204 (some 182)) else d1878 (change p 204 (some 182))) = d5915 p
  rw [sub10697, sub10644]
  rfl
theorem sub10776 (p : Pattern) : d2001 (change p 204 (some 182)) = d5917 p := by
  change (if p 162 then d1925 (change p 204 (some 182)) else d2000 (change p 204 (some 182))) = d5917 p
  rw [sub10699, sub10775]
  rfl
theorem sub10777 (p : Pattern) : d2002 (change p 204 (some 182)) = d5920 p := by
  change (if p 161 then d1928 (change p 204 (some 182)) else d2001 (change p 204 (some 182))) = d5920 p
  rw [sub10702, sub10776]
  rfl
theorem sub10778 (p : Pattern) : d2003 (change p 204 (some 182)) = d5924 p := by
  change (if p 160 then d1936 (change p 204 (some 182)) else d2002 (change p 204 (some 182))) = d5924 p
  rw [sub10710, sub10777]
  rfl
theorem sub10779 (p : Pattern) : d2004 (change p 204 (some 182)) = d5925 p := by
  change (if p 141 then d2003 (change p 204 (some 182)) else d1999 (change p 204 (some 182))) = d5925 p
  rw [sub10778, sub10774]
  rfl
theorem sub10780 (p : Pattern) : d2005 (change p 204 (some 182)) = d5940 p := by
  change (if p 138 then d1989 (change p 204 (some 182)) else d2004 (change p 204 (some 182))) = d5940 p
  rw [sub10764, sub10779]
  rfl
theorem sub10781 (p : Pattern) : d2006 (change p 204 (some 182)) = d5947 p := by
  change (if p 138 then d12 (change p 204 (some 182)) else d1989 (change p 204 (some 182))) = d5947 p
  rw [sub10415, sub10764]
  rfl
theorem sub10782 (p : Pattern) : d2007 (change p 204 (some 182)) = d5948 p := by
  change (if p 116 then d2006 (change p 204 (some 182)) else d2005 (change p 204 (some 182))) = d5948 p
  rw [sub10781, sub10780]
  rfl
theorem sub10783 (p : Pattern) : d2008 (change p 204 (some 182)) = d5949 p := by
  change (if p 115 then d2007 (change p 204 (some 182)) else d1996 (change p 204 (some 182))) = d5949 p
  rw [sub10782, sub10771]
  rfl
theorem sub10784 (p : Pattern) : d2009 (change p 204 (some 182)) = d5950 p := by
  change (if p 71 then d2008 (change p 204 (some 182)) else d1849 (change p 204 (some 182))) = d5950 p
  rw [sub10783, sub10612]
  rfl
theorem sub10785 (p : Pattern) : d2010 (change p 204 (some 182)) = d5951 p := by
  change (if p 49 then d2009 (change p 204 (some 182)) else d1870 (change p 204 (some 182))) = d5951 p
  rw [sub10784, sub10632]
  rfl
theorem sub10786 (p : Pattern) : d2011 (change p 204 (some 182)) = d2011 p := by
  change (if p 225 then d1795 (change p 204 (some 182)) else d18 (change p 204 (some 182))) = d2011 p
  rw [sub10556, sub10431]
  rfl
theorem sub10787 (p : Pattern) : d2012 (change p 204 (some 182)) = d2012 p := by
  change (if p 224 then d1795 (change p 204 (some 182)) else d2011 (change p 204 (some 182))) = d2012 p
  rw [sub10556, sub10786]
  rfl
theorem sub10788 (p : Pattern) : d2013 (change p 204 (some 182)) = d2012 p := by
  change d2012 (change p 204 (some 182)) = d2012 p
  exact sub10787 p
theorem sub10789 (p : Pattern) : d2014 (change p 204 (some 182)) = d2012 p := by
  change d2013 (change p 204 (some 182)) = d2012 p
  exact sub10788 p
theorem sub10790 (p : Pattern) : d2015 (change p 204 (some 182)) = d5952 p := by
  change (if p 163 then d2014 (change p 204 (some 182)) else d1774 (change p 204 (some 182))) = d5952 p
  rw [sub10789, sub10535]
  rfl
theorem sub10791 (p : Pattern) : d2016 (change p 204 (some 182)) = d5953 p := by
  change (if p 162 then d2015 (change p 204 (some 182)) else d1774 (change p 204 (some 182))) = d5953 p
  rw [sub10790, sub10535]
  rfl
theorem sub10792 (p : Pattern) : d2017 (change p 204 (some 182)) = d5954 p := by
  change (if p 162 then d1806 (change p 204 (some 182)) else d2015 (change p 204 (some 182))) = d5954 p
  rw [sub10569, sub10790]
  rfl
theorem sub10793 (p : Pattern) : d2018 (change p 204 (some 182)) = d5955 p := by
  change (if p 161 then d2017 (change p 204 (some 182)) else d2016 (change p 204 (some 182))) = d5955 p
  rw [sub10792, sub10791]
  rfl
theorem sub10794 (p : Pattern) : d2019 (change p 204 (some 182)) = d1724 p := by
  change d1725 (change p 204 (some 182)) = d1724 p
  exact sub10478 p
theorem sub10795 (p : Pattern) : d2020 (change p 204 (some 182)) = d5861 p := by
  change (if p 163 then d2019 (change p 204 (some 182)) else d1809 (change p 204 (some 182))) = d5861 p
  rw [sub10794, sub10572]
  rfl
theorem sub10796 (p : Pattern) : d2021 (change p 204 (some 182)) = d1729 p := by
  change d1730 (change p 204 (some 182)) = d1729 p
  exact sub10485 p
theorem sub10797 (p : Pattern) : d2022 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10798 (p : Pattern) : d2023 (change p 204 (some 182)) = d5862 p := by
  change (if p 163 then d2022 (change p 204 (some 182)) else d2021 (change p 204 (some 182))) = d5862 p
  rw [sub10797, sub10796]
  rfl
theorem sub10799 (p : Pattern) : d2024 (change p 204 (some 182)) = d5863 p := by
  change (if p 162 then d2023 (change p 204 (some 182)) else d2020 (change p 204 (some 182))) = d5863 p
  rw [sub10798, sub10795]
  rfl
end NetHack.Sokoban22Refined85
