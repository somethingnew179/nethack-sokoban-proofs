/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1920 (p : Pattern) : Int := if p 133 then d1919 p else d1907 p
theorem agree1920 (p q : Pattern) (h : Agree support p q) : d1920 p = d1920 q := by
  simp only [d1920, h 133 (by decide), agree1919 p q h, agree1907 p q h]
theorem nonnegative1920 (p : Pattern) : 0 ≤ d1920 p :=
  nonnegative_ite (p 133) (nonnegative1919 p) (nonnegative1907 p)
def d1921 (p : Pattern) : Int := if p 133 then d2 p else d1919 p
theorem agree1921 (p q : Pattern) (h : Agree support p q) : d1921 p = d1921 q := by
  simp only [d1921, h 133 (by decide), agree2 p q h, agree1919 p q h]
theorem nonnegative1921 (p : Pattern) : 0 ≤ d1921 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative1919 p)
def d1922 (p : Pattern) : Int := if p 132 then d1921 p else d1920 p
theorem agree1922 (p q : Pattern) (h : Agree support p q) : d1922 p = d1922 q := by
  simp only [d1922, h 132 (by decide), agree1921 p q h, agree1920 p q h]
theorem nonnegative1922 (p : Pattern) : 0 ≤ d1922 p :=
  nonnegative_ite (p 132) (nonnegative1921 p) (nonnegative1920 p)
def d1923 (p : Pattern) : Int := if p 113 then d1922 p else d1918 p
theorem agree1923 (p q : Pattern) (h : Agree support p q) : d1923 p = d1923 q := by
  simp only [d1923, h 113 (by decide), agree1922 p q h, agree1918 p q h]
theorem nonnegative1923 (p : Pattern) : 0 ≤ d1923 p :=
  nonnegative_ite (p 113) (nonnegative1922 p) (nonnegative1918 p)
def d1924 (p : Pattern) : Int := if p 112 then d1923 p else d1916 p
theorem agree1924 (p q : Pattern) (h : Agree support p q) : d1924 p = d1924 q := by
  simp only [d1924, h 112 (by decide), agree1923 p q h, agree1916 p q h]
theorem nonnegative1924 (p : Pattern) : 0 ≤ d1924 p :=
  nonnegative_ite (p 112) (nonnegative1923 p) (nonnegative1916 p)
def d1925 (p : Pattern) : Int := if p 106 then d1924 p else d1913 p
theorem agree1925 (p q : Pattern) (h : Agree support p q) : d1925 p = d1925 q := by
  simp only [d1925, h 106 (by decide), agree1924 p q h, agree1913 p q h]
theorem nonnegative1925 (p : Pattern) : 0 ≤ d1925 p :=
  nonnegative_ite (p 106) (nonnegative1924 p) (nonnegative1913 p)
def d1926 (p : Pattern) : Int := if p 86 then d1925 p else d1899 p
theorem agree1926 (p q : Pattern) (h : Agree support p q) : d1926 p = d1926 q := by
  simp only [d1926, h 86 (by decide), agree1925 p q h, agree1899 p q h]
theorem nonnegative1926 (p : Pattern) : 0 ≤ d1926 p :=
  nonnegative_ite (p 86) (nonnegative1925 p) (nonnegative1899 p)
def d1927 (p : Pattern) : Int := if p 112 then d1897 p else d1891 p
theorem agree1927 (p q : Pattern) (h : Agree support p q) : d1927 p = d1927 q := by
  simp only [d1927, h 112 (by decide), agree1897 p q h, agree1891 p q h]
theorem nonnegative1927 (p : Pattern) : 0 ≤ d1927 p :=
  nonnegative_ite (p 112) (nonnegative1897 p) (nonnegative1891 p)
def d1928 (p : Pattern) : Int := if p 106 then d1927 p else d1885 p
theorem agree1928 (p q : Pattern) (h : Agree support p q) : d1928 p = d1928 q := by
  simp only [d1928, h 106 (by decide), agree1927 p q h, agree1885 p q h]
theorem nonnegative1928 (p : Pattern) : 0 ≤ d1928 p :=
  nonnegative_ite (p 106) (nonnegative1927 p) (nonnegative1885 p)
def d1929 (p : Pattern) : Int := if p 133 then d1886 p else d1919 p
theorem agree1929 (p q : Pattern) (h : Agree support p q) : d1929 p = d1929 q := by
  simp only [d1929, h 133 (by decide), agree1886 p q h, agree1919 p q h]
theorem nonnegative1929 (p : Pattern) : 0 ≤ d1929 p :=
  nonnegative_ite (p 133) (nonnegative1886 p) (nonnegative1919 p)
def d1930 (p : Pattern) : Int := if p 132 then d1929 p else d1920 p
theorem agree1930 (p q : Pattern) (h : Agree support p q) : d1930 p = d1930 q := by
  simp only [d1930, h 132 (by decide), agree1929 p q h, agree1920 p q h]
theorem nonnegative1930 (p : Pattern) : 0 ≤ d1930 p :=
  nonnegative_ite (p 132) (nonnegative1929 p) (nonnegative1920 p)
def d1931 (p : Pattern) : Int := if p 113 then d1930 p else d1912 p
theorem agree1931 (p q : Pattern) (h : Agree support p q) : d1931 p = d1931 q := by
  simp only [d1931, h 113 (by decide), agree1930 p q h, agree1912 p q h]
theorem nonnegative1931 (p : Pattern) : 0 ≤ d1931 p :=
  nonnegative_ite (p 113) (nonnegative1930 p) (nonnegative1912 p)
def d1932 (p : Pattern) : Int := if p 112 then d1931 p else d1906 p
theorem agree1932 (p q : Pattern) (h : Agree support p q) : d1932 p = d1932 q := by
  simp only [d1932, h 112 (by decide), agree1931 p q h, agree1906 p q h]
theorem nonnegative1932 (p : Pattern) : 0 ≤ d1932 p :=
  nonnegative_ite (p 112) (nonnegative1931 p) (nonnegative1906 p)
def d1933 (p : Pattern) : Int := if p 113 then d1896 p else d1891 p
theorem agree1933 (p q : Pattern) (h : Agree support p q) : d1933 p = d1933 q := by
  simp only [d1933, h 113 (by decide), agree1896 p q h, agree1891 p q h]
theorem nonnegative1933 (p : Pattern) : 0 ≤ d1933 p :=
  nonnegative_ite (p 113) (nonnegative1896 p) (nonnegative1891 p)
def d1934 (p : Pattern) : Int := if p 113 then d2 p else d1922 p
theorem agree1934 (p q : Pattern) (h : Agree support p q) : d1934 p = d1934 q := by
  simp only [d1934, h 113 (by decide), agree2 p q h, agree1922 p q h]
theorem nonnegative1934 (p : Pattern) : 0 ≤ d1934 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative1922 p)
def d1935 (p : Pattern) : Int := if p 112 then d1934 p else d1933 p
theorem agree1935 (p q : Pattern) (h : Agree support p q) : d1935 p = d1935 q := by
  simp only [d1935, h 112 (by decide), agree1934 p q h, agree1933 p q h]
theorem nonnegative1935 (p : Pattern) : 0 ≤ d1935 p :=
  nonnegative_ite (p 112) (nonnegative1934 p) (nonnegative1933 p)
def d1936 (p : Pattern) : Int := if p 106 then d1935 p else d1932 p
theorem agree1936 (p q : Pattern) (h : Agree support p q) : d1936 p = d1936 q := by
  simp only [d1936, h 106 (by decide), agree1935 p q h, agree1932 p q h]
theorem nonnegative1936 (p : Pattern) : 0 ≤ d1936 p :=
  nonnegative_ite (p 106) (nonnegative1935 p) (nonnegative1932 p)
def d1937 (p : Pattern) : Int := if p 86 then d1936 p else d1928 p
theorem agree1937 (p q : Pattern) (h : Agree support p q) : d1937 p = d1937 q := by
  simp only [d1937, h 86 (by decide), agree1936 p q h, agree1928 p q h]
theorem nonnegative1937 (p : Pattern) : 0 ≤ d1937 p :=
  nonnegative_ite (p 86) (nonnegative1936 p) (nonnegative1928 p)
def d1938 (p : Pattern) : Int := if p 80 then d1937 p else d1926 p
theorem agree1938 (p q : Pattern) (h : Agree support p q) : d1938 p = d1938 q := by
  simp only [d1938, h 80 (by decide), agree1937 p q h, agree1926 p q h]
theorem nonnegative1938 (p : Pattern) : 0 ≤ d1938 p :=
  nonnegative_ite (p 80) (nonnegative1937 p) (nonnegative1926 p)
def d1939 (p : Pattern) : Int := if p 112 then d2 p else d1105 p
theorem agree1939 (p q : Pattern) (h : Agree support p q) : d1939 p = d1939 q := by
  simp only [d1939, h 112 (by decide), agree2 p q h, agree1105 p q h]
theorem nonnegative1939 (p : Pattern) : 0 ≤ d1939 p :=
  nonnegative_ite (p 112) (nonnegative2 p) (nonnegative1105 p)
def d1940 (p : Pattern) : Int := if p 106 then d1939 p else d1111 p
theorem agree1940 (p q : Pattern) (h : Agree support p q) : d1940 p = d1940 q := by
  simp only [d1940, h 106 (by decide), agree1939 p q h, agree1111 p q h]
theorem nonnegative1940 (p : Pattern) : 0 ≤ d1940 p :=
  nonnegative_ite (p 106) (nonnegative1939 p) (nonnegative1111 p)
def d1941 (p : Pattern) : Int := if p 86 then d1940 p else d1106 p
theorem agree1941 (p q : Pattern) (h : Agree support p q) : d1941 p = d1941 q := by
  simp only [d1941, h 86 (by decide), agree1940 p q h, agree1106 p q h]
theorem nonnegative1941 (p : Pattern) : 0 ≤ d1941 p :=
  nonnegative_ite (p 86) (nonnegative1940 p) (nonnegative1106 p)
def d1942 (p : Pattern) : Int := if p 80 then d1941 p else d1116 p
theorem agree1942 (p q : Pattern) (h : Agree support p q) : d1942 p = d1942 q := by
  simp only [d1942, h 80 (by decide), agree1941 p q h, agree1116 p q h]
theorem nonnegative1942 (p : Pattern) : 0 ≤ d1942 p :=
  nonnegative_ite (p 80) (nonnegative1941 p) (nonnegative1116 p)
def d1943 (p : Pattern) : Int := if p 160 then d985 p else d1 p
theorem agree1943 (p q : Pattern) (h : Agree support p q) : d1943 p = d1943 q := by
  simp only [d1943, h 160 (by decide), agree985 p q h, agree1 p q h]
theorem nonnegative1943 (p : Pattern) : 0 ≤ d1943 p :=
  nonnegative_ite (p 160) (nonnegative985 p) (nonnegative1 p)
def d1944 (p : Pattern) : Int := if p 159 then d1943 p else d1 p
theorem agree1944 (p q : Pattern) (h : Agree support p q) : d1944 p = d1944 q := by
  simp only [d1944, h 159 (by decide), agree1943 p q h, agree1 p q h]
theorem nonnegative1944 (p : Pattern) : 0 ≤ d1944 p :=
  nonnegative_ite (p 159) (nonnegative1943 p) (nonnegative1 p)
def d1945 (p : Pattern) : Int := if p 158 then d1944 p else d1 p
theorem agree1945 (p q : Pattern) (h : Agree support p q) : d1945 p = d1945 q := by
  simp only [d1945, h 158 (by decide), agree1944 p q h, agree1 p q h]
theorem nonnegative1945 (p : Pattern) : 0 ≤ d1945 p :=
  nonnegative_ite (p 158) (nonnegative1944 p) (nonnegative1 p)
def d1946 (p : Pattern) : Int := if p 139 then d1945 p else d1 p
theorem agree1946 (p q : Pattern) (h : Agree support p q) : d1946 p = d1946 q := by
  simp only [d1946, h 139 (by decide), agree1945 p q h, agree1 p q h]
theorem nonnegative1946 (p : Pattern) : 0 ≤ d1946 p :=
  nonnegative_ite (p 139) (nonnegative1945 p) (nonnegative1 p)
def d1947 (p : Pattern) : Int := if p 159 then d1293 p else d1943 p
theorem agree1947 (p q : Pattern) (h : Agree support p q) : d1947 p = d1947 q := by
  simp only [d1947, h 159 (by decide), agree1293 p q h, agree1943 p q h]
theorem nonnegative1947 (p : Pattern) : 0 ≤ d1947 p :=
  nonnegative_ite (p 159) (nonnegative1293 p) (nonnegative1943 p)
def d1948 (p : Pattern) : Int := if p 158 then d1947 p else d1944 p
theorem agree1948 (p q : Pattern) (h : Agree support p q) : d1948 p = d1948 q := by
  simp only [d1948, h 158 (by decide), agree1947 p q h, agree1944 p q h]
theorem nonnegative1948 (p : Pattern) : 0 ≤ d1948 p :=
  nonnegative_ite (p 158) (nonnegative1947 p) (nonnegative1944 p)
def d1949 (p : Pattern) : Int := if p 139 then d1948 p else d1945 p
theorem agree1949 (p q : Pattern) (h : Agree support p q) : d1949 p = d1949 q := by
  simp only [d1949, h 139 (by decide), agree1948 p q h, agree1945 p q h]
theorem nonnegative1949 (p : Pattern) : 0 ≤ d1949 p :=
  nonnegative_ite (p 139) (nonnegative1948 p) (nonnegative1945 p)
def d1950 (p : Pattern) : Int := if p 138 then d1949 p else d1946 p
theorem agree1950 (p q : Pattern) (h : Agree support p q) : d1950 p = d1950 q := by
  simp only [d1950, h 138 (by decide), agree1949 p q h, agree1946 p q h]
theorem nonnegative1950 (p : Pattern) : 0 ≤ d1950 p :=
  nonnegative_ite (p 138) (nonnegative1949 p) (nonnegative1946 p)
def d1951 (p : Pattern) : Int := if p 159 then d0 p else d1293 p
theorem agree1951 (p q : Pattern) (h : Agree support p q) : d1951 p = d1951 q := by
  simp only [d1951, h 159 (by decide), agree0 p q h, agree1293 p q h]
theorem nonnegative1951 (p : Pattern) : 0 ≤ d1951 p :=
  nonnegative_ite (p 159) (nonnegative0 p) (nonnegative1293 p)
def d1952 (p : Pattern) : Int := if p 158 then d1951 p else d1947 p
theorem agree1952 (p q : Pattern) (h : Agree support p q) : d1952 p = d1952 q := by
  simp only [d1952, h 158 (by decide), agree1951 p q h, agree1947 p q h]
theorem nonnegative1952 (p : Pattern) : 0 ≤ d1952 p :=
  nonnegative_ite (p 158) (nonnegative1951 p) (nonnegative1947 p)
def d1953 (p : Pattern) : Int := if p 139 then d1952 p else d1948 p
theorem agree1953 (p q : Pattern) (h : Agree support p q) : d1953 p = d1953 q := by
  simp only [d1953, h 139 (by decide), agree1952 p q h, agree1948 p q h]
theorem nonnegative1953 (p : Pattern) : 0 ≤ d1953 p :=
  nonnegative_ite (p 139) (nonnegative1952 p) (nonnegative1948 p)
def d1954 (p : Pattern) : Int := if p 138 then d1953 p else d1949 p
theorem agree1954 (p q : Pattern) (h : Agree support p q) : d1954 p = d1954 q := by
  simp only [d1954, h 138 (by decide), agree1953 p q h, agree1949 p q h]
theorem nonnegative1954 (p : Pattern) : 0 ≤ d1954 p :=
  nonnegative_ite (p 138) (nonnegative1953 p) (nonnegative1949 p)
def d1955 (p : Pattern) : Int := if p 134 then d1954 p else d1950 p
theorem agree1955 (p q : Pattern) (h : Agree support p q) : d1955 p = d1955 q := by
  simp only [d1955, h 134 (by decide), agree1954 p q h, agree1950 p q h]
theorem nonnegative1955 (p : Pattern) : 0 ≤ d1955 p :=
  nonnegative_ite (p 134) (nonnegative1954 p) (nonnegative1950 p)
def d1956 (p : Pattern) : Int := if p 158 then d0 p else d1951 p
theorem agree1956 (p q : Pattern) (h : Agree support p q) : d1956 p = d1956 q := by
  simp only [d1956, h 158 (by decide), agree0 p q h, agree1951 p q h]
theorem nonnegative1956 (p : Pattern) : 0 ≤ d1956 p :=
  nonnegative_ite (p 158) (nonnegative0 p) (nonnegative1951 p)
def d1957 (p : Pattern) : Int := if p 139 then d1956 p else d1952 p
theorem agree1957 (p q : Pattern) (h : Agree support p q) : d1957 p = d1957 q := by
  simp only [d1957, h 139 (by decide), agree1956 p q h, agree1952 p q h]
theorem nonnegative1957 (p : Pattern) : 0 ≤ d1957 p :=
  nonnegative_ite (p 139) (nonnegative1956 p) (nonnegative1952 p)
def d1958 (p : Pattern) : Int := if p 138 then d1957 p else d1953 p
theorem agree1958 (p q : Pattern) (h : Agree support p q) : d1958 p = d1958 q := by
  simp only [d1958, h 138 (by decide), agree1957 p q h, agree1953 p q h]
theorem nonnegative1958 (p : Pattern) : 0 ≤ d1958 p :=
  nonnegative_ite (p 138) (nonnegative1957 p) (nonnegative1953 p)
def d1959 (p : Pattern) : Int := if p 134 then d1958 p else d1954 p
theorem agree1959 (p q : Pattern) (h : Agree support p q) : d1959 p = d1959 q := by
  simp only [d1959, h 134 (by decide), agree1958 p q h, agree1954 p q h]
theorem nonnegative1959 (p : Pattern) : 0 ≤ d1959 p :=
  nonnegative_ite (p 134) (nonnegative1958 p) (nonnegative1954 p)
def d1960 (p : Pattern) : Int := if p 133 then d1959 p else d1955 p
theorem agree1960 (p q : Pattern) (h : Agree support p q) : d1960 p = d1960 q := by
  simp only [d1960, h 133 (by decide), agree1959 p q h, agree1955 p q h]
theorem nonnegative1960 (p : Pattern) : 0 ≤ d1960 p :=
  nonnegative_ite (p 133) (nonnegative1959 p) (nonnegative1955 p)
def d1961 (p : Pattern) : Int := if p 139 then d0 p else d1956 p
theorem agree1961 (p q : Pattern) (h : Agree support p q) : d1961 p = d1961 q := by
  simp only [d1961, h 139 (by decide), agree0 p q h, agree1956 p q h]
theorem nonnegative1961 (p : Pattern) : 0 ≤ d1961 p :=
  nonnegative_ite (p 139) (nonnegative0 p) (nonnegative1956 p)
def d1962 (p : Pattern) : Int := if p 138 then d1961 p else d1957 p
theorem agree1962 (p q : Pattern) (h : Agree support p q) : d1962 p = d1962 q := by
  simp only [d1962, h 138 (by decide), agree1961 p q h, agree1957 p q h]
theorem nonnegative1962 (p : Pattern) : 0 ≤ d1962 p :=
  nonnegative_ite (p 138) (nonnegative1961 p) (nonnegative1957 p)
def d1963 (p : Pattern) : Int := if p 134 then d1962 p else d1958 p
theorem agree1963 (p q : Pattern) (h : Agree support p q) : d1963 p = d1963 q := by
  simp only [d1963, h 134 (by decide), agree1962 p q h, agree1958 p q h]
theorem nonnegative1963 (p : Pattern) : 0 ≤ d1963 p :=
  nonnegative_ite (p 134) (nonnegative1962 p) (nonnegative1958 p)
def d1964 (p : Pattern) : Int := if p 133 then d1963 p else d1959 p
theorem agree1964 (p q : Pattern) (h : Agree support p q) : d1964 p = d1964 q := by
  simp only [d1964, h 133 (by decide), agree1963 p q h, agree1959 p q h]
theorem nonnegative1964 (p : Pattern) : 0 ≤ d1964 p :=
  nonnegative_ite (p 133) (nonnegative1963 p) (nonnegative1959 p)
def d1965 (p : Pattern) : Int := if p 132 then d1964 p else d1960 p
theorem agree1965 (p q : Pattern) (h : Agree support p q) : d1965 p = d1965 q := by
  simp only [d1965, h 132 (by decide), agree1964 p q h, agree1960 p q h]
theorem nonnegative1965 (p : Pattern) : 0 ≤ d1965 p :=
  nonnegative_ite (p 132) (nonnegative1964 p) (nonnegative1960 p)
def d1966 (p : Pattern) : Int := if p 138 then d0 p else d1961 p
theorem agree1966 (p q : Pattern) (h : Agree support p q) : d1966 p = d1966 q := by
  simp only [d1966, h 138 (by decide), agree0 p q h, agree1961 p q h]
theorem nonnegative1966 (p : Pattern) : 0 ≤ d1966 p :=
  nonnegative_ite (p 138) (nonnegative0 p) (nonnegative1961 p)
def d1967 (p : Pattern) : Int := if p 134 then d1966 p else d1962 p
theorem agree1967 (p q : Pattern) (h : Agree support p q) : d1967 p = d1967 q := by
  simp only [d1967, h 134 (by decide), agree1966 p q h, agree1962 p q h]
theorem nonnegative1967 (p : Pattern) : 0 ≤ d1967 p :=
  nonnegative_ite (p 134) (nonnegative1966 p) (nonnegative1962 p)
def d1968 (p : Pattern) : Int := if p 133 then d1967 p else d1963 p
theorem agree1968 (p q : Pattern) (h : Agree support p q) : d1968 p = d1968 q := by
  simp only [d1968, h 133 (by decide), agree1967 p q h, agree1963 p q h]
theorem nonnegative1968 (p : Pattern) : 0 ≤ d1968 p :=
  nonnegative_ite (p 133) (nonnegative1967 p) (nonnegative1963 p)
def d1969 (p : Pattern) : Int := if p 132 then d1968 p else d1964 p
theorem agree1969 (p q : Pattern) (h : Agree support p q) : d1969 p = d1969 q := by
  simp only [d1969, h 132 (by decide), agree1968 p q h, agree1964 p q h]
theorem nonnegative1969 (p : Pattern) : 0 ≤ d1969 p :=
  nonnegative_ite (p 132) (nonnegative1968 p) (nonnegative1964 p)
def d1970 (p : Pattern) : Int := if p 113 then d1969 p else d1965 p
theorem agree1970 (p q : Pattern) (h : Agree support p q) : d1970 p = d1970 q := by
  simp only [d1970, h 113 (by decide), agree1969 p q h, agree1965 p q h]
theorem nonnegative1970 (p : Pattern) : 0 ≤ d1970 p :=
  nonnegative_ite (p 113) (nonnegative1969 p) (nonnegative1965 p)
def d1971 (p : Pattern) : Int := if p 134 then d0 p else d1966 p
theorem agree1971 (p q : Pattern) (h : Agree support p q) : d1971 p = d1971 q := by
  simp only [d1971, h 134 (by decide), agree0 p q h, agree1966 p q h]
theorem nonnegative1971 (p : Pattern) : 0 ≤ d1971 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative1966 p)
def d1972 (p : Pattern) : Int := if p 133 then d1971 p else d1967 p
theorem agree1972 (p q : Pattern) (h : Agree support p q) : d1972 p = d1972 q := by
  simp only [d1972, h 133 (by decide), agree1971 p q h, agree1967 p q h]
theorem nonnegative1972 (p : Pattern) : 0 ≤ d1972 p :=
  nonnegative_ite (p 133) (nonnegative1971 p) (nonnegative1967 p)
def d1973 (p : Pattern) : Int := if p 132 then d1972 p else d1968 p
theorem agree1973 (p q : Pattern) (h : Agree support p q) : d1973 p = d1973 q := by
  simp only [d1973, h 132 (by decide), agree1972 p q h, agree1968 p q h]
theorem nonnegative1973 (p : Pattern) : 0 ≤ d1973 p :=
  nonnegative_ite (p 132) (nonnegative1972 p) (nonnegative1968 p)
def d1974 (p : Pattern) : Int := if p 113 then d1973 p else d1969 p
theorem agree1974 (p q : Pattern) (h : Agree support p q) : d1974 p = d1974 q := by
  simp only [d1974, h 113 (by decide), agree1973 p q h, agree1969 p q h]
theorem nonnegative1974 (p : Pattern) : 0 ≤ d1974 p :=
  nonnegative_ite (p 113) (nonnegative1973 p) (nonnegative1969 p)
def d1975 (p : Pattern) : Int := if p 112 then d1974 p else d1970 p
theorem agree1975 (p q : Pattern) (h : Agree support p q) : d1975 p = d1975 q := by
  simp only [d1975, h 112 (by decide), agree1974 p q h, agree1970 p q h]
theorem nonnegative1975 (p : Pattern) : 0 ≤ d1975 p :=
  nonnegative_ite (p 112) (nonnegative1974 p) (nonnegative1970 p)
def d1976 (p : Pattern) : Int := if p 133 then d0 p else d1971 p
theorem agree1976 (p q : Pattern) (h : Agree support p q) : d1976 p = d1976 q := by
  simp only [d1976, h 133 (by decide), agree0 p q h, agree1971 p q h]
theorem nonnegative1976 (p : Pattern) : 0 ≤ d1976 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative1971 p)
def d1977 (p : Pattern) : Int := if p 132 then d1976 p else d1972 p
theorem agree1977 (p q : Pattern) (h : Agree support p q) : d1977 p = d1977 q := by
  simp only [d1977, h 132 (by decide), agree1976 p q h, agree1972 p q h]
theorem nonnegative1977 (p : Pattern) : 0 ≤ d1977 p :=
  nonnegative_ite (p 132) (nonnegative1976 p) (nonnegative1972 p)
def d1978 (p : Pattern) : Int := if p 113 then d1977 p else d1973 p
theorem agree1978 (p q : Pattern) (h : Agree support p q) : d1978 p = d1978 q := by
  simp only [d1978, h 113 (by decide), agree1977 p q h, agree1973 p q h]
theorem nonnegative1978 (p : Pattern) : 0 ≤ d1978 p :=
  nonnegative_ite (p 113) (nonnegative1977 p) (nonnegative1973 p)
def d1979 (p : Pattern) : Int := if p 112 then d1978 p else d1974 p
theorem agree1979 (p q : Pattern) (h : Agree support p q) : d1979 p = d1979 q := by
  simp only [d1979, h 112 (by decide), agree1978 p q h, agree1974 p q h]
theorem nonnegative1979 (p : Pattern) : 0 ≤ d1979 p :=
  nonnegative_ite (p 112) (nonnegative1978 p) (nonnegative1974 p)
def d1980 (p : Pattern) : Int := if p 106 then d1979 p else d1975 p
theorem agree1980 (p q : Pattern) (h : Agree support p q) : d1980 p = d1980 q := by
  simp only [d1980, h 106 (by decide), agree1979 p q h, agree1975 p q h]
theorem nonnegative1980 (p : Pattern) : 0 ≤ d1980 p :=
  nonnegative_ite (p 106) (nonnegative1979 p) (nonnegative1975 p)
def d1981 (p : Pattern) : Int := if p 132 then d0 p else d1976 p
theorem agree1981 (p q : Pattern) (h : Agree support p q) : d1981 p = d1981 q := by
  simp only [d1981, h 132 (by decide), agree0 p q h, agree1976 p q h]
theorem nonnegative1981 (p : Pattern) : 0 ≤ d1981 p :=
  nonnegative_ite (p 132) (nonnegative0 p) (nonnegative1976 p)
def d1982 (p : Pattern) : Int := if p 113 then d1981 p else d1977 p
theorem agree1982 (p q : Pattern) (h : Agree support p q) : d1982 p = d1982 q := by
  simp only [d1982, h 113 (by decide), agree1981 p q h, agree1977 p q h]
theorem nonnegative1982 (p : Pattern) : 0 ≤ d1982 p :=
  nonnegative_ite (p 113) (nonnegative1981 p) (nonnegative1977 p)
def d1983 (p : Pattern) : Int := if p 112 then d1982 p else d1978 p
theorem agree1983 (p q : Pattern) (h : Agree support p q) : d1983 p = d1983 q := by
  simp only [d1983, h 112 (by decide), agree1982 p q h, agree1978 p q h]
theorem nonnegative1983 (p : Pattern) : 0 ≤ d1983 p :=
  nonnegative_ite (p 112) (nonnegative1982 p) (nonnegative1978 p)
def d1984 (p : Pattern) : Int := if p 106 then d1983 p else d1979 p
theorem agree1984 (p q : Pattern) (h : Agree support p q) : d1984 p = d1984 q := by
  simp only [d1984, h 106 (by decide), agree1983 p q h, agree1979 p q h]
theorem nonnegative1984 (p : Pattern) : 0 ≤ d1984 p :=
  nonnegative_ite (p 106) (nonnegative1983 p) (nonnegative1979 p)
def d1985 (p : Pattern) : Int := if p 86 then d1984 p else d1980 p
theorem agree1985 (p q : Pattern) (h : Agree support p q) : d1985 p = d1985 q := by
  simp only [d1985, h 86 (by decide), agree1984 p q h, agree1980 p q h]
theorem nonnegative1985 (p : Pattern) : 0 ≤ d1985 p :=
  nonnegative_ite (p 86) (nonnegative1984 p) (nonnegative1980 p)
def d1986 (p : Pattern) : Int := if p 113 then d0 p else d1981 p
theorem agree1986 (p q : Pattern) (h : Agree support p q) : d1986 p = d1986 q := by
  simp only [d1986, h 113 (by decide), agree0 p q h, agree1981 p q h]
theorem nonnegative1986 (p : Pattern) : 0 ≤ d1986 p :=
  nonnegative_ite (p 113) (nonnegative0 p) (nonnegative1981 p)
def d1987 (p : Pattern) : Int := if p 112 then d1986 p else d1982 p
theorem agree1987 (p q : Pattern) (h : Agree support p q) : d1987 p = d1987 q := by
  simp only [d1987, h 112 (by decide), agree1986 p q h, agree1982 p q h]
theorem nonnegative1987 (p : Pattern) : 0 ≤ d1987 p :=
  nonnegative_ite (p 112) (nonnegative1986 p) (nonnegative1982 p)
def d1988 (p : Pattern) : Int := if p 106 then d1987 p else d1983 p
theorem agree1988 (p q : Pattern) (h : Agree support p q) : d1988 p = d1988 q := by
  simp only [d1988, h 106 (by decide), agree1987 p q h, agree1983 p q h]
theorem nonnegative1988 (p : Pattern) : 0 ≤ d1988 p :=
  nonnegative_ite (p 106) (nonnegative1987 p) (nonnegative1983 p)
def d1989 (p : Pattern) : Int := if p 86 then d1988 p else d1984 p
theorem agree1989 (p q : Pattern) (h : Agree support p q) : d1989 p = d1989 q := by
  simp only [d1989, h 86 (by decide), agree1988 p q h, agree1984 p q h]
theorem nonnegative1989 (p : Pattern) : 0 ≤ d1989 p :=
  nonnegative_ite (p 86) (nonnegative1988 p) (nonnegative1984 p)
def d1990 (p : Pattern) : Int := if p 80 then d1989 p else d1985 p
theorem agree1990 (p q : Pattern) (h : Agree support p q) : d1990 p = d1990 q := by
  simp only [d1990, h 80 (by decide), agree1989 p q h, agree1985 p q h]
theorem nonnegative1990 (p : Pattern) : 0 ≤ d1990 p :=
  nonnegative_ite (p 80) (nonnegative1989 p) (nonnegative1985 p)
def d1991 (p : Pattern) : Int := if p 112 then d152 p else d141 p
theorem agree1991 (p q : Pattern) (h : Agree support p q) : d1991 p = d1991 q := by
  simp only [d1991, h 112 (by decide), agree152 p q h, agree141 p q h]
theorem nonnegative1991 (p : Pattern) : 0 ≤ d1991 p :=
  nonnegative_ite (p 112) (nonnegative152 p) (nonnegative141 p)
end NetHack.Sokoban32Refined
