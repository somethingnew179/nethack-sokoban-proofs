/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1920 (p : Pattern) : Int := if p 225 then d1919 p else d116 p
theorem agree1920 (p q : Pattern) (h : Agree support p q) : d1920 p = d1920 q := by
  simp only [d1920, h 225 (by decide), agree1919 p q h, agree116 p q h]
theorem nonnegative1920 (p : Pattern) : 0 ≤ d1920 p :=
  nonnegative_ite (p 225) (nonnegative1919 p) (nonnegative116 p)
def d1921 (p : Pattern) : Int := if p 224 then d1919 p else d1920 p
theorem agree1921 (p q : Pattern) (h : Agree support p q) : d1921 p = d1921 q := by
  simp only [d1921, h 224 (by decide), agree1919 p q h, agree1920 p q h]
theorem nonnegative1921 (p : Pattern) : 0 ≤ d1921 p :=
  nonnegative_ite (p 224) (nonnegative1919 p) (nonnegative1920 p)
def d1922 (p : Pattern) : Int := if p 204 then d12 p else d1921 p
theorem agree1922 (p q : Pattern) (h : Agree support p q) : d1922 p = d1922 q := by
  simp only [d1922, h 204 (by decide), agree12 p q h, agree1921 p q h]
theorem nonnegative1922 (p : Pattern) : 0 ≤ d1922 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1921 p)
def d1923 (p : Pattern) : Int := if p 182 then d1922 p else d117 p
theorem agree1923 (p q : Pattern) (h : Agree support p q) : d1923 p = d1923 q := by
  simp only [d1923, h 182 (by decide), agree1922 p q h, agree117 p q h]
theorem nonnegative1923 (p : Pattern) : 0 ≤ d1923 p :=
  nonnegative_ite (p 182) (nonnegative1922 p) (nonnegative117 p)
def d1924 (p : Pattern) : Int := if p 163 then d1923 p else d1917 p
theorem agree1924 (p q : Pattern) (h : Agree support p q) : d1924 p = d1924 q := by
  simp only [d1924, h 163 (by decide), agree1923 p q h, agree1917 p q h]
theorem nonnegative1924 (p : Pattern) : 0 ≤ d1924 p :=
  nonnegative_ite (p 163) (nonnegative1923 p) (nonnegative1917 p)
def d1925 (p : Pattern) : Int := if p 163 then d1754 p else d1885 p
theorem agree1925 (p q : Pattern) (h : Agree support p q) : d1925 p = d1925 q := by
  simp only [d1925, h 163 (by decide), agree1754 p q h, agree1885 p q h]
theorem nonnegative1925 (p : Pattern) : 0 ≤ d1925 p :=
  nonnegative_ite (p 163) (nonnegative1754 p) (nonnegative1885 p)
def d1926 (p : Pattern) : Int := if p 162 then d1925 p else d1924 p
theorem agree1926 (p q : Pattern) (h : Agree support p q) : d1926 p = d1926 q := by
  simp only [d1926, h 162 (by decide), agree1925 p q h, agree1924 p q h]
theorem nonnegative1926 (p : Pattern) : 0 ≤ d1926 p :=
  nonnegative_ite (p 162) (nonnegative1925 p) (nonnegative1924 p)
def d1927 (p : Pattern) : Int := if p 163 then d1756 p else d1885 p
theorem agree1927 (p q : Pattern) (h : Agree support p q) : d1927 p = d1927 q := by
  simp only [d1927, h 163 (by decide), agree1756 p q h, agree1885 p q h]
theorem nonnegative1927 (p : Pattern) : 0 ≤ d1927 p :=
  nonnegative_ite (p 163) (nonnegative1756 p) (nonnegative1885 p)
def d1928 (p : Pattern) : Int := if p 162 then d12 p else d1927 p
theorem agree1928 (p q : Pattern) (h : Agree support p q) : d1928 p = d1928 q := by
  simp only [d1928, h 162 (by decide), agree12 p q h, agree1927 p q h]
theorem nonnegative1928 (p : Pattern) : 0 ≤ d1928 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1927 p)
def d1929 (p : Pattern) : Int := if p 161 then d1928 p else d1926 p
theorem agree1929 (p q : Pattern) (h : Agree support p q) : d1929 p = d1929 q := by
  simp only [d1929, h 161 (by decide), agree1928 p q h, agree1926 p q h]
theorem nonnegative1929 (p : Pattern) : 0 ≤ d1929 p :=
  nonnegative_ite (p 161) (nonnegative1928 p) (nonnegative1926 p)
def d1930 (p : Pattern) : Int := if p 182 then d12 p else d117 p
theorem agree1930 (p q : Pattern) (h : Agree support p q) : d1930 p = d1930 q := by
  simp only [d1930, h 182 (by decide), agree12 p q h, agree117 p q h]
theorem nonnegative1930 (p : Pattern) : 0 ≤ d1930 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative117 p)
def d1931 (p : Pattern) : Int := if p 163 then d1930 p else d1907 p
theorem agree1931 (p q : Pattern) (h : Agree support p q) : d1931 p = d1931 q := by
  simp only [d1931, h 163 (by decide), agree1930 p q h, agree1907 p q h]
theorem nonnegative1931 (p : Pattern) : 0 ≤ d1931 p :=
  nonnegative_ite (p 163) (nonnegative1930 p) (nonnegative1907 p)
def d1932 (p : Pattern) : Int := if p 163 then d277 p else d1910 p
theorem agree1932 (p q : Pattern) (h : Agree support p q) : d1932 p = d1932 q := by
  simp only [d1932, h 163 (by decide), agree277 p q h, agree1910 p q h]
theorem nonnegative1932 (p : Pattern) : 0 ≤ d1932 p :=
  nonnegative_ite (p 163) (nonnegative277 p) (nonnegative1910 p)
def d1933 (p : Pattern) : Int := if p 162 then d1932 p else d1931 p
theorem agree1933 (p q : Pattern) (h : Agree support p q) : d1933 p = d1933 q := by
  simp only [d1933, h 162 (by decide), agree1932 p q h, agree1931 p q h]
theorem nonnegative1933 (p : Pattern) : 0 ≤ d1933 p :=
  nonnegative_ite (p 162) (nonnegative1932 p) (nonnegative1931 p)
def d1934 (p : Pattern) : Int := if p 163 then d538 p else d1910 p
theorem agree1934 (p q : Pattern) (h : Agree support p q) : d1934 p = d1934 q := by
  simp only [d1934, h 163 (by decide), agree538 p q h, agree1910 p q h]
theorem nonnegative1934 (p : Pattern) : 0 ≤ d1934 p :=
  nonnegative_ite (p 163) (nonnegative538 p) (nonnegative1910 p)
def d1935 (p : Pattern) : Int := if p 162 then d12 p else d1934 p
theorem agree1935 (p q : Pattern) (h : Agree support p q) : d1935 p = d1935 q := by
  simp only [d1935, h 162 (by decide), agree12 p q h, agree1934 p q h]
theorem nonnegative1935 (p : Pattern) : 0 ≤ d1935 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1934 p)
def d1936 (p : Pattern) : Int := if p 161 then d1935 p else d1933 p
theorem agree1936 (p q : Pattern) (h : Agree support p q) : d1936 p = d1936 q := by
  simp only [d1936, h 161 (by decide), agree1935 p q h, agree1933 p q h]
theorem nonnegative1936 (p : Pattern) : 0 ≤ d1936 p :=
  nonnegative_ite (p 161) (nonnegative1935 p) (nonnegative1933 p)
def d1937 (p : Pattern) : Int := if p 160 then d1936 p else d1929 p
theorem agree1937 (p q : Pattern) (h : Agree support p q) : d1937 p = d1937 q := by
  simp only [d1937, h 160 (by decide), agree1936 p q h, agree1929 p q h]
theorem nonnegative1937 (p : Pattern) : 0 ≤ d1937 p :=
  nonnegative_ite (p 160) (nonnegative1936 p) (nonnegative1929 p)
def d1938 (p : Pattern) : Int := if p 141 then d1937 p else d1915 p
theorem agree1938 (p q : Pattern) (h : Agree support p q) : d1938 p = d1938 q := by
  simp only [d1938, h 141 (by decide), agree1937 p q h, agree1915 p q h]
theorem nonnegative1938 (p : Pattern) : 0 ≤ d1938 p :=
  nonnegative_ite (p 141) (nonnegative1937 p) (nonnegative1915 p)
def d1939 (p : Pattern) : Int := if p 247 then d5 p else d1 p
theorem agree1939 (p q : Pattern) (h : Agree support p q) : d1939 p = d1939 q := by
  simp only [d1939, h 247 (by decide), agree5 p q h, agree1 p q h]
theorem nonnegative1939 (p : Pattern) : 0 ≤ d1939 p :=
  nonnegative_ite (p 247) (nonnegative5 p) (nonnegative1 p)
def d1940 (p : Pattern) : Int := if p 246 then d106 p else d1939 p
theorem agree1940 (p q : Pattern) (h : Agree support p q) : d1940 p = d1940 q := by
  simp only [d1940, h 246 (by decide), agree106 p q h, agree1939 p q h]
theorem nonnegative1940 (p : Pattern) : 0 ≤ d1940 p :=
  nonnegative_ite (p 246) (nonnegative106 p) (nonnegative1939 p)
def d1941 (p : Pattern) : Int := if p 225 then d1940 p else d103 p
theorem agree1941 (p q : Pattern) (h : Agree support p q) : d1941 p = d1941 q := by
  simp only [d1941, h 225 (by decide), agree1940 p q h, agree103 p q h]
theorem nonnegative1941 (p : Pattern) : 0 ≤ d1941 p :=
  nonnegative_ite (p 225) (nonnegative1940 p) (nonnegative103 p)
def d1942 (p : Pattern) : Int := if p 224 then d1940 p else d1941 p
theorem agree1942 (p q : Pattern) (h : Agree support p q) : d1942 p = d1942 q := by
  simp only [d1942, h 224 (by decide), agree1940 p q h, agree1941 p q h]
theorem nonnegative1942 (p : Pattern) : 0 ≤ d1942 p :=
  nonnegative_ite (p 224) (nonnegative1940 p) (nonnegative1941 p)
def d1943 (p : Pattern) : Int := if p 204 then d12 p else d1942 p
theorem agree1943 (p q : Pattern) (h : Agree support p q) : d1943 p = d1943 q := by
  simp only [d1943, h 204 (by decide), agree12 p q h, agree1942 p q h]
theorem nonnegative1943 (p : Pattern) : 0 ≤ d1943 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1942 p)
def d1944 (p : Pattern) : Int := if p 182 then d1943 p else d104 p
theorem agree1944 (p q : Pattern) (h : Agree support p q) : d1944 p = d1944 q := by
  simp only [d1944, h 182 (by decide), agree1943 p q h, agree104 p q h]
theorem nonnegative1944 (p : Pattern) : 0 ≤ d1944 p :=
  nonnegative_ite (p 182) (nonnegative1943 p) (nonnegative104 p)
def d1945 (p : Pattern) : Int := if p 247 then d7 p else d1 p
theorem agree1945 (p q : Pattern) (h : Agree support p q) : d1945 p = d1945 q := by
  simp only [d1945, h 247 (by decide), agree7 p q h, agree1 p q h]
theorem nonnegative1945 (p : Pattern) : 0 ≤ d1945 p :=
  nonnegative_ite (p 247) (nonnegative7 p) (nonnegative1 p)
def d1946 (p : Pattern) : Int := if p 246 then d119 p else d1945 p
theorem agree1946 (p q : Pattern) (h : Agree support p q) : d1946 p = d1946 q := by
  simp only [d1946, h 246 (by decide), agree119 p q h, agree1945 p q h]
theorem nonnegative1946 (p : Pattern) : 0 ≤ d1946 p :=
  nonnegative_ite (p 246) (nonnegative119 p) (nonnegative1945 p)
def d1947 (p : Pattern) : Int := if p 225 then d1946 p else d103 p
theorem agree1947 (p q : Pattern) (h : Agree support p q) : d1947 p = d1947 q := by
  simp only [d1947, h 225 (by decide), agree1946 p q h, agree103 p q h]
theorem nonnegative1947 (p : Pattern) : 0 ≤ d1947 p :=
  nonnegative_ite (p 225) (nonnegative1946 p) (nonnegative103 p)
def d1948 (p : Pattern) : Int := if p 247 then d9 p else d1 p
theorem agree1948 (p q : Pattern) (h : Agree support p q) : d1948 p = d1948 q := by
  simp only [d1948, h 247 (by decide), agree9 p q h, agree1 p q h]
theorem nonnegative1948 (p : Pattern) : 0 ≤ d1948 p :=
  nonnegative_ite (p 247) (nonnegative9 p) (nonnegative1 p)
def d1949 (p : Pattern) : Int := if p 246 then d23 p else d1948 p
theorem agree1949 (p q : Pattern) (h : Agree support p q) : d1949 p = d1949 q := by
  simp only [d1949, h 246 (by decide), agree23 p q h, agree1948 p q h]
theorem nonnegative1949 (p : Pattern) : 0 ≤ d1949 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative1948 p)
def d1950 (p : Pattern) : Int := if p 225 then d1949 p else d1940 p
theorem agree1950 (p q : Pattern) (h : Agree support p q) : d1950 p = d1950 q := by
  simp only [d1950, h 225 (by decide), agree1949 p q h, agree1940 p q h]
theorem nonnegative1950 (p : Pattern) : 0 ≤ d1950 p :=
  nonnegative_ite (p 225) (nonnegative1949 p) (nonnegative1940 p)
def d1951 (p : Pattern) : Int := if p 224 then d1950 p else d1947 p
theorem agree1951 (p q : Pattern) (h : Agree support p q) : d1951 p = d1951 q := by
  simp only [d1951, h 224 (by decide), agree1950 p q h, agree1947 p q h]
theorem nonnegative1951 (p : Pattern) : 0 ≤ d1951 p :=
  nonnegative_ite (p 224) (nonnegative1950 p) (nonnegative1947 p)
def d1952 (p : Pattern) : Int := if p 204 then d12 p else d1951 p
theorem agree1952 (p q : Pattern) (h : Agree support p q) : d1952 p = d1952 q := by
  simp only [d1952, h 204 (by decide), agree12 p q h, agree1951 p q h]
theorem nonnegative1952 (p : Pattern) : 0 ≤ d1952 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1951 p)
def d1953 (p : Pattern) : Int := if p 182 then d1952 p else d104 p
theorem agree1953 (p q : Pattern) (h : Agree support p q) : d1953 p = d1953 q := by
  simp only [d1953, h 182 (by decide), agree1952 p q h, agree104 p q h]
theorem nonnegative1953 (p : Pattern) : 0 ≤ d1953 p :=
  nonnegative_ite (p 182) (nonnegative1952 p) (nonnegative104 p)
def d1954 (p : Pattern) : Int := if p 163 then d1953 p else d1944 p
theorem agree1954 (p q : Pattern) (h : Agree support p q) : d1954 p = d1954 q := by
  simp only [d1954, h 163 (by decide), agree1953 p q h, agree1944 p q h]
theorem nonnegative1954 (p : Pattern) : 0 ≤ d1954 p :=
  nonnegative_ite (p 163) (nonnegative1953 p) (nonnegative1944 p)
def d1955 (p : Pattern) : Int := if p 246 then d57 p else d102 p
theorem agree1955 (p q : Pattern) (h : Agree support p q) : d1955 p = d1955 q := by
  simp only [d1955, h 246 (by decide), agree57 p q h, agree102 p q h]
theorem nonnegative1955 (p : Pattern) : 0 ≤ d1955 p :=
  nonnegative_ite (p 246) (nonnegative57 p) (nonnegative102 p)
def d1956 (p : Pattern) : Int := if p 225 then d1955 p else d1940 p
theorem agree1956 (p q : Pattern) (h : Agree support p q) : d1956 p = d1956 q := by
  simp only [d1956, h 225 (by decide), agree1955 p q h, agree1940 p q h]
theorem nonnegative1956 (p : Pattern) : 0 ≤ d1956 p :=
  nonnegative_ite (p 225) (nonnegative1955 p) (nonnegative1940 p)
def d1957 (p : Pattern) : Int := if p 224 then d1956 p else d1947 p
theorem agree1957 (p q : Pattern) (h : Agree support p q) : d1957 p = d1957 q := by
  simp only [d1957, h 224 (by decide), agree1956 p q h, agree1947 p q h]
theorem nonnegative1957 (p : Pattern) : 0 ≤ d1957 p :=
  nonnegative_ite (p 224) (nonnegative1956 p) (nonnegative1947 p)
def d1958 (p : Pattern) : Int := if p 204 then d12 p else d1957 p
theorem agree1958 (p q : Pattern) (h : Agree support p q) : d1958 p = d1958 q := by
  simp only [d1958, h 204 (by decide), agree12 p q h, agree1957 p q h]
theorem nonnegative1958 (p : Pattern) : 0 ≤ d1958 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1957 p)
def d1959 (p : Pattern) : Int := if p 182 then d1958 p else d104 p
theorem agree1959 (p q : Pattern) (h : Agree support p q) : d1959 p = d1959 q := by
  simp only [d1959, h 182 (by decide), agree1958 p q h, agree104 p q h]
theorem nonnegative1959 (p : Pattern) : 0 ≤ d1959 p :=
  nonnegative_ite (p 182) (nonnegative1958 p) (nonnegative104 p)
def d1960 (p : Pattern) : Int := if p 247 then d11 p else d5 p
theorem agree1960 (p q : Pattern) (h : Agree support p q) : d1960 p = d1960 q := by
  simp only [d1960, h 247 (by decide), agree11 p q h, agree5 p q h]
theorem nonnegative1960 (p : Pattern) : 0 ≤ d1960 p :=
  nonnegative_ite (p 247) (nonnegative11 p) (nonnegative5 p)
def d1961 (p : Pattern) : Int := if p 246 then d39 p else d1960 p
theorem agree1961 (p q : Pattern) (h : Agree support p q) : d1961 p = d1961 q := by
  simp only [d1961, h 246 (by decide), agree39 p q h, agree1960 p q h]
theorem nonnegative1961 (p : Pattern) : 0 ≤ d1961 p :=
  nonnegative_ite (p 246) (nonnegative39 p) (nonnegative1960 p)
def d1962 (p : Pattern) : Int := if p 225 then d1961 p else d107 p
theorem agree1962 (p q : Pattern) (h : Agree support p q) : d1962 p = d1962 q := by
  simp only [d1962, h 225 (by decide), agree1961 p q h, agree107 p q h]
theorem nonnegative1962 (p : Pattern) : 0 ≤ d1962 p :=
  nonnegative_ite (p 225) (nonnegative1961 p) (nonnegative107 p)
def d1963 (p : Pattern) : Int := if p 247 then d9 p else d5 p
theorem agree1963 (p q : Pattern) (h : Agree support p q) : d1963 p = d1963 q := by
  simp only [d1963, h 247 (by decide), agree9 p q h, agree5 p q h]
theorem nonnegative1963 (p : Pattern) : 0 ≤ d1963 p :=
  nonnegative_ite (p 247) (nonnegative9 p) (nonnegative5 p)
def d1964 (p : Pattern) : Int := if p 246 then d23 p else d1963 p
theorem agree1964 (p q : Pattern) (h : Agree support p q) : d1964 p = d1964 q := by
  simp only [d1964, h 246 (by decide), agree23 p q h, agree1963 p q h]
theorem nonnegative1964 (p : Pattern) : 0 ≤ d1964 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative1963 p)
def d1965 (p : Pattern) : Int := if p 225 then d348 p else d1964 p
theorem agree1965 (p q : Pattern) (h : Agree support p q) : d1965 p = d1965 q := by
  simp only [d1965, h 225 (by decide), agree348 p q h, agree1964 p q h]
theorem nonnegative1965 (p : Pattern) : 0 ≤ d1965 p :=
  nonnegative_ite (p 225) (nonnegative348 p) (nonnegative1964 p)
def d1966 (p : Pattern) : Int := if p 224 then d1965 p else d1962 p
theorem agree1966 (p q : Pattern) (h : Agree support p q) : d1966 p = d1966 q := by
  simp only [d1966, h 224 (by decide), agree1965 p q h, agree1962 p q h]
theorem nonnegative1966 (p : Pattern) : 0 ≤ d1966 p :=
  nonnegative_ite (p 224) (nonnegative1965 p) (nonnegative1962 p)
def d1967 (p : Pattern) : Int := if p 204 then d12 p else d1966 p
theorem agree1967 (p q : Pattern) (h : Agree support p q) : d1967 p = d1967 q := by
  simp only [d1967, h 204 (by decide), agree12 p q h, agree1966 p q h]
theorem nonnegative1967 (p : Pattern) : 0 ≤ d1967 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative1966 p)
def d1968 (p : Pattern) : Int := if p 182 then d1967 p else d108 p
theorem agree1968 (p q : Pattern) (h : Agree support p q) : d1968 p = d1968 q := by
  simp only [d1968, h 182 (by decide), agree1967 p q h, agree108 p q h]
theorem nonnegative1968 (p : Pattern) : 0 ≤ d1968 p :=
  nonnegative_ite (p 182) (nonnegative1967 p) (nonnegative108 p)
def d1969 (p : Pattern) : Int := if p 163 then d1968 p else d1959 p
theorem agree1969 (p q : Pattern) (h : Agree support p q) : d1969 p = d1969 q := by
  simp only [d1969, h 163 (by decide), agree1968 p q h, agree1959 p q h]
theorem nonnegative1969 (p : Pattern) : 0 ≤ d1969 p :=
  nonnegative_ite (p 163) (nonnegative1968 p) (nonnegative1959 p)
def d1970 (p : Pattern) : Int := if p 162 then d1969 p else d1954 p
theorem agree1970 (p q : Pattern) (h : Agree support p q) : d1970 p = d1970 q := by
  simp only [d1970, h 162 (by decide), agree1969 p q h, agree1954 p q h]
theorem nonnegative1970 (p : Pattern) : 0 ≤ d1970 p :=
  nonnegative_ite (p 162) (nonnegative1969 p) (nonnegative1954 p)
def d1971 (p : Pattern) : Int := if p 162 then d1888 p else d1969 p
theorem agree1971 (p q : Pattern) (h : Agree support p q) : d1971 p = d1971 q := by
  simp only [d1971, h 162 (by decide), agree1888 p q h, agree1969 p q h]
theorem nonnegative1971 (p : Pattern) : 0 ≤ d1971 p :=
  nonnegative_ite (p 162) (nonnegative1888 p) (nonnegative1969 p)
def d1972 (p : Pattern) : Int := if p 161 then d1971 p else d1970 p
theorem agree1972 (p q : Pattern) (h : Agree support p q) : d1972 p = d1972 q := by
  simp only [d1972, h 161 (by decide), agree1971 p q h, agree1970 p q h]
theorem nonnegative1972 (p : Pattern) : 0 ≤ d1972 p :=
  nonnegative_ite (p 161) (nonnegative1971 p) (nonnegative1970 p)
def d1973 (p : Pattern) : Int := if p 182 then d1899 p else d117 p
theorem agree1973 (p q : Pattern) (h : Agree support p q) : d1973 p = d1973 q := by
  simp only [d1973, h 182 (by decide), agree1899 p q h, agree117 p q h]
theorem nonnegative1973 (p : Pattern) : 0 ≤ d1973 p :=
  nonnegative_ite (p 182) (nonnegative1899 p) (nonnegative117 p)
def d1974 (p : Pattern) : Int := if p 182 then d1906 p else d121 p
theorem agree1974 (p q : Pattern) (h : Agree support p q) : d1974 p = d1974 q := by
  simp only [d1974, h 182 (by decide), agree1906 p q h, agree121 p q h]
theorem nonnegative1974 (p : Pattern) : 0 ≤ d1974 p :=
  nonnegative_ite (p 182) (nonnegative1906 p) (nonnegative121 p)
def d1975 (p : Pattern) : Int := if p 163 then d1974 p else d1973 p
theorem agree1975 (p q : Pattern) (h : Agree support p q) : d1975 p = d1975 q := by
  simp only [d1975, h 163 (by decide), agree1974 p q h, agree1973 p q h]
theorem nonnegative1975 (p : Pattern) : 0 ≤ d1975 p :=
  nonnegative_ite (p 163) (nonnegative1974 p) (nonnegative1973 p)
def d1976 (p : Pattern) : Int := if p 162 then d12 p else d1975 p
theorem agree1976 (p q : Pattern) (h : Agree support p q) : d1976 p = d1976 q := by
  simp only [d1976, h 162 (by decide), agree12 p q h, agree1975 p q h]
theorem nonnegative1976 (p : Pattern) : 0 ≤ d1976 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1975 p)
def d1977 (p : Pattern) : Int := if p 161 then d12 p else d1976 p
theorem agree1977 (p q : Pattern) (h : Agree support p q) : d1977 p = d1977 q := by
  simp only [d1977, h 161 (by decide), agree12 p q h, agree1976 p q h]
theorem nonnegative1977 (p : Pattern) : 0 ≤ d1977 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1976 p)
def d1978 (p : Pattern) : Int := if p 160 then d1977 p else d1972 p
theorem agree1978 (p q : Pattern) (h : Agree support p q) : d1978 p = d1978 q := by
  simp only [d1978, h 160 (by decide), agree1977 p q h, agree1972 p q h]
theorem nonnegative1978 (p : Pattern) : 0 ≤ d1978 p :=
  nonnegative_ite (p 160) (nonnegative1977 p) (nonnegative1972 p)
def d1979 (p : Pattern) : Int := if p 163 then d1973 p else d1953 p
theorem agree1979 (p q : Pattern) (h : Agree support p q) : d1979 p = d1979 q := by
  simp only [d1979, h 163 (by decide), agree1973 p q h, agree1953 p q h]
theorem nonnegative1979 (p : Pattern) : 0 ≤ d1979 p :=
  nonnegative_ite (p 163) (nonnegative1973 p) (nonnegative1953 p)
def d1980 (p : Pattern) : Int := if p 163 then d1754 p else d1968 p
theorem agree1980 (p q : Pattern) (h : Agree support p q) : d1980 p = d1980 q := by
  simp only [d1980, h 163 (by decide), agree1754 p q h, agree1968 p q h]
theorem nonnegative1980 (p : Pattern) : 0 ≤ d1980 p :=
  nonnegative_ite (p 163) (nonnegative1754 p) (nonnegative1968 p)
def d1981 (p : Pattern) : Int := if p 162 then d1980 p else d1979 p
theorem agree1981 (p q : Pattern) (h : Agree support p q) : d1981 p = d1981 q := by
  simp only [d1981, h 162 (by decide), agree1980 p q h, agree1979 p q h]
theorem nonnegative1981 (p : Pattern) : 0 ≤ d1981 p :=
  nonnegative_ite (p 162) (nonnegative1980 p) (nonnegative1979 p)
def d1982 (p : Pattern) : Int := if p 163 then d1756 p else d1968 p
theorem agree1982 (p q : Pattern) (h : Agree support p q) : d1982 p = d1982 q := by
  simp only [d1982, h 163 (by decide), agree1756 p q h, agree1968 p q h]
theorem nonnegative1982 (p : Pattern) : 0 ≤ d1982 p :=
  nonnegative_ite (p 163) (nonnegative1756 p) (nonnegative1968 p)
def d1983 (p : Pattern) : Int := if p 162 then d12 p else d1982 p
theorem agree1983 (p q : Pattern) (h : Agree support p q) : d1983 p = d1983 q := by
  simp only [d1983, h 162 (by decide), agree12 p q h, agree1982 p q h]
theorem nonnegative1983 (p : Pattern) : 0 ≤ d1983 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1982 p)
def d1984 (p : Pattern) : Int := if p 161 then d1983 p else d1981 p
theorem agree1984 (p q : Pattern) (h : Agree support p q) : d1984 p = d1984 q := by
  simp only [d1984, h 161 (by decide), agree1983 p q h, agree1981 p q h]
theorem nonnegative1984 (p : Pattern) : 0 ≤ d1984 p :=
  nonnegative_ite (p 161) (nonnegative1983 p) (nonnegative1981 p)
def d1985 (p : Pattern) : Int := if p 163 then d12 p else d1974 p
theorem agree1985 (p q : Pattern) (h : Agree support p q) : d1985 p = d1985 q := by
  simp only [d1985, h 163 (by decide), agree12 p q h, agree1974 p q h]
theorem nonnegative1985 (p : Pattern) : 0 ≤ d1985 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1974 p)
def d1986 (p : Pattern) : Int := if p 162 then d12 p else d1985 p
theorem agree1986 (p q : Pattern) (h : Agree support p q) : d1986 p = d1986 q := by
  simp only [d1986, h 162 (by decide), agree12 p q h, agree1985 p q h]
theorem nonnegative1986 (p : Pattern) : 0 ≤ d1986 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1985 p)
def d1987 (p : Pattern) : Int := if p 161 then d12 p else d1986 p
theorem agree1987 (p q : Pattern) (h : Agree support p q) : d1987 p = d1987 q := by
  simp only [d1987, h 161 (by decide), agree12 p q h, agree1986 p q h]
theorem nonnegative1987 (p : Pattern) : 0 ≤ d1987 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1986 p)
def d1988 (p : Pattern) : Int := if p 160 then d1987 p else d1984 p
theorem agree1988 (p q : Pattern) (h : Agree support p q) : d1988 p = d1988 q := by
  simp only [d1988, h 160 (by decide), agree1987 p q h, agree1984 p q h]
theorem nonnegative1988 (p : Pattern) : 0 ≤ d1988 p :=
  nonnegative_ite (p 160) (nonnegative1987 p) (nonnegative1984 p)
def d1989 (p : Pattern) : Int := if p 141 then d1988 p else d1978 p
theorem agree1989 (p q : Pattern) (h : Agree support p q) : d1989 p = d1989 q := by
  simp only [d1989, h 141 (by decide), agree1988 p q h, agree1978 p q h]
theorem nonnegative1989 (p : Pattern) : 0 ≤ d1989 p :=
  nonnegative_ite (p 141) (nonnegative1988 p) (nonnegative1978 p)
def d1990 (p : Pattern) : Int := if p 138 then d1989 p else d1938 p
theorem agree1990 (p q : Pattern) (h : Agree support p q) : d1990 p = d1990 q := by
  simp only [d1990, h 138 (by decide), agree1989 p q h, agree1938 p q h]
theorem nonnegative1990 (p : Pattern) : 0 ≤ d1990 p :=
  nonnegative_ite (p 138) (nonnegative1989 p) (nonnegative1938 p)
def d1991 (p : Pattern) : Int := if p 162 then d12 p else d1888 p
theorem agree1991 (p q : Pattern) (h : Agree support p q) : d1991 p = d1991 q := by
  simp only [d1991, h 162 (by decide), agree12 p q h, agree1888 p q h]
theorem nonnegative1991 (p : Pattern) : 0 ≤ d1991 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1888 p)
def d1992 (p : Pattern) : Int := if p 161 then d12 p else d1991 p
theorem agree1992 (p q : Pattern) (h : Agree support p q) : d1992 p = d1992 q := by
  simp only [d1992, h 161 (by decide), agree12 p q h, agree1991 p q h]
theorem nonnegative1992 (p : Pattern) : 0 ≤ d1992 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1991 p)
def d1993 (p : Pattern) : Int := if p 160 then d12 p else d1992 p
theorem agree1993 (p q : Pattern) (h : Agree support p q) : d1993 p = d1993 q := by
  simp only [d1993, h 160 (by decide), agree12 p q h, agree1992 p q h]
theorem nonnegative1993 (p : Pattern) : 0 ≤ d1993 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative1992 p)
def d1994 (p : Pattern) : Int := if p 141 then d12 p else d1993 p
theorem agree1994 (p q : Pattern) (h : Agree support p q) : d1994 p = d1994 q := by
  simp only [d1994, h 141 (by decide), agree12 p q h, agree1993 p q h]
theorem nonnegative1994 (p : Pattern) : 0 ≤ d1994 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative1993 p)
def d1995 (p : Pattern) : Int := if p 138 then d1994 p else d1989 p
theorem agree1995 (p q : Pattern) (h : Agree support p q) : d1995 p = d1995 q := by
  simp only [d1995, h 138 (by decide), agree1994 p q h, agree1989 p q h]
theorem nonnegative1995 (p : Pattern) : 0 ≤ d1995 p :=
  nonnegative_ite (p 138) (nonnegative1994 p) (nonnegative1989 p)
def d1996 (p : Pattern) : Int := if p 116 then d1995 p else d1990 p
theorem agree1996 (p q : Pattern) (h : Agree support p q) : d1996 p = d1996 q := by
  simp only [d1996, h 116 (by decide), agree1995 p q h, agree1990 p q h]
theorem nonnegative1996 (p : Pattern) : 0 ≤ d1996 p :=
  nonnegative_ite (p 116) (nonnegative1995 p) (nonnegative1990 p)
def d1997 (p : Pattern) : Int := if p 162 then d1886 p else d1878 p
theorem agree1997 (p q : Pattern) (h : Agree support p q) : d1997 p = d1997 q := by
  simp only [d1997, h 162 (by decide), agree1886 p q h, agree1878 p q h]
theorem nonnegative1997 (p : Pattern) : 0 ≤ d1997 p :=
  nonnegative_ite (p 162) (nonnegative1886 p) (nonnegative1878 p)
def d1998 (p : Pattern) : Int := if p 161 then d1889 p else d1997 p
theorem agree1998 (p q : Pattern) (h : Agree support p q) : d1998 p = d1998 q := by
  simp only [d1998, h 161 (by decide), agree1889 p q h, agree1997 p q h]
theorem nonnegative1998 (p : Pattern) : 0 ≤ d1998 p :=
  nonnegative_ite (p 161) (nonnegative1889 p) (nonnegative1997 p)
def d1999 (p : Pattern) : Int := if p 160 then d1914 p else d1998 p
theorem agree1999 (p q : Pattern) (h : Agree support p q) : d1999 p = d1999 q := by
  simp only [d1999, h 160 (by decide), agree1914 p q h, agree1998 p q h]
theorem nonnegative1999 (p : Pattern) : 0 ≤ d1999 p :=
  nonnegative_ite (p 160) (nonnegative1914 p) (nonnegative1998 p)
def d2000 (p : Pattern) : Int := if p 163 then d1923 p else d1878 p
theorem agree2000 (p q : Pattern) (h : Agree support p q) : d2000 p = d2000 q := by
  simp only [d2000, h 163 (by decide), agree1923 p q h, agree1878 p q h]
theorem nonnegative2000 (p : Pattern) : 0 ≤ d2000 p :=
  nonnegative_ite (p 163) (nonnegative1923 p) (nonnegative1878 p)
def d2001 (p : Pattern) : Int := if p 162 then d1925 p else d2000 p
theorem agree2001 (p q : Pattern) (h : Agree support p q) : d2001 p = d2001 q := by
  simp only [d2001, h 162 (by decide), agree1925 p q h, agree2000 p q h]
theorem nonnegative2001 (p : Pattern) : 0 ≤ d2001 p :=
  nonnegative_ite (p 162) (nonnegative1925 p) (nonnegative2000 p)
def d2002 (p : Pattern) : Int := if p 161 then d1928 p else d2001 p
theorem agree2002 (p q : Pattern) (h : Agree support p q) : d2002 p = d2002 q := by
  simp only [d2002, h 161 (by decide), agree1928 p q h, agree2001 p q h]
theorem nonnegative2002 (p : Pattern) : 0 ≤ d2002 p :=
  nonnegative_ite (p 161) (nonnegative1928 p) (nonnegative2001 p)
def d2003 (p : Pattern) : Int := if p 160 then d1936 p else d2002 p
theorem agree2003 (p q : Pattern) (h : Agree support p q) : d2003 p = d2003 q := by
  simp only [d2003, h 160 (by decide), agree1936 p q h, agree2002 p q h]
theorem nonnegative2003 (p : Pattern) : 0 ≤ d2003 p :=
  nonnegative_ite (p 160) (nonnegative1936 p) (nonnegative2002 p)
def d2004 (p : Pattern) : Int := if p 141 then d2003 p else d1999 p
theorem agree2004 (p q : Pattern) (h : Agree support p q) : d2004 p = d2004 q := by
  simp only [d2004, h 141 (by decide), agree2003 p q h, agree1999 p q h]
theorem nonnegative2004 (p : Pattern) : 0 ≤ d2004 p :=
  nonnegative_ite (p 141) (nonnegative2003 p) (nonnegative1999 p)
def d2005 (p : Pattern) : Int := if p 138 then d1989 p else d2004 p
theorem agree2005 (p q : Pattern) (h : Agree support p q) : d2005 p = d2005 q := by
  simp only [d2005, h 138 (by decide), agree1989 p q h, agree2004 p q h]
theorem nonnegative2005 (p : Pattern) : 0 ≤ d2005 p :=
  nonnegative_ite (p 138) (nonnegative1989 p) (nonnegative2004 p)
def d2006 (p : Pattern) : Int := if p 138 then d12 p else d1989 p
theorem agree2006 (p q : Pattern) (h : Agree support p q) : d2006 p = d2006 q := by
  simp only [d2006, h 138 (by decide), agree12 p q h, agree1989 p q h]
theorem nonnegative2006 (p : Pattern) : 0 ≤ d2006 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1989 p)
def d2007 (p : Pattern) : Int := if p 116 then d2006 p else d2005 p
theorem agree2007 (p q : Pattern) (h : Agree support p q) : d2007 p = d2007 q := by
  simp only [d2007, h 116 (by decide), agree2006 p q h, agree2005 p q h]
theorem nonnegative2007 (p : Pattern) : 0 ≤ d2007 p :=
  nonnegative_ite (p 116) (nonnegative2006 p) (nonnegative2005 p)
def d2008 (p : Pattern) : Int := if p 115 then d2007 p else d1996 p
theorem agree2008 (p q : Pattern) (h : Agree support p q) : d2008 p = d2008 q := by
  simp only [d2008, h 115 (by decide), agree2007 p q h, agree1996 p q h]
theorem nonnegative2008 (p : Pattern) : 0 ≤ d2008 p :=
  nonnegative_ite (p 115) (nonnegative2007 p) (nonnegative1996 p)
def d2009 (p : Pattern) : Int := if p 71 then d2008 p else d1849 p
theorem agree2009 (p q : Pattern) (h : Agree support p q) : d2009 p = d2009 q := by
  simp only [d2009, h 71 (by decide), agree2008 p q h, agree1849 p q h]
theorem nonnegative2009 (p : Pattern) : 0 ≤ d2009 p :=
  nonnegative_ite (p 71) (nonnegative2008 p) (nonnegative1849 p)
def d2010 (p : Pattern) : Int := if p 49 then d2009 p else d1870 p
theorem agree2010 (p q : Pattern) (h : Agree support p q) : d2010 p = d2010 q := by
  simp only [d2010, h 49 (by decide), agree2009 p q h, agree1870 p q h]
theorem nonnegative2010 (p : Pattern) : 0 ≤ d2010 p :=
  nonnegative_ite (p 49) (nonnegative2009 p) (nonnegative1870 p)
def d2011 (p : Pattern) : Int := if p 225 then d1795 p else d18 p
theorem agree2011 (p q : Pattern) (h : Agree support p q) : d2011 p = d2011 q := by
  simp only [d2011, h 225 (by decide), agree1795 p q h, agree18 p q h]
theorem nonnegative2011 (p : Pattern) : 0 ≤ d2011 p :=
  nonnegative_ite (p 225) (nonnegative1795 p) (nonnegative18 p)
def d2012 (p : Pattern) : Int := if p 224 then d1795 p else d2011 p
theorem agree2012 (p q : Pattern) (h : Agree support p q) : d2012 p = d2012 q := by
  simp only [d2012, h 224 (by decide), agree1795 p q h, agree2011 p q h]
theorem nonnegative2012 (p : Pattern) : 0 ≤ d2012 p :=
  nonnegative_ite (p 224) (nonnegative1795 p) (nonnegative2011 p)
def d2013 (p : Pattern) : Int := if p 204 then d12 p else d2012 p
theorem agree2013 (p q : Pattern) (h : Agree support p q) : d2013 p = d2013 q := by
  simp only [d2013, h 204 (by decide), agree12 p q h, agree2012 p q h]
theorem nonnegative2013 (p : Pattern) : 0 ≤ d2013 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2012 p)
def d2014 (p : Pattern) : Int := if p 182 then d2013 p else d19 p
theorem agree2014 (p q : Pattern) (h : Agree support p q) : d2014 p = d2014 q := by
  simp only [d2014, h 182 (by decide), agree2013 p q h, agree19 p q h]
theorem nonnegative2014 (p : Pattern) : 0 ≤ d2014 p :=
  nonnegative_ite (p 182) (nonnegative2013 p) (nonnegative19 p)
def d2015 (p : Pattern) : Int := if p 163 then d2014 p else d1774 p
theorem agree2015 (p q : Pattern) (h : Agree support p q) : d2015 p = d2015 q := by
  simp only [d2015, h 163 (by decide), agree2014 p q h, agree1774 p q h]
theorem nonnegative2015 (p : Pattern) : 0 ≤ d2015 p :=
  nonnegative_ite (p 163) (nonnegative2014 p) (nonnegative1774 p)
def d2016 (p : Pattern) : Int := if p 162 then d2015 p else d1774 p
theorem agree2016 (p q : Pattern) (h : Agree support p q) : d2016 p = d2016 q := by
  simp only [d2016, h 162 (by decide), agree2015 p q h, agree1774 p q h]
theorem nonnegative2016 (p : Pattern) : 0 ≤ d2016 p :=
  nonnegative_ite (p 162) (nonnegative2015 p) (nonnegative1774 p)
def d2017 (p : Pattern) : Int := if p 162 then d1806 p else d2015 p
theorem agree2017 (p q : Pattern) (h : Agree support p q) : d2017 p = d2017 q := by
  simp only [d2017, h 162 (by decide), agree1806 p q h, agree2015 p q h]
theorem nonnegative2017 (p : Pattern) : 0 ≤ d2017 p :=
  nonnegative_ite (p 162) (nonnegative1806 p) (nonnegative2015 p)
def d2018 (p : Pattern) : Int := if p 161 then d2017 p else d2016 p
theorem agree2018 (p q : Pattern) (h : Agree support p q) : d2018 p = d2018 q := by
  simp only [d2018, h 161 (by decide), agree2017 p q h, agree2016 p q h]
theorem nonnegative2018 (p : Pattern) : 0 ≤ d2018 p :=
  nonnegative_ite (p 161) (nonnegative2017 p) (nonnegative2016 p)
def d2019 (p : Pattern) : Int := if p 182 then d1725 p else d32 p
theorem agree2019 (p q : Pattern) (h : Agree support p q) : d2019 p = d2019 q := by
  simp only [d2019, h 182 (by decide), agree1725 p q h, agree32 p q h]
theorem nonnegative2019 (p : Pattern) : 0 ≤ d2019 p :=
  nonnegative_ite (p 182) (nonnegative1725 p) (nonnegative32 p)
def d2020 (p : Pattern) : Int := if p 163 then d2019 p else d1809 p
theorem agree2020 (p q : Pattern) (h : Agree support p q) : d2020 p = d2020 q := by
  simp only [d2020, h 163 (by decide), agree2019 p q h, agree1809 p q h]
theorem nonnegative2020 (p : Pattern) : 0 ≤ d2020 p :=
  nonnegative_ite (p 163) (nonnegative2019 p) (nonnegative1809 p)
def d2021 (p : Pattern) : Int := if p 182 then d1730 p else d32 p
theorem agree2021 (p q : Pattern) (h : Agree support p q) : d2021 p = d2021 q := by
  simp only [d2021, h 182 (by decide), agree1730 p q h, agree32 p q h]
theorem nonnegative2021 (p : Pattern) : 0 ≤ d2021 p :=
  nonnegative_ite (p 182) (nonnegative1730 p) (nonnegative32 p)
def d2022 (p : Pattern) : Int := if p 182 then d12 p else d36 p
theorem agree2022 (p q : Pattern) (h : Agree support p q) : d2022 p = d2022 q := by
  simp only [d2022, h 182 (by decide), agree12 p q h, agree36 p q h]
theorem nonnegative2022 (p : Pattern) : 0 ≤ d2022 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative36 p)
def d2023 (p : Pattern) : Int := if p 163 then d2022 p else d2021 p
theorem agree2023 (p q : Pattern) (h : Agree support p q) : d2023 p = d2023 q := by
  simp only [d2023, h 163 (by decide), agree2022 p q h, agree2021 p q h]
theorem nonnegative2023 (p : Pattern) : 0 ≤ d2023 p :=
  nonnegative_ite (p 163) (nonnegative2022 p) (nonnegative2021 p)
def d2024 (p : Pattern) : Int := if p 162 then d2023 p else d2020 p
theorem agree2024 (p q : Pattern) (h : Agree support p q) : d2024 p = d2024 q := by
  simp only [d2024, h 162 (by decide), agree2023 p q h, agree2020 p q h]
theorem nonnegative2024 (p : Pattern) : 0 ≤ d2024 p :=
  nonnegative_ite (p 162) (nonnegative2023 p) (nonnegative2020 p)
def d2025 (p : Pattern) : Int := if p 163 then d2022 p else d1760 p
theorem agree2025 (p q : Pattern) (h : Agree support p q) : d2025 p = d2025 q := by
  simp only [d2025, h 163 (by decide), agree2022 p q h, agree1760 p q h]
theorem nonnegative2025 (p : Pattern) : 0 ≤ d2025 p :=
  nonnegative_ite (p 163) (nonnegative2022 p) (nonnegative1760 p)
def d2026 (p : Pattern) : Int := if p 162 then d539 p else d2025 p
theorem agree2026 (p q : Pattern) (h : Agree support p q) : d2026 p = d2026 q := by
  simp only [d2026, h 162 (by decide), agree539 p q h, agree2025 p q h]
theorem nonnegative2026 (p : Pattern) : 0 ≤ d2026 p :=
  nonnegative_ite (p 162) (nonnegative539 p) (nonnegative2025 p)
def d2027 (p : Pattern) : Int := if p 161 then d2026 p else d2024 p
theorem agree2027 (p q : Pattern) (h : Agree support p q) : d2027 p = d2027 q := by
  simp only [d2027, h 161 (by decide), agree2026 p q h, agree2024 p q h]
theorem nonnegative2027 (p : Pattern) : 0 ≤ d2027 p :=
  nonnegative_ite (p 161) (nonnegative2026 p) (nonnegative2024 p)
def d2028 (p : Pattern) : Int := if p 160 then d2027 p else d2018 p
theorem agree2028 (p q : Pattern) (h : Agree support p q) : d2028 p = d2028 q := by
  simp only [d2028, h 160 (by decide), agree2027 p q h, agree2018 p q h]
theorem nonnegative2028 (p : Pattern) : 0 ≤ d2028 p :=
  nonnegative_ite (p 160) (nonnegative2027 p) (nonnegative2018 p)
def d2029 (p : Pattern) : Int := if p 225 then d1714 p else d31 p
theorem agree2029 (p q : Pattern) (h : Agree support p q) : d2029 p = d2029 q := by
  simp only [d2029, h 225 (by decide), agree1714 p q h, agree31 p q h]
theorem nonnegative2029 (p : Pattern) : 0 ≤ d2029 p :=
  nonnegative_ite (p 225) (nonnegative1714 p) (nonnegative31 p)
def d2030 (p : Pattern) : Int := if p 224 then d1714 p else d2029 p
theorem agree2030 (p q : Pattern) (h : Agree support p q) : d2030 p = d2030 q := by
  simp only [d2030, h 224 (by decide), agree1714 p q h, agree2029 p q h]
theorem nonnegative2030 (p : Pattern) : 0 ≤ d2030 p :=
  nonnegative_ite (p 224) (nonnegative1714 p) (nonnegative2029 p)
def d2031 (p : Pattern) : Int := if p 204 then d12 p else d2030 p
theorem agree2031 (p q : Pattern) (h : Agree support p q) : d2031 p = d2031 q := by
  simp only [d2031, h 204 (by decide), agree12 p q h, agree2030 p q h]
theorem nonnegative2031 (p : Pattern) : 0 ≤ d2031 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2030 p)
def d2032 (p : Pattern) : Int := if p 182 then d2031 p else d32 p
theorem agree2032 (p q : Pattern) (h : Agree support p q) : d2032 p = d2032 q := by
  simp only [d2032, h 182 (by decide), agree2031 p q h, agree32 p q h]
theorem nonnegative2032 (p : Pattern) : 0 ≤ d2032 p :=
  nonnegative_ite (p 182) (nonnegative2031 p) (nonnegative32 p)
def d2033 (p : Pattern) : Int := if p 163 then d2032 p else d1774 p
theorem agree2033 (p q : Pattern) (h : Agree support p q) : d2033 p = d2033 q := by
  simp only [d2033, h 163 (by decide), agree2032 p q h, agree1774 p q h]
theorem nonnegative2033 (p : Pattern) : 0 ≤ d2033 p :=
  nonnegative_ite (p 163) (nonnegative2032 p) (nonnegative1774 p)
def d2034 (p : Pattern) : Int := if p 163 then d1805 p else d2014 p
theorem agree2034 (p q : Pattern) (h : Agree support p q) : d2034 p = d2034 q := by
  simp only [d2034, h 163 (by decide), agree1805 p q h, agree2014 p q h]
theorem nonnegative2034 (p : Pattern) : 0 ≤ d2034 p :=
  nonnegative_ite (p 163) (nonnegative1805 p) (nonnegative2014 p)
def d2035 (p : Pattern) : Int := if p 162 then d2034 p else d2033 p
theorem agree2035 (p q : Pattern) (h : Agree support p q) : d2035 p = d2035 q := by
  simp only [d2035, h 162 (by decide), agree2034 p q h, agree2033 p q h]
theorem nonnegative2035 (p : Pattern) : 0 ≤ d2035 p :=
  nonnegative_ite (p 162) (nonnegative2034 p) (nonnegative2033 p)
def d2036 (p : Pattern) : Int := if p 163 then d1754 p else d2014 p
theorem agree2036 (p q : Pattern) (h : Agree support p q) : d2036 p = d2036 q := by
  simp only [d2036, h 163 (by decide), agree1754 p q h, agree2014 p q h]
theorem nonnegative2036 (p : Pattern) : 0 ≤ d2036 p :=
  nonnegative_ite (p 163) (nonnegative1754 p) (nonnegative2014 p)
def d2037 (p : Pattern) : Int := if p 162 then d1757 p else d2036 p
theorem agree2037 (p q : Pattern) (h : Agree support p q) : d2037 p = d2037 q := by
  simp only [d2037, h 162 (by decide), agree1757 p q h, agree2036 p q h]
theorem nonnegative2037 (p : Pattern) : 0 ≤ d2037 p :=
  nonnegative_ite (p 162) (nonnegative1757 p) (nonnegative2036 p)
def d2038 (p : Pattern) : Int := if p 161 then d2037 p else d2035 p
theorem agree2038 (p q : Pattern) (h : Agree support p q) : d2038 p = d2038 q := by
  simp only [d2038, h 161 (by decide), agree2037 p q h, agree2035 p q h]
theorem nonnegative2038 (p : Pattern) : 0 ≤ d2038 p :=
  nonnegative_ite (p 161) (nonnegative2037 p) (nonnegative2035 p)
def d2039 (p : Pattern) : Int := if p 163 then d1732 p else d2019 p
theorem agree2039 (p q : Pattern) (h : Agree support p q) : d2039 p = d2039 q := by
  simp only [d2039, h 163 (by decide), agree1732 p q h, agree2019 p q h]
theorem nonnegative2039 (p : Pattern) : 0 ≤ d2039 p :=
  nonnegative_ite (p 163) (nonnegative1732 p) (nonnegative2019 p)
end NetHack.Sokoban22Refined85
