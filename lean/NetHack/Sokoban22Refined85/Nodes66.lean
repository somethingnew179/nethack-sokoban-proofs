/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes65
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d7920 (p : Pattern) : Int := if p 225 then d3279 p else d3461 p
theorem agree7920 (p q : Pattern) (h : Agree support p q) : d7920 p = d7920 q := by
  simp only [d7920, h 225 (by decide), agree3279 p q h, agree3461 p q h]
theorem nonnegative7920 (p : Pattern) : 0 ≤ d7920 p :=
  nonnegative_ite (p 225) (nonnegative3279 p) (nonnegative3461 p)
def d7921 (p : Pattern) : Int := if p 224 then d7920 p else d7706 p
theorem agree7921 (p q : Pattern) (h : Agree support p q) : d7921 p = d7921 q := by
  simp only [d7921, h 224 (by decide), agree7920 p q h, agree7706 p q h]
theorem nonnegative7921 (p : Pattern) : 0 ≤ d7921 p :=
  nonnegative_ite (p 224) (nonnegative7920 p) (nonnegative7706 p)
def d7922 (p : Pattern) : Int := if p 204 then d7921 p else d3239 p
theorem agree7922 (p q : Pattern) (h : Agree support p q) : d7922 p = d7922 q := by
  simp only [d7922, h 204 (by decide), agree7921 p q h, agree3239 p q h]
theorem nonnegative7922 (p : Pattern) : 0 ≤ d7922 p :=
  nonnegative_ite (p 204) (nonnegative7921 p) (nonnegative3239 p)
def d7923 (p : Pattern) : Int := if p 204 then d12 p else d7670 p
theorem agree7923 (p q : Pattern) (h : Agree support p q) : d7923 p = d7923 q := by
  simp only [d7923, h 204 (by decide), agree12 p q h, agree7670 p q h]
theorem nonnegative7923 (p : Pattern) : 0 ≤ d7923 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7670 p)
def d7924 (p : Pattern) : Int := if p 182 then d7923 p else d7922 p
theorem agree7924 (p q : Pattern) (h : Agree support p q) : d7924 p = d7924 q := by
  simp only [d7924, h 182 (by decide), agree7923 p q h, agree7922 p q h]
theorem nonnegative7924 (p : Pattern) : 0 ≤ d7924 p :=
  nonnegative_ite (p 182) (nonnegative7923 p) (nonnegative7922 p)
def d7925 (p : Pattern) : Int := if p 163 then d7924 p else d7756 p
theorem agree7925 (p q : Pattern) (h : Agree support p q) : d7925 p = d7925 q := by
  simp only [d7925, h 163 (by decide), agree7924 p q h, agree7756 p q h]
theorem nonnegative7925 (p : Pattern) : 0 ≤ d7925 p :=
  nonnegative_ite (p 163) (nonnegative7924 p) (nonnegative7756 p)
def d7926 (p : Pattern) : Int := if p 162 then d7925 p else d7756 p
theorem agree7926 (p q : Pattern) (h : Agree support p q) : d7926 p = d7926 q := by
  simp only [d7926, h 162 (by decide), agree7925 p q h, agree7756 p q h]
theorem nonnegative7926 (p : Pattern) : 0 ≤ d7926 p :=
  nonnegative_ite (p 162) (nonnegative7925 p) (nonnegative7756 p)
def d7927 (p : Pattern) : Int := if p 162 then d7771 p else d7925 p
theorem agree7927 (p q : Pattern) (h : Agree support p q) : d7927 p = d7927 q := by
  simp only [d7927, h 162 (by decide), agree7771 p q h, agree7925 p q h]
theorem nonnegative7927 (p : Pattern) : 0 ≤ d7927 p :=
  nonnegative_ite (p 162) (nonnegative7771 p) (nonnegative7925 p)
def d7928 (p : Pattern) : Int := if p 161 then d7927 p else d7926 p
theorem agree7928 (p q : Pattern) (h : Agree support p q) : d7928 p = d7928 q := by
  simp only [d7928, h 161 (by decide), agree7927 p q h, agree7926 p q h]
theorem nonnegative7928 (p : Pattern) : 0 ≤ d7928 p :=
  nonnegative_ite (p 161) (nonnegative7927 p) (nonnegative7926 p)
def d7929 (p : Pattern) : Int := if p 182 then d7699 p else d7740 p
theorem agree7929 (p q : Pattern) (h : Agree support p q) : d7929 p = d7929 q := by
  simp only [d7929, h 182 (by decide), agree7699 p q h, agree7740 p q h]
theorem nonnegative7929 (p : Pattern) : 0 ≤ d7929 p :=
  nonnegative_ite (p 182) (nonnegative7699 p) (nonnegative7740 p)
def d7930 (p : Pattern) : Int := if p 163 then d7929 p else d7774 p
theorem agree7930 (p q : Pattern) (h : Agree support p q) : d7930 p = d7930 q := by
  simp only [d7930, h 163 (by decide), agree7929 p q h, agree7774 p q h]
theorem nonnegative7930 (p : Pattern) : 0 ≤ d7930 p :=
  nonnegative_ite (p 163) (nonnegative7929 p) (nonnegative7774 p)
def d7931 (p : Pattern) : Int := if p 182 then d7704 p else d7740 p
theorem agree7931 (p q : Pattern) (h : Agree support p q) : d7931 p = d7931 q := by
  simp only [d7931, h 182 (by decide), agree7704 p q h, agree7740 p q h]
theorem nonnegative7931 (p : Pattern) : 0 ≤ d7931 p :=
  nonnegative_ite (p 182) (nonnegative7704 p) (nonnegative7740 p)
def d7932 (p : Pattern) : Int := if p 182 then d12 p else d7775 p
theorem agree7932 (p q : Pattern) (h : Agree support p q) : d7932 p = d7932 q := by
  simp only [d7932, h 182 (by decide), agree12 p q h, agree7775 p q h]
theorem nonnegative7932 (p : Pattern) : 0 ≤ d7932 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7775 p)
def d7933 (p : Pattern) : Int := if p 163 then d7932 p else d7931 p
theorem agree7933 (p q : Pattern) (h : Agree support p q) : d7933 p = d7933 q := by
  simp only [d7933, h 163 (by decide), agree7932 p q h, agree7931 p q h]
theorem nonnegative7933 (p : Pattern) : 0 ≤ d7933 p :=
  nonnegative_ite (p 163) (nonnegative7932 p) (nonnegative7931 p)
def d7934 (p : Pattern) : Int := if p 162 then d7933 p else d7930 p
theorem agree7934 (p q : Pattern) (h : Agree support p q) : d7934 p = d7934 q := by
  simp only [d7934, h 162 (by decide), agree7933 p q h, agree7930 p q h]
theorem nonnegative7934 (p : Pattern) : 0 ≤ d7934 p :=
  nonnegative_ite (p 162) (nonnegative7933 p) (nonnegative7930 p)
def d7935 (p : Pattern) : Int := if p 163 then d7932 p else d7741 p
theorem agree7935 (p q : Pattern) (h : Agree support p q) : d7935 p = d7935 q := by
  simp only [d7935, h 163 (by decide), agree7932 p q h, agree7741 p q h]
theorem nonnegative7935 (p : Pattern) : 0 ≤ d7935 p :=
  nonnegative_ite (p 163) (nonnegative7932 p) (nonnegative7741 p)
def d7936 (p : Pattern) : Int := if p 162 then d7748 p else d7935 p
theorem agree7936 (p q : Pattern) (h : Agree support p q) : d7936 p = d7936 q := by
  simp only [d7936, h 162 (by decide), agree7748 p q h, agree7935 p q h]
theorem nonnegative7936 (p : Pattern) : 0 ≤ d7936 p :=
  nonnegative_ite (p 162) (nonnegative7748 p) (nonnegative7935 p)
def d7937 (p : Pattern) : Int := if p 161 then d7936 p else d7934 p
theorem agree7937 (p q : Pattern) (h : Agree support p q) : d7937 p = d7937 q := by
  simp only [d7937, h 161 (by decide), agree7936 p q h, agree7934 p q h]
theorem nonnegative7937 (p : Pattern) : 0 ≤ d7937 p :=
  nonnegative_ite (p 161) (nonnegative7936 p) (nonnegative7934 p)
def d7938 (p : Pattern) : Int := if p 160 then d7937 p else d7928 p
theorem agree7938 (p q : Pattern) (h : Agree support p q) : d7938 p = d7938 q := by
  simp only [d7938, h 160 (by decide), agree7937 p q h, agree7928 p q h]
theorem nonnegative7938 (p : Pattern) : 0 ≤ d7938 p :=
  nonnegative_ite (p 160) (nonnegative7937 p) (nonnegative7928 p)
def d7939 (p : Pattern) : Int := if p 225 then d3461 p else d3253 p
theorem agree7939 (p q : Pattern) (h : Agree support p q) : d7939 p = d7939 q := by
  simp only [d7939, h 225 (by decide), agree3461 p q h, agree3253 p q h]
theorem nonnegative7939 (p : Pattern) : 0 ≤ d7939 p :=
  nonnegative_ite (p 225) (nonnegative3461 p) (nonnegative3253 p)
def d7940 (p : Pattern) : Int := if p 224 then d7939 p else d7692 p
theorem agree7940 (p q : Pattern) (h : Agree support p q) : d7940 p = d7940 q := by
  simp only [d7940, h 224 (by decide), agree7939 p q h, agree7692 p q h]
theorem nonnegative7940 (p : Pattern) : 0 ≤ d7940 p :=
  nonnegative_ite (p 224) (nonnegative7939 p) (nonnegative7692 p)
def d7941 (p : Pattern) : Int := if p 204 then d7940 p else d3250 p
theorem agree7941 (p q : Pattern) (h : Agree support p q) : d7941 p = d7941 q := by
  simp only [d7941, h 204 (by decide), agree7940 p q h, agree3250 p q h]
theorem nonnegative7941 (p : Pattern) : 0 ≤ d7941 p :=
  nonnegative_ite (p 204) (nonnegative7940 p) (nonnegative3250 p)
def d7942 (p : Pattern) : Int := if p 204 then d12 p else d7721 p
theorem agree7942 (p q : Pattern) (h : Agree support p q) : d7942 p = d7942 q := by
  simp only [d7942, h 204 (by decide), agree12 p q h, agree7721 p q h]
theorem nonnegative7942 (p : Pattern) : 0 ≤ d7942 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7721 p)
def d7943 (p : Pattern) : Int := if p 182 then d7942 p else d7941 p
theorem agree7943 (p q : Pattern) (h : Agree support p q) : d7943 p = d7943 q := by
  simp only [d7943, h 182 (by decide), agree7942 p q h, agree7941 p q h]
theorem nonnegative7943 (p : Pattern) : 0 ≤ d7943 p :=
  nonnegative_ite (p 182) (nonnegative7942 p) (nonnegative7941 p)
def d7944 (p : Pattern) : Int := if p 163 then d7943 p else d7756 p
theorem agree7944 (p q : Pattern) (h : Agree support p q) : d7944 p = d7944 q := by
  simp only [d7944, h 163 (by decide), agree7943 p q h, agree7756 p q h]
theorem nonnegative7944 (p : Pattern) : 0 ≤ d7944 p :=
  nonnegative_ite (p 163) (nonnegative7943 p) (nonnegative7756 p)
def d7945 (p : Pattern) : Int := if p 163 then d7770 p else d7924 p
theorem agree7945 (p q : Pattern) (h : Agree support p q) : d7945 p = d7945 q := by
  simp only [d7945, h 163 (by decide), agree7770 p q h, agree7924 p q h]
theorem nonnegative7945 (p : Pattern) : 0 ≤ d7945 p :=
  nonnegative_ite (p 163) (nonnegative7770 p) (nonnegative7924 p)
def d7946 (p : Pattern) : Int := if p 162 then d7945 p else d7944 p
theorem agree7946 (p q : Pattern) (h : Agree support p q) : d7946 p = d7946 q := by
  simp only [d7946, h 162 (by decide), agree7945 p q h, agree7944 p q h]
theorem nonnegative7946 (p : Pattern) : 0 ≤ d7946 p :=
  nonnegative_ite (p 162) (nonnegative7945 p) (nonnegative7944 p)
def d7947 (p : Pattern) : Int := if p 163 then d7733 p else d7924 p
theorem agree7947 (p q : Pattern) (h : Agree support p q) : d7947 p = d7947 q := by
  simp only [d7947, h 163 (by decide), agree7733 p q h, agree7924 p q h]
theorem nonnegative7947 (p : Pattern) : 0 ≤ d7947 p :=
  nonnegative_ite (p 163) (nonnegative7733 p) (nonnegative7924 p)
def d7948 (p : Pattern) : Int := if p 162 then d7737 p else d7947 p
theorem agree7948 (p q : Pattern) (h : Agree support p q) : d7948 p = d7948 q := by
  simp only [d7948, h 162 (by decide), agree7737 p q h, agree7947 p q h]
theorem nonnegative7948 (p : Pattern) : 0 ≤ d7948 p :=
  nonnegative_ite (p 162) (nonnegative7737 p) (nonnegative7947 p)
def d7949 (p : Pattern) : Int := if p 161 then d7948 p else d7946 p
theorem agree7949 (p q : Pattern) (h : Agree support p q) : d7949 p = d7949 q := by
  simp only [d7949, h 161 (by decide), agree7948 p q h, agree7946 p q h]
theorem nonnegative7949 (p : Pattern) : 0 ≤ d7949 p :=
  nonnegative_ite (p 161) (nonnegative7948 p) (nonnegative7946 p)
def d7950 (p : Pattern) : Int := if p 163 then d7710 p else d7929 p
theorem agree7950 (p q : Pattern) (h : Agree support p q) : d7950 p = d7950 q := by
  simp only [d7950, h 163 (by decide), agree7710 p q h, agree7929 p q h]
theorem nonnegative7950 (p : Pattern) : 0 ≤ d7950 p :=
  nonnegative_ite (p 163) (nonnegative7710 p) (nonnegative7929 p)
def d7951 (p : Pattern) : Int := if p 163 then d7747 p else d7932 p
theorem agree7951 (p q : Pattern) (h : Agree support p q) : d7951 p = d7951 q := by
  simp only [d7951, h 163 (by decide), agree7747 p q h, agree7932 p q h]
theorem nonnegative7951 (p : Pattern) : 0 ≤ d7951 p :=
  nonnegative_ite (p 163) (nonnegative7747 p) (nonnegative7932 p)
def d7952 (p : Pattern) : Int := if p 162 then d7951 p else d7950 p
theorem agree7952 (p q : Pattern) (h : Agree support p q) : d7952 p = d7952 q := by
  simp only [d7952, h 162 (by decide), agree7951 p q h, agree7950 p q h]
theorem nonnegative7952 (p : Pattern) : 0 ≤ d7952 p :=
  nonnegative_ite (p 162) (nonnegative7951 p) (nonnegative7950 p)
def d7953 (p : Pattern) : Int := if p 163 then d12 p else d7932 p
theorem agree7953 (p q : Pattern) (h : Agree support p q) : d7953 p = d7953 q := by
  simp only [d7953, h 163 (by decide), agree12 p q h, agree7932 p q h]
theorem nonnegative7953 (p : Pattern) : 0 ≤ d7953 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7932 p)
def d7954 (p : Pattern) : Int := if p 162 then d12 p else d7953 p
theorem agree7954 (p q : Pattern) (h : Agree support p q) : d7954 p = d7954 q := by
  simp only [d7954, h 162 (by decide), agree12 p q h, agree7953 p q h]
theorem nonnegative7954 (p : Pattern) : 0 ≤ d7954 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7953 p)
def d7955 (p : Pattern) : Int := if p 161 then d7954 p else d7952 p
theorem agree7955 (p q : Pattern) (h : Agree support p q) : d7955 p = d7955 q := by
  simp only [d7955, h 161 (by decide), agree7954 p q h, agree7952 p q h]
theorem nonnegative7955 (p : Pattern) : 0 ≤ d7955 p :=
  nonnegative_ite (p 161) (nonnegative7954 p) (nonnegative7952 p)
def d7956 (p : Pattern) : Int := if p 160 then d7955 p else d7949 p
theorem agree7956 (p q : Pattern) (h : Agree support p q) : d7956 p = d7956 q := by
  simp only [d7956, h 160 (by decide), agree7955 p q h, agree7949 p q h]
theorem nonnegative7956 (p : Pattern) : 0 ≤ d7956 p :=
  nonnegative_ite (p 160) (nonnegative7955 p) (nonnegative7949 p)
def d7957 (p : Pattern) : Int := if p 141 then d7956 p else d7938 p
theorem agree7957 (p q : Pattern) (h : Agree support p q) : d7957 p = d7957 q := by
  simp only [d7957, h 141 (by decide), agree7956 p q h, agree7938 p q h]
theorem nonnegative7957 (p : Pattern) : 0 ≤ d7957 p :=
  nonnegative_ite (p 141) (nonnegative7956 p) (nonnegative7938 p)
def d7958 (p : Pattern) : Int := if p 204 then d7759 p else d3226 p
theorem agree7958 (p q : Pattern) (h : Agree support p q) : d7958 p = d7958 q := by
  simp only [d7958, h 204 (by decide), agree7759 p q h, agree3226 p q h]
theorem nonnegative7958 (p : Pattern) : 0 ≤ d7958 p :=
  nonnegative_ite (p 204) (nonnegative7759 p) (nonnegative3226 p)
def d7959 (p : Pattern) : Int := if p 204 then d12 p else d7753 p
theorem agree7959 (p q : Pattern) (h : Agree support p q) : d7959 p = d7959 q := by
  simp only [d7959, h 204 (by decide), agree12 p q h, agree7753 p q h]
theorem nonnegative7959 (p : Pattern) : 0 ≤ d7959 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7753 p)
def d7960 (p : Pattern) : Int := if p 182 then d7959 p else d7958 p
theorem agree7960 (p q : Pattern) (h : Agree support p q) : d7960 p = d7960 q := by
  simp only [d7960, h 182 (by decide), agree7959 p q h, agree7958 p q h]
theorem nonnegative7960 (p : Pattern) : 0 ≤ d7960 p :=
  nonnegative_ite (p 182) (nonnegative7959 p) (nonnegative7958 p)
def d7961 (p : Pattern) : Int := if p 204 then d12 p else d7757 p
theorem agree7961 (p q : Pattern) (h : Agree support p q) : d7961 p = d7961 q := by
  simp only [d7961, h 204 (by decide), agree12 p q h, agree7757 p q h]
theorem nonnegative7961 (p : Pattern) : 0 ≤ d7961 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7757 p)
def d7962 (p : Pattern) : Int := if p 182 then d7961 p else d7691 p
theorem agree7962 (p q : Pattern) (h : Agree support p q) : d7962 p = d7962 q := by
  simp only [d7962, h 182 (by decide), agree7961 p q h, agree7691 p q h]
theorem nonnegative7962 (p : Pattern) : 0 ≤ d7962 p :=
  nonnegative_ite (p 182) (nonnegative7961 p) (nonnegative7691 p)
def d7963 (p : Pattern) : Int := if p 163 then d7962 p else d7960 p
theorem agree7963 (p q : Pattern) (h : Agree support p q) : d7963 p = d7963 q := by
  simp only [d7963, h 163 (by decide), agree7962 p q h, agree7960 p q h]
theorem nonnegative7963 (p : Pattern) : 0 ≤ d7963 p :=
  nonnegative_ite (p 163) (nonnegative7962 p) (nonnegative7960 p)
def d7964 (p : Pattern) : Int := if p 162 then d7777 p else d7963 p
theorem agree7964 (p q : Pattern) (h : Agree support p q) : d7964 p = d7964 q := by
  simp only [d7964, h 162 (by decide), agree7777 p q h, agree7963 p q h]
theorem nonnegative7964 (p : Pattern) : 0 ≤ d7964 p :=
  nonnegative_ite (p 162) (nonnegative7777 p) (nonnegative7963 p)
def d7965 (p : Pattern) : Int := if p 161 then d7778 p else d7964 p
theorem agree7965 (p q : Pattern) (h : Agree support p q) : d7965 p = d7965 q := by
  simp only [d7965, h 161 (by decide), agree7778 p q h, agree7964 p q h]
theorem nonnegative7965 (p : Pattern) : 0 ≤ d7965 p :=
  nonnegative_ite (p 161) (nonnegative7778 p) (nonnegative7964 p)
def d7966 (p : Pattern) : Int := if p 224 then d12 p else d7707 p
theorem agree7966 (p q : Pattern) (h : Agree support p q) : d7966 p = d7966 q := by
  simp only [d7966, h 224 (by decide), agree12 p q h, agree7707 p q h]
theorem nonnegative7966 (p : Pattern) : 0 ≤ d7966 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative7707 p)
def d7967 (p : Pattern) : Int := if p 204 then d7966 p else d3461 p
theorem agree7967 (p q : Pattern) (h : Agree support p q) : d7967 p = d7967 q := by
  simp only [d7967, h 204 (by decide), agree7966 p q h, agree3461 p q h]
theorem nonnegative7967 (p : Pattern) : 0 ≤ d7967 p :=
  nonnegative_ite (p 204) (nonnegative7966 p) (nonnegative3461 p)
def d7968 (p : Pattern) : Int := if p 204 then d12 p else d7966 p
theorem agree7968 (p q : Pattern) (h : Agree support p q) : d7968 p = d7968 q := by
  simp only [d7968, h 204 (by decide), agree12 p q h, agree7966 p q h]
theorem nonnegative7968 (p : Pattern) : 0 ≤ d7968 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7966 p)
def d7969 (p : Pattern) : Int := if p 182 then d7968 p else d7967 p
theorem agree7969 (p q : Pattern) (h : Agree support p q) : d7969 p = d7969 q := by
  simp only [d7969, h 182 (by decide), agree7968 p q h, agree7967 p q h]
theorem nonnegative7969 (p : Pattern) : 0 ≤ d7969 p :=
  nonnegative_ite (p 182) (nonnegative7968 p) (nonnegative7967 p)
def d7970 (p : Pattern) : Int := if p 163 then d7969 p else d7766 p
theorem agree7970 (p q : Pattern) (h : Agree support p q) : d7970 p = d7970 q := by
  simp only [d7970, h 163 (by decide), agree7969 p q h, agree7766 p q h]
theorem nonnegative7970 (p : Pattern) : 0 ≤ d7970 p :=
  nonnegative_ite (p 163) (nonnegative7969 p) (nonnegative7766 p)
def d7971 (p : Pattern) : Int := if p 162 then d12 p else d7970 p
theorem agree7971 (p q : Pattern) (h : Agree support p q) : d7971 p = d7971 q := by
  simp only [d7971, h 162 (by decide), agree12 p q h, agree7970 p q h]
theorem nonnegative7971 (p : Pattern) : 0 ≤ d7971 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7970 p)
def d7972 (p : Pattern) : Int := if p 161 then d12 p else d7971 p
theorem agree7972 (p q : Pattern) (h : Agree support p q) : d7972 p = d7972 q := by
  simp only [d7972, h 161 (by decide), agree12 p q h, agree7971 p q h]
theorem nonnegative7972 (p : Pattern) : 0 ≤ d7972 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7971 p)
def d7973 (p : Pattern) : Int := if p 160 then d7972 p else d7965 p
theorem agree7973 (p q : Pattern) (h : Agree support p q) : d7973 p = d7973 q := by
  simp only [d7973, h 160 (by decide), agree7972 p q h, agree7965 p q h]
theorem nonnegative7973 (p : Pattern) : 0 ≤ d7973 p :=
  nonnegative_ite (p 160) (nonnegative7972 p) (nonnegative7965 p)
def d7974 (p : Pattern) : Int := if p 225 then d3279 p else d3253 p
theorem agree7974 (p q : Pattern) (h : Agree support p q) : d7974 p = d7974 q := by
  simp only [d7974, h 225 (by decide), agree3279 p q h, agree3253 p q h]
theorem nonnegative7974 (p : Pattern) : 0 ≤ d7974 p :=
  nonnegative_ite (p 225) (nonnegative3279 p) (nonnegative3253 p)
def d7975 (p : Pattern) : Int := if p 224 then d7974 p else d7692 p
theorem agree7975 (p q : Pattern) (h : Agree support p q) : d7975 p = d7975 q := by
  simp only [d7975, h 224 (by decide), agree7974 p q h, agree7692 p q h]
theorem nonnegative7975 (p : Pattern) : 0 ≤ d7975 p :=
  nonnegative_ite (p 224) (nonnegative7974 p) (nonnegative7692 p)
def d7976 (p : Pattern) : Int := if p 204 then d12 p else d7975 p
theorem agree7976 (p q : Pattern) (h : Agree support p q) : d7976 p = d7976 q := by
  simp only [d7976, h 204 (by decide), agree12 p q h, agree7975 p q h]
theorem nonnegative7976 (p : Pattern) : 0 ≤ d7976 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7975 p)
def d7977 (p : Pattern) : Int := if p 182 then d7976 p else d7740 p
theorem agree7977 (p q : Pattern) (h : Agree support p q) : d7977 p = d7977 q := by
  simp only [d7977, h 182 (by decide), agree7976 p q h, agree7740 p q h]
theorem nonnegative7977 (p : Pattern) : 0 ≤ d7977 p :=
  nonnegative_ite (p 182) (nonnegative7976 p) (nonnegative7740 p)
def d7978 (p : Pattern) : Int := if p 163 then d7774 p else d7977 p
theorem agree7978 (p q : Pattern) (h : Agree support p q) : d7978 p = d7978 q := by
  simp only [d7978, h 163 (by decide), agree7774 p q h, agree7977 p q h]
theorem nonnegative7978 (p : Pattern) : 0 ≤ d7978 p :=
  nonnegative_ite (p 163) (nonnegative7774 p) (nonnegative7977 p)
def d7979 (p : Pattern) : Int := if p 163 then d7736 p else d7766 p
theorem agree7979 (p q : Pattern) (h : Agree support p q) : d7979 p = d7979 q := by
  simp only [d7979, h 163 (by decide), agree7736 p q h, agree7766 p q h]
theorem nonnegative7979 (p : Pattern) : 0 ≤ d7979 p :=
  nonnegative_ite (p 163) (nonnegative7736 p) (nonnegative7766 p)
def d7980 (p : Pattern) : Int := if p 162 then d7979 p else d7978 p
theorem agree7980 (p q : Pattern) (h : Agree support p q) : d7980 p = d7980 q := by
  simp only [d7980, h 162 (by decide), agree7979 p q h, agree7978 p q h]
theorem nonnegative7980 (p : Pattern) : 0 ≤ d7980 p :=
  nonnegative_ite (p 162) (nonnegative7979 p) (nonnegative7978 p)
def d7981 (p : Pattern) : Int := if p 161 then d7788 p else d7980 p
theorem agree7981 (p q : Pattern) (h : Agree support p q) : d7981 p = d7981 q := by
  simp only [d7981, h 161 (by decide), agree7788 p q h, agree7980 p q h]
theorem nonnegative7981 (p : Pattern) : 0 ≤ d7981 p :=
  nonnegative_ite (p 161) (nonnegative7788 p) (nonnegative7980 p)
def d7982 (p : Pattern) : Int := if p 163 then d12 p else d7969 p
theorem agree7982 (p q : Pattern) (h : Agree support p q) : d7982 p = d7982 q := by
  simp only [d7982, h 163 (by decide), agree12 p q h, agree7969 p q h]
theorem nonnegative7982 (p : Pattern) : 0 ≤ d7982 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7969 p)
def d7983 (p : Pattern) : Int := if p 162 then d12 p else d7982 p
theorem agree7983 (p q : Pattern) (h : Agree support p q) : d7983 p = d7983 q := by
  simp only [d7983, h 162 (by decide), agree12 p q h, agree7982 p q h]
theorem nonnegative7983 (p : Pattern) : 0 ≤ d7983 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7982 p)
def d7984 (p : Pattern) : Int := if p 161 then d12 p else d7983 p
theorem agree7984 (p q : Pattern) (h : Agree support p q) : d7984 p = d7984 q := by
  simp only [d7984, h 161 (by decide), agree12 p q h, agree7983 p q h]
theorem nonnegative7984 (p : Pattern) : 0 ≤ d7984 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7983 p)
def d7985 (p : Pattern) : Int := if p 160 then d7984 p else d7981 p
theorem agree7985 (p q : Pattern) (h : Agree support p q) : d7985 p = d7985 q := by
  simp only [d7985, h 160 (by decide), agree7984 p q h, agree7981 p q h]
theorem nonnegative7985 (p : Pattern) : 0 ≤ d7985 p :=
  nonnegative_ite (p 160) (nonnegative7984 p) (nonnegative7981 p)
def d7986 (p : Pattern) : Int := if p 141 then d7985 p else d7973 p
theorem agree7986 (p q : Pattern) (h : Agree support p q) : d7986 p = d7986 q := by
  simp only [d7986, h 141 (by decide), agree7985 p q h, agree7973 p q h]
theorem nonnegative7986 (p : Pattern) : 0 ≤ d7986 p :=
  nonnegative_ite (p 141) (nonnegative7985 p) (nonnegative7973 p)
def d7987 (p : Pattern) : Int := if p 138 then d7986 p else d7957 p
theorem agree7987 (p q : Pattern) (h : Agree support p q) : d7987 p = d7987 q := by
  simp only [d7987, h 138 (by decide), agree7986 p q h, agree7957 p q h]
theorem nonnegative7987 (p : Pattern) : 0 ≤ d7987 p :=
  nonnegative_ite (p 138) (nonnegative7986 p) (nonnegative7957 p)
def d7988 (p : Pattern) : Int := if p 138 then d12 p else d7986 p
theorem agree7988 (p q : Pattern) (h : Agree support p q) : d7988 p = d7988 q := by
  simp only [d7988, h 138 (by decide), agree12 p q h, agree7986 p q h]
theorem nonnegative7988 (p : Pattern) : 0 ≤ d7988 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7986 p)
def d7989 (p : Pattern) : Int := if p 116 then d7988 p else d7987 p
theorem agree7989 (p q : Pattern) (h : Agree support p q) : d7989 p = d7989 q := by
  simp only [d7989, h 116 (by decide), agree7988 p q h, agree7987 p q h]
theorem nonnegative7989 (p : Pattern) : 0 ≤ d7989 p :=
  nonnegative_ite (p 116) (nonnegative7988 p) (nonnegative7987 p)
def d7990 (p : Pattern) : Int := if p 115 then d7989 p else d7802 p
theorem agree7990 (p q : Pattern) (h : Agree support p q) : d7990 p = d7990 q := by
  simp only [d7990, h 115 (by decide), agree7989 p q h, agree7802 p q h]
theorem nonnegative7990 (p : Pattern) : 0 ≤ d7990 p :=
  nonnegative_ite (p 115) (nonnegative7989 p) (nonnegative7802 p)
def d7991 (p : Pattern) : Int := if p 71 then d7990 p else d7805 p
theorem agree7991 (p q : Pattern) (h : Agree support p q) : d7991 p = d7991 q := by
  simp only [d7991, h 71 (by decide), agree7990 p q h, agree7805 p q h]
theorem nonnegative7991 (p : Pattern) : 0 ≤ d7991 p :=
  nonnegative_ite (p 71) (nonnegative7990 p) (nonnegative7805 p)
def d7992 (p : Pattern) : Int := if p 163 then d12 p else d7819 p
theorem agree7992 (p q : Pattern) (h : Agree support p q) : d7992 p = d7992 q := by
  simp only [d7992, h 163 (by decide), agree12 p q h, agree7819 p q h]
theorem nonnegative7992 (p : Pattern) : 0 ≤ d7992 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7819 p)
def d7993 (p : Pattern) : Int := if p 162 then d7992 p else d7856 p
theorem agree7993 (p q : Pattern) (h : Agree support p q) : d7993 p = d7993 q := by
  simp only [d7993, h 162 (by decide), agree7992 p q h, agree7856 p q h]
theorem nonnegative7993 (p : Pattern) : 0 ≤ d7993 p :=
  nonnegative_ite (p 162) (nonnegative7992 p) (nonnegative7856 p)
def d7994 (p : Pattern) : Int := if p 162 then d12 p else d7992 p
theorem agree7994 (p q : Pattern) (h : Agree support p q) : d7994 p = d7994 q := by
  simp only [d7994, h 162 (by decide), agree12 p q h, agree7992 p q h]
theorem nonnegative7994 (p : Pattern) : 0 ≤ d7994 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7992 p)
def d7995 (p : Pattern) : Int := if p 161 then d7994 p else d7993 p
theorem agree7995 (p q : Pattern) (h : Agree support p q) : d7995 p = d7995 q := by
  simp only [d7995, h 161 (by decide), agree7994 p q h, agree7993 p q h]
theorem nonnegative7995 (p : Pattern) : 0 ≤ d7995 p :=
  nonnegative_ite (p 161) (nonnegative7994 p) (nonnegative7993 p)
def d7996 (p : Pattern) : Int := if p 163 then d12 p else d7842 p
theorem agree7996 (p q : Pattern) (h : Agree support p q) : d7996 p = d7996 q := by
  simp only [d7996, h 163 (by decide), agree12 p q h, agree7842 p q h]
theorem nonnegative7996 (p : Pattern) : 0 ≤ d7996 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7842 p)
def d7997 (p : Pattern) : Int := if p 162 then d7996 p else d7864 p
theorem agree7997 (p q : Pattern) (h : Agree support p q) : d7997 p = d7997 q := by
  simp only [d7997, h 162 (by decide), agree7996 p q h, agree7864 p q h]
theorem nonnegative7997 (p : Pattern) : 0 ≤ d7997 p :=
  nonnegative_ite (p 162) (nonnegative7996 p) (nonnegative7864 p)
def d7998 (p : Pattern) : Int := if p 162 then d12 p else d7996 p
theorem agree7998 (p q : Pattern) (h : Agree support p q) : d7998 p = d7998 q := by
  simp only [d7998, h 162 (by decide), agree12 p q h, agree7996 p q h]
theorem nonnegative7998 (p : Pattern) : 0 ≤ d7998 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7996 p)
def d7999 (p : Pattern) : Int := if p 161 then d7998 p else d7997 p
theorem agree7999 (p q : Pattern) (h : Agree support p q) : d7999 p = d7999 q := by
  simp only [d7999, h 161 (by decide), agree7998 p q h, agree7997 p q h]
theorem nonnegative7999 (p : Pattern) : 0 ≤ d7999 p :=
  nonnegative_ite (p 161) (nonnegative7998 p) (nonnegative7997 p)
def d8000 (p : Pattern) : Int := if p 160 then d7999 p else d7995 p
theorem agree8000 (p q : Pattern) (h : Agree support p q) : d8000 p = d8000 q := by
  simp only [d8000, h 160 (by decide), agree7999 p q h, agree7995 p q h]
theorem nonnegative8000 (p : Pattern) : 0 ≤ d8000 p :=
  nonnegative_ite (p 160) (nonnegative7999 p) (nonnegative7995 p)
def d8001 (p : Pattern) : Int := if p 141 then d8000 p else d7848 p
theorem agree8001 (p q : Pattern) (h : Agree support p q) : d8001 p = d8001 q := by
  simp only [d8001, h 141 (by decide), agree8000 p q h, agree7848 p q h]
theorem nonnegative8001 (p : Pattern) : 0 ≤ d8001 p :=
  nonnegative_ite (p 141) (nonnegative8000 p) (nonnegative7848 p)
def d8002 (p : Pattern) : Int := if p 163 then d12 p else d7885 p
theorem agree8002 (p q : Pattern) (h : Agree support p q) : d8002 p = d8002 q := by
  simp only [d8002, h 163 (by decide), agree12 p q h, agree7885 p q h]
theorem nonnegative8002 (p : Pattern) : 0 ≤ d8002 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7885 p)
def d8003 (p : Pattern) : Int := if p 162 then d8002 p else d7897 p
theorem agree8003 (p q : Pattern) (h : Agree support p q) : d8003 p = d8003 q := by
  simp only [d8003, h 162 (by decide), agree8002 p q h, agree7897 p q h]
theorem nonnegative8003 (p : Pattern) : 0 ≤ d8003 p :=
  nonnegative_ite (p 162) (nonnegative8002 p) (nonnegative7897 p)
def d8004 (p : Pattern) : Int := if p 162 then d12 p else d8002 p
theorem agree8004 (p q : Pattern) (h : Agree support p q) : d8004 p = d8004 q := by
  simp only [d8004, h 162 (by decide), agree12 p q h, agree8002 p q h]
theorem nonnegative8004 (p : Pattern) : 0 ≤ d8004 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative8002 p)
def d8005 (p : Pattern) : Int := if p 161 then d8004 p else d8003 p
theorem agree8005 (p q : Pattern) (h : Agree support p q) : d8005 p = d8005 q := by
  simp only [d8005, h 161 (by decide), agree8004 p q h, agree8003 p q h]
theorem nonnegative8005 (p : Pattern) : 0 ≤ d8005 p :=
  nonnegative_ite (p 161) (nonnegative8004 p) (nonnegative8003 p)
def d8006 (p : Pattern) : Int := if p 160 then d7905 p else d8005 p
theorem agree8006 (p q : Pattern) (h : Agree support p q) : d8006 p = d8006 q := by
  simp only [d8006, h 160 (by decide), agree7905 p q h, agree8005 p q h]
theorem nonnegative8006 (p : Pattern) : 0 ≤ d8006 p :=
  nonnegative_ite (p 160) (nonnegative7905 p) (nonnegative8005 p)
def d8007 (p : Pattern) : Int := if p 141 then d8006 p else d7896 p
theorem agree8007 (p q : Pattern) (h : Agree support p q) : d8007 p = d8007 q := by
  simp only [d8007, h 141 (by decide), agree8006 p q h, agree7896 p q h]
theorem nonnegative8007 (p : Pattern) : 0 ≤ d8007 p :=
  nonnegative_ite (p 141) (nonnegative8006 p) (nonnegative7896 p)
def d8008 (p : Pattern) : Int := if p 138 then d8007 p else d8001 p
theorem agree8008 (p q : Pattern) (h : Agree support p q) : d8008 p = d8008 q := by
  simp only [d8008, h 138 (by decide), agree8007 p q h, agree8001 p q h]
theorem nonnegative8008 (p : Pattern) : 0 ≤ d8008 p :=
  nonnegative_ite (p 138) (nonnegative8007 p) (nonnegative8001 p)
def d8009 (p : Pattern) : Int := if p 138 then d7912 p else d8007 p
theorem agree8009 (p q : Pattern) (h : Agree support p q) : d8009 p = d8009 q := by
  simp only [d8009, h 138 (by decide), agree7912 p q h, agree8007 p q h]
theorem nonnegative8009 (p : Pattern) : 0 ≤ d8009 p :=
  nonnegative_ite (p 138) (nonnegative7912 p) (nonnegative8007 p)
def d8010 (p : Pattern) : Int := if p 116 then d8009 p else d8008 p
theorem agree8010 (p q : Pattern) (h : Agree support p q) : d8010 p = d8010 q := by
  simp only [d8010, h 116 (by decide), agree8009 p q h, agree8008 p q h]
theorem nonnegative8010 (p : Pattern) : 0 ≤ d8010 p :=
  nonnegative_ite (p 116) (nonnegative8009 p) (nonnegative8008 p)
def d8011 (p : Pattern) : Int := if p 204 then d7878 p else d3358 p
theorem agree8011 (p q : Pattern) (h : Agree support p q) : d8011 p = d8011 q := by
  simp only [d8011, h 204 (by decide), agree7878 p q h, agree3358 p q h]
theorem nonnegative8011 (p : Pattern) : 0 ≤ d8011 p :=
  nonnegative_ite (p 204) (nonnegative7878 p) (nonnegative3358 p)
def d8012 (p : Pattern) : Int := if p 204 then d12 p else d7872 p
theorem agree8012 (p q : Pattern) (h : Agree support p q) : d8012 p = d8012 q := by
  simp only [d8012, h 204 (by decide), agree12 p q h, agree7872 p q h]
theorem nonnegative8012 (p : Pattern) : 0 ≤ d8012 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7872 p)
def d8013 (p : Pattern) : Int := if p 182 then d8012 p else d8011 p
theorem agree8013 (p q : Pattern) (h : Agree support p q) : d8013 p = d8013 q := by
  simp only [d8013, h 182 (by decide), agree8012 p q h, agree8011 p q h]
theorem nonnegative8013 (p : Pattern) : 0 ≤ d8013 p :=
  nonnegative_ite (p 182) (nonnegative8012 p) (nonnegative8011 p)
def d8014 (p : Pattern) : Int := if p 163 then d7885 p else d8013 p
theorem agree8014 (p q : Pattern) (h : Agree support p q) : d8014 p = d8014 q := by
  simp only [d8014, h 163 (by decide), agree7885 p q h, agree8013 p q h]
theorem nonnegative8014 (p : Pattern) : 0 ≤ d8014 p :=
  nonnegative_ite (p 163) (nonnegative7885 p) (nonnegative8013 p)
def d8015 (p : Pattern) : Int := if p 162 then d8014 p else d7875 p
theorem agree8015 (p q : Pattern) (h : Agree support p q) : d8015 p = d8015 q := by
  simp only [d8015, h 162 (by decide), agree8014 p q h, agree7875 p q h]
theorem nonnegative8015 (p : Pattern) : 0 ≤ d8015 p :=
  nonnegative_ite (p 162) (nonnegative8014 p) (nonnegative7875 p)
def d8016 (p : Pattern) : Int := if p 163 then d7885 p else d7880 p
theorem agree8016 (p q : Pattern) (h : Agree support p q) : d8016 p = d8016 q := by
  simp only [d8016, h 163 (by decide), agree7885 p q h, agree7880 p q h]
theorem nonnegative8016 (p : Pattern) : 0 ≤ d8016 p :=
  nonnegative_ite (p 163) (nonnegative7885 p) (nonnegative7880 p)
def d8017 (p : Pattern) : Int := if p 162 then d7822 p else d8016 p
theorem agree8017 (p q : Pattern) (h : Agree support p q) : d8017 p = d8017 q := by
  simp only [d8017, h 162 (by decide), agree7822 p q h, agree8016 p q h]
theorem nonnegative8017 (p : Pattern) : 0 ≤ d8017 p :=
  nonnegative_ite (p 162) (nonnegative7822 p) (nonnegative8016 p)
def d8018 (p : Pattern) : Int := if p 161 then d8017 p else d8015 p
theorem agree8018 (p q : Pattern) (h : Agree support p q) : d8018 p = d8018 q := by
  simp only [d8018, h 161 (by decide), agree8017 p q h, agree8015 p q h]
theorem nonnegative8018 (p : Pattern) : 0 ≤ d8018 p :=
  nonnegative_ite (p 161) (nonnegative8017 p) (nonnegative8015 p)
def d8019 (p : Pattern) : Int := if p 182 then d7835 p else d7862 p
theorem agree8019 (p q : Pattern) (h : Agree support p q) : d8019 p = d8019 q := by
  simp only [d8019, h 182 (by decide), agree7835 p q h, agree7862 p q h]
theorem nonnegative8019 (p : Pattern) : 0 ≤ d8019 p :=
  nonnegative_ite (p 182) (nonnegative7835 p) (nonnegative7862 p)
def d8020 (p : Pattern) : Int := if p 163 then d8019 p else d7890 p
theorem agree8020 (p q : Pattern) (h : Agree support p q) : d8020 p = d8020 q := by
  simp only [d8020, h 163 (by decide), agree8019 p q h, agree7890 p q h]
theorem nonnegative8020 (p : Pattern) : 0 ≤ d8020 p :=
  nonnegative_ite (p 163) (nonnegative8019 p) (nonnegative7890 p)
def d8021 (p : Pattern) : Int := if p 162 then d7996 p else d8020 p
theorem agree8021 (p q : Pattern) (h : Agree support p q) : d8021 p = d8021 q := by
  simp only [d8021, h 162 (by decide), agree7996 p q h, agree8020 p q h]
theorem nonnegative8021 (p : Pattern) : 0 ≤ d8021 p :=
  nonnegative_ite (p 162) (nonnegative7996 p) (nonnegative8020 p)
def d8022 (p : Pattern) : Int := if p 182 then d12 p else d7891 p
theorem agree8022 (p q : Pattern) (h : Agree support p q) : d8022 p = d8022 q := by
  simp only [d8022, h 182 (by decide), agree12 p q h, agree7891 p q h]
theorem nonnegative8022 (p : Pattern) : 0 ≤ d8022 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative7891 p)
def d8023 (p : Pattern) : Int := if p 163 then d12 p else d8022 p
theorem agree8023 (p q : Pattern) (h : Agree support p q) : d8023 p = d8023 q := by
  simp only [d8023, h 163 (by decide), agree12 p q h, agree8022 p q h]
theorem nonnegative8023 (p : Pattern) : 0 ≤ d8023 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative8022 p)
def d8024 (p : Pattern) : Int := if p 162 then d12 p else d8023 p
theorem agree8024 (p q : Pattern) (h : Agree support p q) : d8024 p = d8024 q := by
  simp only [d8024, h 162 (by decide), agree12 p q h, agree8023 p q h]
theorem nonnegative8024 (p : Pattern) : 0 ≤ d8024 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative8023 p)
def d8025 (p : Pattern) : Int := if p 161 then d8024 p else d8021 p
theorem agree8025 (p q : Pattern) (h : Agree support p q) : d8025 p = d8025 q := by
  simp only [d8025, h 161 (by decide), agree8024 p q h, agree8021 p q h]
theorem nonnegative8025 (p : Pattern) : 0 ≤ d8025 p :=
  nonnegative_ite (p 161) (nonnegative8024 p) (nonnegative8021 p)
def d8026 (p : Pattern) : Int := if p 160 then d8025 p else d8018 p
theorem agree8026 (p q : Pattern) (h : Agree support p q) : d8026 p = d8026 q := by
  simp only [d8026, h 160 (by decide), agree8025 p q h, agree8018 p q h]
theorem nonnegative8026 (p : Pattern) : 0 ≤ d8026 p :=
  nonnegative_ite (p 160) (nonnegative8025 p) (nonnegative8018 p)
def d8027 (p : Pattern) : Int := if p 225 then d3244 p else d3377 p
theorem agree8027 (p q : Pattern) (h : Agree support p q) : d8027 p = d8027 q := by
  simp only [d8027, h 225 (by decide), agree3244 p q h, agree3377 p q h]
theorem nonnegative8027 (p : Pattern) : 0 ≤ d8027 p :=
  nonnegative_ite (p 225) (nonnegative3244 p) (nonnegative3377 p)
def d8028 (p : Pattern) : Int := if p 224 then d8027 p else d7829 p
theorem agree8028 (p q : Pattern) (h : Agree support p q) : d8028 p = d8028 q := by
  simp only [d8028, h 224 (by decide), agree8027 p q h, agree7829 p q h]
theorem nonnegative8028 (p : Pattern) : 0 ≤ d8028 p :=
  nonnegative_ite (p 224) (nonnegative8027 p) (nonnegative7829 p)
def d8029 (p : Pattern) : Int := if p 204 then d8028 p else d3374 p
theorem agree8029 (p q : Pattern) (h : Agree support p q) : d8029 p = d8029 q := by
  simp only [d8029, h 204 (by decide), agree8028 p q h, agree3374 p q h]
theorem nonnegative8029 (p : Pattern) : 0 ≤ d8029 p :=
  nonnegative_ite (p 204) (nonnegative8028 p) (nonnegative3374 p)
def d8030 (p : Pattern) : Int := if p 204 then d12 p else d7850 p
theorem agree8030 (p q : Pattern) (h : Agree support p q) : d8030 p = d8030 q := by
  simp only [d8030, h 204 (by decide), agree12 p q h, agree7850 p q h]
theorem nonnegative8030 (p : Pattern) : 0 ≤ d8030 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7850 p)
def d8031 (p : Pattern) : Int := if p 182 then d8030 p else d8029 p
theorem agree8031 (p q : Pattern) (h : Agree support p q) : d8031 p = d8031 q := by
  simp only [d8031, h 182 (by decide), agree8030 p q h, agree8029 p q h]
theorem nonnegative8031 (p : Pattern) : 0 ≤ d8031 p :=
  nonnegative_ite (p 182) (nonnegative8030 p) (nonnegative8029 p)
def d8032 (p : Pattern) : Int := if p 163 then d8031 p else d8013 p
theorem agree8032 (p q : Pattern) (h : Agree support p q) : d8032 p = d8032 q := by
  simp only [d8032, h 163 (by decide), agree8031 p q h, agree8013 p q h]
theorem nonnegative8032 (p : Pattern) : 0 ≤ d8032 p :=
  nonnegative_ite (p 163) (nonnegative8031 p) (nonnegative8013 p)
def d8033 (p : Pattern) : Int := if p 224 then d7681 p else d7839 p
theorem agree8033 (p q : Pattern) (h : Agree support p q) : d8033 p = d8033 q := by
  simp only [d8033, h 224 (by decide), agree7681 p q h, agree7839 p q h]
theorem nonnegative8033 (p : Pattern) : 0 ≤ d8033 p :=
  nonnegative_ite (p 224) (nonnegative7681 p) (nonnegative7839 p)
def d8034 (p : Pattern) : Int := if p 204 then d8033 p else d3366 p
theorem agree8034 (p q : Pattern) (h : Agree support p q) : d8034 p = d8034 q := by
  simp only [d8034, h 204 (by decide), agree8033 p q h, agree3366 p q h]
theorem nonnegative8034 (p : Pattern) : 0 ≤ d8034 p :=
  nonnegative_ite (p 204) (nonnegative8033 p) (nonnegative3366 p)
def d8035 (p : Pattern) : Int := if p 204 then d12 p else d7814 p
theorem agree8035 (p q : Pattern) (h : Agree support p q) : d8035 p = d8035 q := by
  simp only [d8035, h 204 (by decide), agree12 p q h, agree7814 p q h]
theorem nonnegative8035 (p : Pattern) : 0 ≤ d8035 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative7814 p)
def d8036 (p : Pattern) : Int := if p 182 then d8035 p else d8034 p
theorem agree8036 (p q : Pattern) (h : Agree support p q) : d8036 p = d8036 q := by
  simp only [d8036, h 182 (by decide), agree8035 p q h, agree8034 p q h]
theorem nonnegative8036 (p : Pattern) : 0 ≤ d8036 p :=
  nonnegative_ite (p 182) (nonnegative8035 p) (nonnegative8034 p)
def d8037 (p : Pattern) : Int := if p 163 then d12 p else d8036 p
theorem agree8037 (p q : Pattern) (h : Agree support p q) : d8037 p = d8037 q := by
  simp only [d8037, h 163 (by decide), agree12 p q h, agree8036 p q h]
theorem nonnegative8037 (p : Pattern) : 0 ≤ d8037 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative8036 p)
def d8038 (p : Pattern) : Int := if p 162 then d8037 p else d8032 p
theorem agree8038 (p q : Pattern) (h : Agree support p q) : d8038 p = d8038 q := by
  simp only [d8038, h 162 (by decide), agree8037 p q h, agree8032 p q h]
theorem nonnegative8038 (p : Pattern) : 0 ≤ d8038 p :=
  nonnegative_ite (p 162) (nonnegative8037 p) (nonnegative8032 p)
def d8039 (p : Pattern) : Int := if p 204 then d12 p else d8033 p
theorem agree8039 (p q : Pattern) (h : Agree support p q) : d8039 p = d8039 q := by
  simp only [d8039, h 204 (by decide), agree12 p q h, agree8033 p q h]
theorem nonnegative8039 (p : Pattern) : 0 ≤ d8039 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative8033 p)
end NetHack.Sokoban22Refined85
