/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes40
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d4920 (p : Pattern) : Int := if p 161 then d12 p else d4282 p
theorem agree4920 (p q : Pattern) (h : Agree support p q) : d4920 p = d4920 q := by
  simp only [d4920, h 161 (by decide), agree12 p q h, agree4282 p q h]
theorem nonnegative4920 (p : Pattern) : 0 ≤ d4920 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4282 p)
def d4921 (p : Pattern) : Int := if p 160 then d4920 p else d4243 p
theorem agree4921 (p q : Pattern) (h : Agree support p q) : d4921 p = d4921 q := by
  simp only [d4921, h 160 (by decide), agree4920 p q h, agree4243 p q h]
theorem nonnegative4921 (p : Pattern) : 0 ≤ d4921 p :=
  nonnegative_ite (p 160) (nonnegative4920 p) (nonnegative4243 p)
def d4922 (p : Pattern) : Int := if p 141 then d4921 p else d4919 p
theorem agree4922 (p q : Pattern) (h : Agree support p q) : d4922 p = d4922 q := by
  simp only [d4922, h 141 (by decide), agree4921 p q h, agree4919 p q h]
theorem nonnegative4922 (p : Pattern) : 0 ≤ d4922 p :=
  nonnegative_ite (p 141) (nonnegative4921 p) (nonnegative4919 p)
def d4923 (p : Pattern) : Int := if p 160 then d12 p else d4246 p
theorem agree4923 (p q : Pattern) (h : Agree support p q) : d4923 p = d4923 q := by
  simp only [d4923, h 160 (by decide), agree12 p q h, agree4246 p q h]
theorem nonnegative4923 (p : Pattern) : 0 ≤ d4923 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative4246 p)
def d4924 (p : Pattern) : Int := if p 141 then d12 p else d4923 p
theorem agree4924 (p q : Pattern) (h : Agree support p q) : d4924 p = d4924 q := by
  simp only [d4924, h 141 (by decide), agree12 p q h, agree4923 p q h]
theorem nonnegative4924 (p : Pattern) : 0 ≤ d4924 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative4923 p)
def d4925 (p : Pattern) : Int := if p 138 then d4924 p else d4922 p
theorem agree4925 (p q : Pattern) (h : Agree support p q) : d4925 p = d4925 q := by
  simp only [d4925, h 138 (by decide), agree4924 p q h, agree4922 p q h]
theorem nonnegative4925 (p : Pattern) : 0 ≤ d4925 p :=
  nonnegative_ite (p 138) (nonnegative4924 p) (nonnegative4922 p)
def d4926 (p : Pattern) : Int := if p 116 then d4925 p else d4922 p
theorem agree4926 (p q : Pattern) (h : Agree support p q) : d4926 p = d4926 q := by
  simp only [d4926, h 116 (by decide), agree4925 p q h, agree4922 p q h]
theorem nonnegative4926 (p : Pattern) : 0 ≤ d4926 p :=
  nonnegative_ite (p 116) (nonnegative4925 p) (nonnegative4922 p)
def d4927 (p : Pattern) : Int := if p 138 then d12 p else d4922 p
theorem agree4927 (p q : Pattern) (h : Agree support p q) : d4927 p = d4927 q := by
  simp only [d4927, h 138 (by decide), agree12 p q h, agree4922 p q h]
theorem nonnegative4927 (p : Pattern) : 0 ≤ d4927 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4922 p)
def d4928 (p : Pattern) : Int := if p 116 then d4927 p else d4922 p
theorem agree4928 (p q : Pattern) (h : Agree support p q) : d4928 p = d4928 q := by
  simp only [d4928, h 116 (by decide), agree4927 p q h, agree4922 p q h]
theorem nonnegative4928 (p : Pattern) : 0 ≤ d4928 p :=
  nonnegative_ite (p 116) (nonnegative4927 p) (nonnegative4922 p)
def d4929 (p : Pattern) : Int := if p 115 then d4928 p else d4926 p
theorem agree4929 (p q : Pattern) (h : Agree support p q) : d4929 p = d4929 q := by
  simp only [d4929, h 115 (by decide), agree4928 p q h, agree4926 p q h]
theorem nonnegative4929 (p : Pattern) : 0 ≤ d4929 p :=
  nonnegative_ite (p 115) (nonnegative4928 p) (nonnegative4926 p)
def d4930 (p : Pattern) : Int := if p 71 then d4929 p else d4915 p
theorem agree4930 (p q : Pattern) (h : Agree support p q) : d4930 p = d4930 q := by
  simp only [d4930, h 71 (by decide), agree4929 p q h, agree4915 p q h]
theorem nonnegative4930 (p : Pattern) : 0 ≤ d4930 p :=
  nonnegative_ite (p 71) (nonnegative4929 p) (nonnegative4915 p)
def d4931 (p : Pattern) : Int := if p 49 then d4930 p else d4915 p
theorem agree4931 (p q : Pattern) (h : Agree support p q) : d4931 p = d4931 q := by
  simp only [d4931, h 49 (by decide), agree4930 p q h, agree4915 p q h]
theorem nonnegative4931 (p : Pattern) : 0 ≤ d4931 p :=
  nonnegative_ite (p 49) (nonnegative4930 p) (nonnegative4915 p)
def d4932 (p : Pattern) : Int := if p 163 then d192 p else d19 p
theorem agree4932 (p q : Pattern) (h : Agree support p q) : d4932 p = d4932 q := by
  simp only [d4932, h 163 (by decide), agree192 p q h, agree19 p q h]
theorem nonnegative4932 (p : Pattern) : 0 ≤ d4932 p :=
  nonnegative_ite (p 163) (nonnegative192 p) (nonnegative19 p)
def d4933 (p : Pattern) : Int := if p 162 then d12 p else d4932 p
theorem agree4933 (p q : Pattern) (h : Agree support p q) : d4933 p = d4933 q := by
  simp only [d4933, h 162 (by decide), agree12 p q h, agree4932 p q h]
theorem nonnegative4933 (p : Pattern) : 0 ≤ d4933 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4932 p)
def d4934 (p : Pattern) : Int := if p 161 then d12 p else d4933 p
theorem agree4934 (p q : Pattern) (h : Agree support p q) : d4934 p = d4934 q := by
  simp only [d4934, h 161 (by decide), agree12 p q h, agree4933 p q h]
theorem nonnegative4934 (p : Pattern) : 0 ≤ d4934 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4933 p)
def d4935 (p : Pattern) : Int := if p 160 then d4934 p else d4258 p
theorem agree4935 (p q : Pattern) (h : Agree support p q) : d4935 p = d4935 q := by
  simp only [d4935, h 160 (by decide), agree4934 p q h, agree4258 p q h]
theorem nonnegative4935 (p : Pattern) : 0 ≤ d4935 p :=
  nonnegative_ite (p 160) (nonnegative4934 p) (nonnegative4258 p)
def d4936 (p : Pattern) : Int := if p 163 then d12 p else d192 p
theorem agree4936 (p q : Pattern) (h : Agree support p q) : d4936 p = d4936 q := by
  simp only [d4936, h 163 (by decide), agree12 p q h, agree192 p q h]
theorem nonnegative4936 (p : Pattern) : 0 ≤ d4936 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative192 p)
def d4937 (p : Pattern) : Int := if p 162 then d12 p else d4936 p
theorem agree4937 (p q : Pattern) (h : Agree support p q) : d4937 p = d4937 q := by
  simp only [d4937, h 162 (by decide), agree12 p q h, agree4936 p q h]
theorem nonnegative4937 (p : Pattern) : 0 ≤ d4937 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4936 p)
def d4938 (p : Pattern) : Int := if p 161 then d12 p else d4937 p
theorem agree4938 (p q : Pattern) (h : Agree support p q) : d4938 p = d4938 q := by
  simp only [d4938, h 161 (by decide), agree12 p q h, agree4937 p q h]
theorem nonnegative4938 (p : Pattern) : 0 ≤ d4938 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4937 p)
def d4939 (p : Pattern) : Int := if p 160 then d4938 p else d4263 p
theorem agree4939 (p q : Pattern) (h : Agree support p q) : d4939 p = d4939 q := by
  simp only [d4939, h 160 (by decide), agree4938 p q h, agree4263 p q h]
theorem nonnegative4939 (p : Pattern) : 0 ≤ d4939 p :=
  nonnegative_ite (p 160) (nonnegative4938 p) (nonnegative4263 p)
def d4940 (p : Pattern) : Int := if p 141 then d4939 p else d4935 p
theorem agree4940 (p q : Pattern) (h : Agree support p q) : d4940 p = d4940 q := by
  simp only [d4940, h 141 (by decide), agree4939 p q h, agree4935 p q h]
theorem nonnegative4940 (p : Pattern) : 0 ≤ d4940 p :=
  nonnegative_ite (p 141) (nonnegative4939 p) (nonnegative4935 p)
def d4941 (p : Pattern) : Int := if p 138 then d4940 p else d4907 p
theorem agree4941 (p q : Pattern) (h : Agree support p q) : d4941 p = d4941 q := by
  simp only [d4941, h 138 (by decide), agree4940 p q h, agree4907 p q h]
theorem nonnegative4941 (p : Pattern) : 0 ≤ d4941 p :=
  nonnegative_ite (p 138) (nonnegative4940 p) (nonnegative4907 p)
def d4942 (p : Pattern) : Int := if p 138 then d12 p else d4940 p
theorem agree4942 (p q : Pattern) (h : Agree support p q) : d4942 p = d4942 q := by
  simp only [d4942, h 138 (by decide), agree12 p q h, agree4940 p q h]
theorem nonnegative4942 (p : Pattern) : 0 ≤ d4942 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4940 p)
def d4943 (p : Pattern) : Int := if p 116 then d4942 p else d4941 p
theorem agree4943 (p q : Pattern) (h : Agree support p q) : d4943 p = d4943 q := by
  simp only [d4943, h 116 (by decide), agree4942 p q h, agree4941 p q h]
theorem nonnegative4943 (p : Pattern) : 0 ≤ d4943 p :=
  nonnegative_ite (p 116) (nonnegative4942 p) (nonnegative4941 p)
def d4944 (p : Pattern) : Int := if p 115 then d4943 p else d4912 p
theorem agree4944 (p q : Pattern) (h : Agree support p q) : d4944 p = d4944 q := by
  simp only [d4944, h 115 (by decide), agree4943 p q h, agree4912 p q h]
theorem nonnegative4944 (p : Pattern) : 0 ≤ d4944 p :=
  nonnegative_ite (p 115) (nonnegative4943 p) (nonnegative4912 p)
def d4945 (p : Pattern) : Int := if p 71 then d4944 p else d4915 p
theorem agree4945 (p q : Pattern) (h : Agree support p q) : d4945 p = d4945 q := by
  simp only [d4945, h 71 (by decide), agree4944 p q h, agree4915 p q h]
theorem nonnegative4945 (p : Pattern) : 0 ≤ d4945 p :=
  nonnegative_ite (p 71) (nonnegative4944 p) (nonnegative4915 p)
def d4946 (p : Pattern) : Int := if p 160 then d4920 p else d4273 p
theorem agree4946 (p q : Pattern) (h : Agree support p q) : d4946 p = d4946 q := by
  simp only [d4946, h 160 (by decide), agree4920 p q h, agree4273 p q h]
theorem nonnegative4946 (p : Pattern) : 0 ≤ d4946 p :=
  nonnegative_ite (p 160) (nonnegative4920 p) (nonnegative4273 p)
def d4947 (p : Pattern) : Int := if p 141 then d4946 p else d4919 p
theorem agree4947 (p q : Pattern) (h : Agree support p q) : d4947 p = d4947 q := by
  simp only [d4947, h 141 (by decide), agree4946 p q h, agree4919 p q h]
theorem nonnegative4947 (p : Pattern) : 0 ≤ d4947 p :=
  nonnegative_ite (p 141) (nonnegative4946 p) (nonnegative4919 p)
def d4948 (p : Pattern) : Int := if p 138 then d4924 p else d4947 p
theorem agree4948 (p q : Pattern) (h : Agree support p q) : d4948 p = d4948 q := by
  simp only [d4948, h 138 (by decide), agree4924 p q h, agree4947 p q h]
theorem nonnegative4948 (p : Pattern) : 0 ≤ d4948 p :=
  nonnegative_ite (p 138) (nonnegative4924 p) (nonnegative4947 p)
def d4949 (p : Pattern) : Int := if p 116 then d4948 p else d4947 p
theorem agree4949 (p q : Pattern) (h : Agree support p q) : d4949 p = d4949 q := by
  simp only [d4949, h 116 (by decide), agree4948 p q h, agree4947 p q h]
theorem nonnegative4949 (p : Pattern) : 0 ≤ d4949 p :=
  nonnegative_ite (p 116) (nonnegative4948 p) (nonnegative4947 p)
def d4950 (p : Pattern) : Int := if p 160 then d4920 p else d4279 p
theorem agree4950 (p q : Pattern) (h : Agree support p q) : d4950 p = d4950 q := by
  simp only [d4950, h 160 (by decide), agree4920 p q h, agree4279 p q h]
theorem nonnegative4950 (p : Pattern) : 0 ≤ d4950 p :=
  nonnegative_ite (p 160) (nonnegative4920 p) (nonnegative4279 p)
def d4951 (p : Pattern) : Int := if p 162 then d12 p else d4211 p
theorem agree4951 (p q : Pattern) (h : Agree support p q) : d4951 p = d4951 q := by
  simp only [d4951, h 162 (by decide), agree12 p q h, agree4211 p q h]
theorem nonnegative4951 (p : Pattern) : 0 ≤ d4951 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4211 p)
def d4952 (p : Pattern) : Int := if p 161 then d12 p else d4951 p
theorem agree4952 (p q : Pattern) (h : Agree support p q) : d4952 p = d4952 q := by
  simp only [d4952, h 161 (by decide), agree12 p q h, agree4951 p q h]
theorem nonnegative4952 (p : Pattern) : 0 ≤ d4952 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4951 p)
def d4953 (p : Pattern) : Int := if p 160 then d4952 p else d4283 p
theorem agree4953 (p q : Pattern) (h : Agree support p q) : d4953 p = d4953 q := by
  simp only [d4953, h 160 (by decide), agree4952 p q h, agree4283 p q h]
theorem nonnegative4953 (p : Pattern) : 0 ≤ d4953 p :=
  nonnegative_ite (p 160) (nonnegative4952 p) (nonnegative4283 p)
def d4954 (p : Pattern) : Int := if p 141 then d4953 p else d4950 p
theorem agree4954 (p q : Pattern) (h : Agree support p q) : d4954 p = d4954 q := by
  simp only [d4954, h 141 (by decide), agree4953 p q h, agree4950 p q h]
theorem nonnegative4954 (p : Pattern) : 0 ≤ d4954 p :=
  nonnegative_ite (p 141) (nonnegative4953 p) (nonnegative4950 p)
def d4955 (p : Pattern) : Int := if p 138 then d4954 p else d4947 p
theorem agree4955 (p q : Pattern) (h : Agree support p q) : d4955 p = d4955 q := by
  simp only [d4955, h 138 (by decide), agree4954 p q h, agree4947 p q h]
theorem nonnegative4955 (p : Pattern) : 0 ≤ d4955 p :=
  nonnegative_ite (p 138) (nonnegative4954 p) (nonnegative4947 p)
def d4956 (p : Pattern) : Int := if p 163 then d41 p else d121 p
theorem agree4956 (p q : Pattern) (h : Agree support p q) : d4956 p = d4956 q := by
  simp only [d4956, h 163 (by decide), agree41 p q h, agree121 p q h]
theorem nonnegative4956 (p : Pattern) : 0 ≤ d4956 p :=
  nonnegative_ite (p 163) (nonnegative41 p) (nonnegative121 p)
def d4957 (p : Pattern) : Int := if p 162 then d12 p else d4956 p
theorem agree4957 (p q : Pattern) (h : Agree support p q) : d4957 p = d4957 q := by
  simp only [d4957, h 162 (by decide), agree12 p q h, agree4956 p q h]
theorem nonnegative4957 (p : Pattern) : 0 ≤ d4957 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4956 p)
def d4958 (p : Pattern) : Int := if p 161 then d12 p else d4957 p
theorem agree4958 (p q : Pattern) (h : Agree support p q) : d4958 p = d4958 q := by
  simp only [d4958, h 161 (by decide), agree12 p q h, agree4957 p q h]
theorem nonnegative4958 (p : Pattern) : 0 ≤ d4958 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4957 p)
def d4959 (p : Pattern) : Int := if p 160 then d4958 p else d4290 p
theorem agree4959 (p q : Pattern) (h : Agree support p q) : d4959 p = d4959 q := by
  simp only [d4959, h 160 (by decide), agree4958 p q h, agree4290 p q h]
theorem nonnegative4959 (p : Pattern) : 0 ≤ d4959 p :=
  nonnegative_ite (p 160) (nonnegative4958 p) (nonnegative4290 p)
def d4960 (p : Pattern) : Int := if p 141 then d4953 p else d4959 p
theorem agree4960 (p q : Pattern) (h : Agree support p q) : d4960 p = d4960 q := by
  simp only [d4960, h 141 (by decide), agree4953 p q h, agree4959 p q h]
theorem nonnegative4960 (p : Pattern) : 0 ≤ d4960 p :=
  nonnegative_ite (p 141) (nonnegative4953 p) (nonnegative4959 p)
def d4961 (p : Pattern) : Int := if p 138 then d12 p else d4960 p
theorem agree4961 (p q : Pattern) (h : Agree support p q) : d4961 p = d4961 q := by
  simp only [d4961, h 138 (by decide), agree12 p q h, agree4960 p q h]
theorem nonnegative4961 (p : Pattern) : 0 ≤ d4961 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4960 p)
def d4962 (p : Pattern) : Int := if p 116 then d4961 p else d4955 p
theorem agree4962 (p q : Pattern) (h : Agree support p q) : d4962 p = d4962 q := by
  simp only [d4962, h 116 (by decide), agree4961 p q h, agree4955 p q h]
theorem nonnegative4962 (p : Pattern) : 0 ≤ d4962 p :=
  nonnegative_ite (p 116) (nonnegative4961 p) (nonnegative4955 p)
def d4963 (p : Pattern) : Int := if p 115 then d4962 p else d4949 p
theorem agree4963 (p q : Pattern) (h : Agree support p q) : d4963 p = d4963 q := by
  simp only [d4963, h 115 (by decide), agree4962 p q h, agree4949 p q h]
theorem nonnegative4963 (p : Pattern) : 0 ≤ d4963 p :=
  nonnegative_ite (p 115) (nonnegative4962 p) (nonnegative4949 p)
def d4964 (p : Pattern) : Int := if p 71 then d4963 p else d4915 p
theorem agree4964 (p q : Pattern) (h : Agree support p q) : d4964 p = d4964 q := by
  simp only [d4964, h 71 (by decide), agree4963 p q h, agree4915 p q h]
theorem nonnegative4964 (p : Pattern) : 0 ≤ d4964 p :=
  nonnegative_ite (p 71) (nonnegative4963 p) (nonnegative4915 p)
def d4965 (p : Pattern) : Int := if p 49 then d4964 p else d4945 p
theorem agree4965 (p q : Pattern) (h : Agree support p q) : d4965 p = d4965 q := by
  simp only [d4965, h 49 (by decide), agree4964 p q h, agree4945 p q h]
theorem nonnegative4965 (p : Pattern) : 0 ≤ d4965 p :=
  nonnegative_ite (p 49) (nonnegative4964 p) (nonnegative4945 p)
def d4966 (p : Pattern) : Int := if p 48 then d4965 p else d4931 p
theorem agree4966 (p q : Pattern) (h : Agree support p q) : d4966 p = d4966 q := by
  simp only [d4966, h 48 (by decide), agree4965 p q h, agree4931 p q h]
theorem nonnegative4966 (p : Pattern) : 0 ≤ d4966 p :=
  nonnegative_ite (p 48) (nonnegative4965 p) (nonnegative4931 p)
def d4967 (p : Pattern) : Int := if p 182 then d0 p else d4474 p
theorem agree4967 (p q : Pattern) (h : Agree support p q) : d4967 p = d4967 q := by
  simp only [d4967, h 182 (by decide), agree0 p q h, agree4474 p q h]
theorem nonnegative4967 (p : Pattern) : 0 ≤ d4967 p :=
  nonnegative_ite (p 182) (nonnegative0 p) (nonnegative4474 p)
def d4968 (p : Pattern) : Int := if p 116 then d4730 p else d4729 p
theorem agree4968 (p q : Pattern) (h : Agree support p q) : d4968 p = d4968 q := by
  simp only [d4968, h 116 (by decide), agree4730 p q h, agree4729 p q h]
theorem nonnegative4968 (p : Pattern) : 0 ≤ d4968 p :=
  nonnegative_ite (p 116) (nonnegative4730 p) (nonnegative4729 p)
def d4969 (p : Pattern) : Int := if p 116 then d12 p else d4729 p
theorem agree4969 (p q : Pattern) (h : Agree support p q) : d4969 p = d4969 q := by
  simp only [d4969, h 116 (by decide), agree12 p q h, agree4729 p q h]
theorem nonnegative4969 (p : Pattern) : 0 ≤ d4969 p :=
  nonnegative_ite (p 116) (nonnegative12 p) (nonnegative4729 p)
def d4970 (p : Pattern) : Int := if p 115 then d4969 p else d4968 p
theorem agree4970 (p q : Pattern) (h : Agree support p q) : d4970 p = d4970 q := by
  simp only [d4970, h 115 (by decide), agree4969 p q h, agree4968 p q h]
theorem nonnegative4970 (p : Pattern) : 0 ≤ d4970 p :=
  nonnegative_ite (p 115) (nonnegative4969 p) (nonnegative4968 p)
def d4971 (p : Pattern) : Int := if p 116 then d4737 p else d4736 p
theorem agree4971 (p q : Pattern) (h : Agree support p q) : d4971 p = d4971 q := by
  simp only [d4971, h 116 (by decide), agree4737 p q h, agree4736 p q h]
theorem nonnegative4971 (p : Pattern) : 0 ≤ d4971 p :=
  nonnegative_ite (p 116) (nonnegative4737 p) (nonnegative4736 p)
def d4972 (p : Pattern) : Int := if p 116 then d12 p else d4736 p
theorem agree4972 (p q : Pattern) (h : Agree support p q) : d4972 p = d4972 q := by
  simp only [d4972, h 116 (by decide), agree12 p q h, agree4736 p q h]
theorem nonnegative4972 (p : Pattern) : 0 ≤ d4972 p :=
  nonnegative_ite (p 116) (nonnegative12 p) (nonnegative4736 p)
def d4973 (p : Pattern) : Int := if p 115 then d4972 p else d4971 p
theorem agree4973 (p q : Pattern) (h : Agree support p q) : d4973 p = d4973 q := by
  simp only [d4973, h 115 (by decide), agree4972 p q h, agree4971 p q h]
theorem nonnegative4973 (p : Pattern) : 0 ≤ d4973 p :=
  nonnegative_ite (p 115) (nonnegative4972 p) (nonnegative4971 p)
def d4974 (p : Pattern) : Int := if p 71 then d4973 p else d4970 p
theorem agree4974 (p q : Pattern) (h : Agree support p q) : d4974 p = d4974 q := by
  simp only [d4974, h 71 (by decide), agree4973 p q h, agree4970 p q h]
theorem nonnegative4974 (p : Pattern) : 0 ≤ d4974 p :=
  nonnegative_ite (p 71) (nonnegative4973 p) (nonnegative4970 p)
def d4975 (p : Pattern) : Int := if p 49 then d4974 p else d4970 p
theorem agree4975 (p q : Pattern) (h : Agree support p q) : d4975 p = d4975 q := by
  simp only [d4975, h 49 (by decide), agree4974 p q h, agree4970 p q h]
theorem nonnegative4975 (p : Pattern) : 0 ≤ d4975 p :=
  nonnegative_ite (p 49) (nonnegative4974 p) (nonnegative4970 p)
def d4976 (p : Pattern) : Int := if p 116 then d12 p else d4745 p
theorem agree4976 (p q : Pattern) (h : Agree support p q) : d4976 p = d4976 q := by
  simp only [d4976, h 116 (by decide), agree12 p q h, agree4745 p q h]
theorem nonnegative4976 (p : Pattern) : 0 ≤ d4976 p :=
  nonnegative_ite (p 116) (nonnegative12 p) (nonnegative4745 p)
def d4977 (p : Pattern) : Int := if p 115 then d4976 p else d4968 p
theorem agree4977 (p q : Pattern) (h : Agree support p q) : d4977 p = d4977 q := by
  simp only [d4977, h 115 (by decide), agree4976 p q h, agree4968 p q h]
theorem nonnegative4977 (p : Pattern) : 0 ≤ d4977 p :=
  nonnegative_ite (p 115) (nonnegative4976 p) (nonnegative4968 p)
def d4978 (p : Pattern) : Int := if p 71 then d4977 p else d4970 p
theorem agree4978 (p q : Pattern) (h : Agree support p q) : d4978 p = d4978 q := by
  simp only [d4978, h 71 (by decide), agree4977 p q h, agree4970 p q h]
theorem nonnegative4978 (p : Pattern) : 0 ≤ d4978 p :=
  nonnegative_ite (p 71) (nonnegative4977 p) (nonnegative4970 p)
def d4979 (p : Pattern) : Int := if p 116 then d4737 p else d4751 p
theorem agree4979 (p q : Pattern) (h : Agree support p q) : d4979 p = d4979 q := by
  simp only [d4979, h 116 (by decide), agree4737 p q h, agree4751 p q h]
theorem nonnegative4979 (p : Pattern) : 0 ≤ d4979 p :=
  nonnegative_ite (p 116) (nonnegative4737 p) (nonnegative4751 p)
def d4980 (p : Pattern) : Int := if p 116 then d12 p else d4754 p
theorem agree4980 (p q : Pattern) (h : Agree support p q) : d4980 p = d4980 q := by
  simp only [d4980, h 116 (by decide), agree12 p q h, agree4754 p q h]
theorem nonnegative4980 (p : Pattern) : 0 ≤ d4980 p :=
  nonnegative_ite (p 116) (nonnegative12 p) (nonnegative4754 p)
def d4981 (p : Pattern) : Int := if p 115 then d4980 p else d4979 p
theorem agree4981 (p q : Pattern) (h : Agree support p q) : d4981 p = d4981 q := by
  simp only [d4981, h 115 (by decide), agree4980 p q h, agree4979 p q h]
theorem nonnegative4981 (p : Pattern) : 0 ≤ d4981 p :=
  nonnegative_ite (p 115) (nonnegative4980 p) (nonnegative4979 p)
def d4982 (p : Pattern) : Int := if p 71 then d4981 p else d4970 p
theorem agree4982 (p q : Pattern) (h : Agree support p q) : d4982 p = d4982 q := by
  simp only [d4982, h 71 (by decide), agree4981 p q h, agree4970 p q h]
theorem nonnegative4982 (p : Pattern) : 0 ≤ d4982 p :=
  nonnegative_ite (p 71) (nonnegative4981 p) (nonnegative4970 p)
def d4983 (p : Pattern) : Int := if p 49 then d4982 p else d4978 p
theorem agree4983 (p q : Pattern) (h : Agree support p q) : d4983 p = d4983 q := by
  simp only [d4983, h 49 (by decide), agree4982 p q h, agree4978 p q h]
theorem nonnegative4983 (p : Pattern) : 0 ≤ d4983 p :=
  nonnegative_ite (p 49) (nonnegative4982 p) (nonnegative4978 p)
def d4984 (p : Pattern) : Int := if p 48 then d4983 p else d4975 p
theorem agree4984 (p q : Pattern) (h : Agree support p q) : d4984 p = d4984 q := by
  simp only [d4984, h 48 (by decide), agree4983 p q h, agree4975 p q h]
theorem nonnegative4984 (p : Pattern) : 0 ≤ d4984 p :=
  nonnegative_ite (p 48) (nonnegative4983 p) (nonnegative4975 p)
def d4985 (p : Pattern) : Int := if p 182 then d0 p else d4473 p
theorem agree4985 (p q : Pattern) (h : Agree support p q) : d4985 p = d4985 q := by
  simp only [d4985, h 182 (by decide), agree0 p q h, agree4473 p q h]
theorem nonnegative4985 (p : Pattern) : 0 ≤ d4985 p :=
  nonnegative_ite (p 182) (nonnegative0 p) (nonnegative4473 p)
def d4986 (p : Pattern) : Int := if p 182 then d1686 p else d14 p
theorem agree4986 (p q : Pattern) (h : Agree support p q) : d4986 p = d4986 q := by
  simp only [d4986, h 182 (by decide), agree1686 p q h, agree14 p q h]
theorem nonnegative4986 (p : Pattern) : 0 ≤ d4986 p :=
  nonnegative_ite (p 182) (nonnegative1686 p) (nonnegative14 p)
def d4987 (p : Pattern) : Int := if p 182 then d1696 p else d18 p
theorem agree4987 (p q : Pattern) (h : Agree support p q) : d4987 p = d4987 q := by
  simp only [d4987, h 182 (by decide), agree1696 p q h, agree18 p q h]
theorem nonnegative4987 (p : Pattern) : 0 ≤ d4987 p :=
  nonnegative_ite (p 182) (nonnegative1696 p) (nonnegative18 p)
def d4988 (p : Pattern) : Int := if p 163 then d4987 p else d4986 p
theorem agree4988 (p q : Pattern) (h : Agree support p q) : d4988 p = d4988 q := by
  simp only [d4988, h 163 (by decide), agree4987 p q h, agree4986 p q h]
theorem nonnegative4988 (p : Pattern) : 0 ≤ d4988 p :=
  nonnegative_ite (p 163) (nonnegative4987 p) (nonnegative4986 p)
def d4989 (p : Pattern) : Int := if p 162 then d4988 p else d4986 p
theorem agree4989 (p q : Pattern) (h : Agree support p q) : d4989 p = d4989 q := by
  simp only [d4989, h 162 (by decide), agree4988 p q h, agree4986 p q h]
theorem nonnegative4989 (p : Pattern) : 0 ≤ d4989 p :=
  nonnegative_ite (p 162) (nonnegative4988 p) (nonnegative4986 p)
def d4990 (p : Pattern) : Int := if p 182 then d1704 p else d24 p
theorem agree4990 (p q : Pattern) (h : Agree support p q) : d4990 p = d4990 q := by
  simp only [d4990, h 182 (by decide), agree1704 p q h, agree24 p q h]
theorem nonnegative4990 (p : Pattern) : 0 ≤ d4990 p :=
  nonnegative_ite (p 182) (nonnegative1704 p) (nonnegative24 p)
def d4991 (p : Pattern) : Int := if p 163 then d12 p else d4990 p
theorem agree4991 (p q : Pattern) (h : Agree support p q) : d4991 p = d4991 q := by
  simp only [d4991, h 163 (by decide), agree12 p q h, agree4990 p q h]
theorem nonnegative4991 (p : Pattern) : 0 ≤ d4991 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative4990 p)
def d4992 (p : Pattern) : Int := if p 162 then d4991 p else d4988 p
theorem agree4992 (p q : Pattern) (h : Agree support p q) : d4992 p = d4992 q := by
  simp only [d4992, h 162 (by decide), agree4991 p q h, agree4988 p q h]
theorem nonnegative4992 (p : Pattern) : 0 ≤ d4992 p :=
  nonnegative_ite (p 162) (nonnegative4991 p) (nonnegative4988 p)
def d4993 (p : Pattern) : Int := if p 161 then d4992 p else d4989 p
theorem agree4993 (p q : Pattern) (h : Agree support p q) : d4993 p = d4993 q := by
  simp only [d4993, h 161 (by decide), agree4992 p q h, agree4989 p q h]
theorem nonnegative4993 (p : Pattern) : 0 ≤ d4993 p :=
  nonnegative_ite (p 161) (nonnegative4992 p) (nonnegative4989 p)
def d4994 (p : Pattern) : Int := if p 182 then d1717 p else d14 p
theorem agree4994 (p q : Pattern) (h : Agree support p q) : d4994 p = d4994 q := by
  simp only [d4994, h 182 (by decide), agree1717 p q h, agree14 p q h]
theorem nonnegative4994 (p : Pattern) : 0 ≤ d4994 p :=
  nonnegative_ite (p 182) (nonnegative1717 p) (nonnegative14 p)
def d4995 (p : Pattern) : Int := if p 182 then d1724 p else d14 p
theorem agree4995 (p q : Pattern) (h : Agree support p q) : d4995 p = d4995 q := by
  simp only [d4995, h 182 (by decide), agree1724 p q h, agree14 p q h]
theorem nonnegative4995 (p : Pattern) : 0 ≤ d4995 p :=
  nonnegative_ite (p 182) (nonnegative1724 p) (nonnegative14 p)
def d4996 (p : Pattern) : Int := if p 163 then d4995 p else d4994 p
theorem agree4996 (p q : Pattern) (h : Agree support p q) : d4996 p = d4996 q := by
  simp only [d4996, h 163 (by decide), agree4995 p q h, agree4994 p q h]
theorem nonnegative4996 (p : Pattern) : 0 ≤ d4996 p :=
  nonnegative_ite (p 163) (nonnegative4995 p) (nonnegative4994 p)
def d4997 (p : Pattern) : Int := if p 182 then d1729 p else d14 p
theorem agree4997 (p q : Pattern) (h : Agree support p q) : d4997 p = d4997 q := by
  simp only [d4997, h 182 (by decide), agree1729 p q h, agree14 p q h]
theorem nonnegative4997 (p : Pattern) : 0 ≤ d4997 p :=
  nonnegative_ite (p 182) (nonnegative1729 p) (nonnegative14 p)
def d4998 (p : Pattern) : Int := if p 163 then d43 p else d4997 p
theorem agree4998 (p q : Pattern) (h : Agree support p q) : d4998 p = d4998 q := by
  simp only [d4998, h 163 (by decide), agree43 p q h, agree4997 p q h]
theorem nonnegative4998 (p : Pattern) : 0 ≤ d4998 p :=
  nonnegative_ite (p 163) (nonnegative43 p) (nonnegative4997 p)
def d4999 (p : Pattern) : Int := if p 162 then d4998 p else d4996 p
theorem agree4999 (p q : Pattern) (h : Agree support p q) : d4999 p = d4999 q := by
  simp only [d4999, h 162 (by decide), agree4998 p q h, agree4996 p q h]
theorem nonnegative4999 (p : Pattern) : 0 ≤ d4999 p :=
  nonnegative_ite (p 162) (nonnegative4998 p) (nonnegative4996 p)
def d5000 (p : Pattern) : Int := if p 161 then d50 p else d4999 p
theorem agree5000 (p q : Pattern) (h : Agree support p q) : d5000 p = d5000 q := by
  simp only [d5000, h 161 (by decide), agree50 p q h, agree4999 p q h]
theorem nonnegative5000 (p : Pattern) : 0 ≤ d5000 p :=
  nonnegative_ite (p 161) (nonnegative50 p) (nonnegative4999 p)
def d5001 (p : Pattern) : Int := if p 160 then d5000 p else d4993 p
theorem agree5001 (p q : Pattern) (h : Agree support p q) : d5001 p = d5001 q := by
  simp only [d5001, h 160 (by decide), agree5000 p q h, agree4993 p q h]
theorem nonnegative5001 (p : Pattern) : 0 ≤ d5001 p :=
  nonnegative_ite (p 160) (nonnegative5000 p) (nonnegative4993 p)
def d5002 (p : Pattern) : Int := if p 182 then d1745 p else d31 p
theorem agree5002 (p q : Pattern) (h : Agree support p q) : d5002 p = d5002 q := by
  simp only [d5002, h 182 (by decide), agree1745 p q h, agree31 p q h]
theorem nonnegative5002 (p : Pattern) : 0 ≤ d5002 p :=
  nonnegative_ite (p 182) (nonnegative1745 p) (nonnegative31 p)
def d5003 (p : Pattern) : Int := if p 163 then d5002 p else d4986 p
theorem agree5003 (p q : Pattern) (h : Agree support p q) : d5003 p = d5003 q := by
  simp only [d5003, h 163 (by decide), agree5002 p q h, agree4986 p q h]
theorem nonnegative5003 (p : Pattern) : 0 ≤ d5003 p :=
  nonnegative_ite (p 163) (nonnegative5002 p) (nonnegative4986 p)
def d5004 (p : Pattern) : Int := if p 163 then d4990 p else d4987 p
theorem agree5004 (p q : Pattern) (h : Agree support p q) : d5004 p = d5004 q := by
  simp only [d5004, h 163 (by decide), agree4990 p q h, agree4987 p q h]
theorem nonnegative5004 (p : Pattern) : 0 ≤ d5004 p :=
  nonnegative_ite (p 163) (nonnegative4990 p) (nonnegative4987 p)
def d5005 (p : Pattern) : Int := if p 162 then d5004 p else d5003 p
theorem agree5005 (p q : Pattern) (h : Agree support p q) : d5005 p = d5005 q := by
  simp only [d5005, h 162 (by decide), agree5004 p q h, agree5003 p q h]
theorem nonnegative5005 (p : Pattern) : 0 ≤ d5005 p :=
  nonnegative_ite (p 162) (nonnegative5004 p) (nonnegative5003 p)
def d5006 (p : Pattern) : Int := if p 182 then d1752 p else d58 p
theorem agree5006 (p q : Pattern) (h : Agree support p q) : d5006 p = d5006 q := by
  simp only [d5006, h 182 (by decide), agree1752 p q h, agree58 p q h]
theorem nonnegative5006 (p : Pattern) : 0 ≤ d5006 p :=
  nonnegative_ite (p 182) (nonnegative1752 p) (nonnegative58 p)
def d5007 (p : Pattern) : Int := if p 163 then d5006 p else d4987 p
theorem agree5007 (p q : Pattern) (h : Agree support p q) : d5007 p = d5007 q := by
  simp only [d5007, h 163 (by decide), agree5006 p q h, agree4987 p q h]
theorem nonnegative5007 (p : Pattern) : 0 ≤ d5007 p :=
  nonnegative_ite (p 163) (nonnegative5006 p) (nonnegative4987 p)
def d5008 (p : Pattern) : Int := if p 182 then d1729 p else d40 p
theorem agree5008 (p q : Pattern) (h : Agree support p q) : d5008 p = d5008 q := by
  simp only [d5008, h 182 (by decide), agree1729 p q h, agree40 p q h]
theorem nonnegative5008 (p : Pattern) : 0 ≤ d5008 p :=
  nonnegative_ite (p 182) (nonnegative1729 p) (nonnegative40 p)
def d5009 (p : Pattern) : Int := if p 163 then d12 p else d5008 p
theorem agree5009 (p q : Pattern) (h : Agree support p q) : d5009 p = d5009 q := by
  simp only [d5009, h 163 (by decide), agree12 p q h, agree5008 p q h]
theorem nonnegative5009 (p : Pattern) : 0 ≤ d5009 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5008 p)
def d5010 (p : Pattern) : Int := if p 162 then d5009 p else d5007 p
theorem agree5010 (p q : Pattern) (h : Agree support p q) : d5010 p = d5010 q := by
  simp only [d5010, h 162 (by decide), agree5009 p q h, agree5007 p q h]
theorem nonnegative5010 (p : Pattern) : 0 ≤ d5010 p :=
  nonnegative_ite (p 162) (nonnegative5009 p) (nonnegative5007 p)
def d5011 (p : Pattern) : Int := if p 161 then d5010 p else d5005 p
theorem agree5011 (p q : Pattern) (h : Agree support p q) : d5011 p = d5011 q := by
  simp only [d5011, h 161 (by decide), agree5010 p q h, agree5005 p q h]
theorem nonnegative5011 (p : Pattern) : 0 ≤ d5011 p :=
  nonnegative_ite (p 161) (nonnegative5010 p) (nonnegative5005 p)
def d5012 (p : Pattern) : Int := if p 163 then d66 p else d4995 p
theorem agree5012 (p q : Pattern) (h : Agree support p q) : d5012 p = d5012 q := by
  simp only [d5012, h 163 (by decide), agree66 p q h, agree4995 p q h]
theorem nonnegative5012 (p : Pattern) : 0 ≤ d5012 p :=
  nonnegative_ite (p 163) (nonnegative66 p) (nonnegative4995 p)
def d5013 (p : Pattern) : Int := if p 162 then d68 p else d5012 p
theorem agree5013 (p q : Pattern) (h : Agree support p q) : d5013 p = d5013 q := by
  simp only [d5013, h 162 (by decide), agree68 p q h, agree5012 p q h]
theorem nonnegative5013 (p : Pattern) : 0 ≤ d5013 p :=
  nonnegative_ite (p 162) (nonnegative68 p) (nonnegative5012 p)
def d5014 (p : Pattern) : Int := if p 161 then d74 p else d5013 p
theorem agree5014 (p q : Pattern) (h : Agree support p q) : d5014 p = d5014 q := by
  simp only [d5014, h 161 (by decide), agree74 p q h, agree5013 p q h]
theorem nonnegative5014 (p : Pattern) : 0 ≤ d5014 p :=
  nonnegative_ite (p 161) (nonnegative74 p) (nonnegative5013 p)
def d5015 (p : Pattern) : Int := if p 160 then d5014 p else d5011 p
theorem agree5015 (p q : Pattern) (h : Agree support p q) : d5015 p = d5015 q := by
  simp only [d5015, h 160 (by decide), agree5014 p q h, agree5011 p q h]
theorem nonnegative5015 (p : Pattern) : 0 ≤ d5015 p :=
  nonnegative_ite (p 160) (nonnegative5014 p) (nonnegative5011 p)
def d5016 (p : Pattern) : Int := if p 141 then d5015 p else d5001 p
theorem agree5016 (p q : Pattern) (h : Agree support p q) : d5016 p = d5016 q := by
  simp only [d5016, h 141 (by decide), agree5015 p q h, agree5001 p q h]
theorem nonnegative5016 (p : Pattern) : 0 ≤ d5016 p :=
  nonnegative_ite (p 141) (nonnegative5015 p) (nonnegative5001 p)
def d5017 (p : Pattern) : Int := if p 182 then d1772 p else d14 p
theorem agree5017 (p q : Pattern) (h : Agree support p q) : d5017 p = d5017 q := by
  simp only [d5017, h 182 (by decide), agree1772 p q h, agree14 p q h]
theorem nonnegative5017 (p : Pattern) : 0 ≤ d5017 p :=
  nonnegative_ite (p 182) (nonnegative1772 p) (nonnegative14 p)
def d5018 (p : Pattern) : Int := if p 182 then d1781 p else d14 p
theorem agree5018 (p q : Pattern) (h : Agree support p q) : d5018 p = d5018 q := by
  simp only [d5018, h 182 (by decide), agree1781 p q h, agree14 p q h]
theorem nonnegative5018 (p : Pattern) : 0 ≤ d5018 p :=
  nonnegative_ite (p 182) (nonnegative1781 p) (nonnegative14 p)
def d5019 (p : Pattern) : Int := if p 163 then d5018 p else d5017 p
theorem agree5019 (p q : Pattern) (h : Agree support p q) : d5019 p = d5019 q := by
  simp only [d5019, h 163 (by decide), agree5018 p q h, agree5017 p q h]
theorem nonnegative5019 (p : Pattern) : 0 ≤ d5019 p :=
  nonnegative_ite (p 163) (nonnegative5018 p) (nonnegative5017 p)
def d5020 (p : Pattern) : Int := if p 182 then d1788 p else d14 p
theorem agree5020 (p q : Pattern) (h : Agree support p q) : d5020 p = d5020 q := by
  simp only [d5020, h 182 (by decide), agree1788 p q h, agree14 p q h]
theorem nonnegative5020 (p : Pattern) : 0 ≤ d5020 p :=
  nonnegative_ite (p 182) (nonnegative1788 p) (nonnegative14 p)
def d5021 (p : Pattern) : Int := if p 182 then d1797 p else d18 p
theorem agree5021 (p q : Pattern) (h : Agree support p q) : d5021 p = d5021 q := by
  simp only [d5021, h 182 (by decide), agree1797 p q h, agree18 p q h]
theorem nonnegative5021 (p : Pattern) : 0 ≤ d5021 p :=
  nonnegative_ite (p 182) (nonnegative1797 p) (nonnegative18 p)
def d5022 (p : Pattern) : Int := if p 163 then d5021 p else d5020 p
theorem agree5022 (p q : Pattern) (h : Agree support p q) : d5022 p = d5022 q := by
  simp only [d5022, h 163 (by decide), agree5021 p q h, agree5020 p q h]
theorem nonnegative5022 (p : Pattern) : 0 ≤ d5022 p :=
  nonnegative_ite (p 163) (nonnegative5021 p) (nonnegative5020 p)
def d5023 (p : Pattern) : Int := if p 162 then d5022 p else d5019 p
theorem agree5023 (p q : Pattern) (h : Agree support p q) : d5023 p = d5023 q := by
  simp only [d5023, h 162 (by decide), agree5022 p q h, agree5019 p q h]
theorem nonnegative5023 (p : Pattern) : 0 ≤ d5023 p :=
  nonnegative_ite (p 162) (nonnegative5022 p) (nonnegative5019 p)
def d5024 (p : Pattern) : Int := if p 182 then d1803 p else d24 p
theorem agree5024 (p q : Pattern) (h : Agree support p q) : d5024 p = d5024 q := by
  simp only [d5024, h 182 (by decide), agree1803 p q h, agree24 p q h]
theorem nonnegative5024 (p : Pattern) : 0 ≤ d5024 p :=
  nonnegative_ite (p 182) (nonnegative1803 p) (nonnegative24 p)
def d5025 (p : Pattern) : Int := if p 163 then d12 p else d5024 p
theorem agree5025 (p q : Pattern) (h : Agree support p q) : d5025 p = d5025 q := by
  simp only [d5025, h 163 (by decide), agree12 p q h, agree5024 p q h]
theorem nonnegative5025 (p : Pattern) : 0 ≤ d5025 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5024 p)
def d5026 (p : Pattern) : Int := if p 162 then d5025 p else d5022 p
theorem agree5026 (p q : Pattern) (h : Agree support p q) : d5026 p = d5026 q := by
  simp only [d5026, h 162 (by decide), agree5025 p q h, agree5022 p q h]
theorem nonnegative5026 (p : Pattern) : 0 ≤ d5026 p :=
  nonnegative_ite (p 162) (nonnegative5025 p) (nonnegative5022 p)
def d5027 (p : Pattern) : Int := if p 161 then d5026 p else d5023 p
theorem agree5027 (p q : Pattern) (h : Agree support p q) : d5027 p = d5027 q := by
  simp only [d5027, h 161 (by decide), agree5026 p q h, agree5023 p q h]
theorem nonnegative5027 (p : Pattern) : 0 ≤ d5027 p :=
  nonnegative_ite (p 161) (nonnegative5026 p) (nonnegative5023 p)
def d5028 (p : Pattern) : Int := if p 182 then d1717 p else d31 p
theorem agree5028 (p q : Pattern) (h : Agree support p q) : d5028 p = d5028 q := by
  simp only [d5028, h 182 (by decide), agree1717 p q h, agree31 p q h]
theorem nonnegative5028 (p : Pattern) : 0 ≤ d5028 p :=
  nonnegative_ite (p 182) (nonnegative1717 p) (nonnegative31 p)
def d5029 (p : Pattern) : Int := if p 182 then d1724 p else d35 p
theorem agree5029 (p q : Pattern) (h : Agree support p q) : d5029 p = d5029 q := by
  simp only [d5029, h 182 (by decide), agree1724 p q h, agree35 p q h]
theorem nonnegative5029 (p : Pattern) : 0 ≤ d5029 p :=
  nonnegative_ite (p 182) (nonnegative1724 p) (nonnegative35 p)
def d5030 (p : Pattern) : Int := if p 163 then d5029 p else d5028 p
theorem agree5030 (p q : Pattern) (h : Agree support p q) : d5030 p = d5030 q := by
  simp only [d5030, h 163 (by decide), agree5029 p q h, agree5028 p q h]
theorem nonnegative5030 (p : Pattern) : 0 ≤ d5030 p :=
  nonnegative_ite (p 163) (nonnegative5029 p) (nonnegative5028 p)
def d5031 (p : Pattern) : Int := if p 162 then d5009 p else d5030 p
theorem agree5031 (p q : Pattern) (h : Agree support p q) : d5031 p = d5031 q := by
  simp only [d5031, h 162 (by decide), agree5009 p q h, agree5030 p q h]
theorem nonnegative5031 (p : Pattern) : 0 ≤ d5031 p :=
  nonnegative_ite (p 162) (nonnegative5009 p) (nonnegative5030 p)
def d5032 (p : Pattern) : Int := if p 161 then d12 p else d5031 p
theorem agree5032 (p q : Pattern) (h : Agree support p q) : d5032 p = d5032 q := by
  simp only [d5032, h 161 (by decide), agree12 p q h, agree5031 p q h]
theorem nonnegative5032 (p : Pattern) : 0 ≤ d5032 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5031 p)
def d5033 (p : Pattern) : Int := if p 160 then d5032 p else d5027 p
theorem agree5033 (p q : Pattern) (h : Agree support p q) : d5033 p = d5033 q := by
  simp only [d5033, h 160 (by decide), agree5032 p q h, agree5027 p q h]
theorem nonnegative5033 (p : Pattern) : 0 ≤ d5033 p :=
  nonnegative_ite (p 160) (nonnegative5032 p) (nonnegative5027 p)
def d5034 (p : Pattern) : Int := if p 163 then d5028 p else d5018 p
theorem agree5034 (p q : Pattern) (h : Agree support p q) : d5034 p = d5034 q := by
  simp only [d5034, h 163 (by decide), agree5028 p q h, agree5018 p q h]
theorem nonnegative5034 (p : Pattern) : 0 ≤ d5034 p :=
  nonnegative_ite (p 163) (nonnegative5028 p) (nonnegative5018 p)
def d5035 (p : Pattern) : Int := if p 163 then d5024 p else d5021 p
theorem agree5035 (p q : Pattern) (h : Agree support p q) : d5035 p = d5035 q := by
  simp only [d5035, h 163 (by decide), agree5024 p q h, agree5021 p q h]
theorem nonnegative5035 (p : Pattern) : 0 ≤ d5035 p :=
  nonnegative_ite (p 163) (nonnegative5024 p) (nonnegative5021 p)
def d5036 (p : Pattern) : Int := if p 162 then d5035 p else d5034 p
theorem agree5036 (p q : Pattern) (h : Agree support p q) : d5036 p = d5036 q := by
  simp only [d5036, h 162 (by decide), agree5035 p q h, agree5034 p q h]
theorem nonnegative5036 (p : Pattern) : 0 ≤ d5036 p :=
  nonnegative_ite (p 162) (nonnegative5035 p) (nonnegative5034 p)
def d5037 (p : Pattern) : Int := if p 163 then d5006 p else d5021 p
theorem agree5037 (p q : Pattern) (h : Agree support p q) : d5037 p = d5037 q := by
  simp only [d5037, h 163 (by decide), agree5006 p q h, agree5021 p q h]
theorem nonnegative5037 (p : Pattern) : 0 ≤ d5037 p :=
  nonnegative_ite (p 163) (nonnegative5006 p) (nonnegative5021 p)
def d5038 (p : Pattern) : Int := if p 162 then d5009 p else d5037 p
theorem agree5038 (p q : Pattern) (h : Agree support p q) : d5038 p = d5038 q := by
  simp only [d5038, h 162 (by decide), agree5009 p q h, agree5037 p q h]
theorem nonnegative5038 (p : Pattern) : 0 ≤ d5038 p :=
  nonnegative_ite (p 162) (nonnegative5009 p) (nonnegative5037 p)
def d5039 (p : Pattern) : Int := if p 161 then d5038 p else d5036 p
theorem agree5039 (p q : Pattern) (h : Agree support p q) : d5039 p = d5039 q := by
  simp only [d5039, h 161 (by decide), agree5038 p q h, agree5036 p q h]
theorem nonnegative5039 (p : Pattern) : 0 ≤ d5039 p :=
  nonnegative_ite (p 161) (nonnegative5038 p) (nonnegative5036 p)
end NetHack.Sokoban22Refined85
