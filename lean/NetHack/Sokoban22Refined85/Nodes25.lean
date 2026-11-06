/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d3000 (p : Pattern) : Int := if p 162 then d2999 p else d2997 p
theorem agree3000 (p q : Pattern) (h : Agree support p q) : d3000 p = d3000 q := by
  simp only [d3000, h 162 (by decide), agree2999 p q h, agree2997 p q h]
theorem nonnegative3000 (p : Pattern) : 0 ≤ d3000 p :=
  nonnegative_ite (p 162) (nonnegative2999 p) (nonnegative2997 p)
def d3001 (p : Pattern) : Int := if p 161 then d3000 p else d2998 p
theorem agree3001 (p q : Pattern) (h : Agree support p q) : d3001 p = d3001 q := by
  simp only [d3001, h 161 (by decide), agree3000 p q h, agree2998 p q h]
theorem nonnegative3001 (p : Pattern) : 0 ≤ d3001 p :=
  nonnegative_ite (p 161) (nonnegative3000 p) (nonnegative2998 p)
def d3002 (p : Pattern) : Int := if p 204 then d1957 p else d103 p
theorem agree3002 (p q : Pattern) (h : Agree support p q) : d3002 p = d3002 q := by
  simp only [d3002, h 204 (by decide), agree1957 p q h, agree103 p q h]
theorem nonnegative3002 (p : Pattern) : 0 ≤ d3002 p :=
  nonnegative_ite (p 204) (nonnegative1957 p) (nonnegative103 p)
def d3003 (p : Pattern) : Int := if p 182 then d1899 p else d3002 p
theorem agree3003 (p q : Pattern) (h : Agree support p q) : d3003 p = d3003 q := by
  simp only [d3003, h 182 (by decide), agree1899 p q h, agree3002 p q h]
theorem nonnegative3003 (p : Pattern) : 0 ≤ d3003 p :=
  nonnegative_ite (p 182) (nonnegative1899 p) (nonnegative3002 p)
def d3004 (p : Pattern) : Int := if p 182 then d1906 p else d3002 p
theorem agree3004 (p q : Pattern) (h : Agree support p q) : d3004 p = d3004 q := by
  simp only [d3004, h 182 (by decide), agree1906 p q h, agree3002 p q h]
theorem nonnegative3004 (p : Pattern) : 0 ≤ d3004 p :=
  nonnegative_ite (p 182) (nonnegative1906 p) (nonnegative3002 p)
def d3005 (p : Pattern) : Int := if p 163 then d3004 p else d3003 p
theorem agree3005 (p q : Pattern) (h : Agree support p q) : d3005 p = d3005 q := by
  simp only [d3005, h 163 (by decide), agree3004 p q h, agree3003 p q h]
theorem nonnegative3005 (p : Pattern) : 0 ≤ d3005 p :=
  nonnegative_ite (p 163) (nonnegative3004 p) (nonnegative3003 p)
def d3006 (p : Pattern) : Int := if p 182 then d12 p else d3002 p
theorem agree3006 (p q : Pattern) (h : Agree support p q) : d3006 p = d3006 q := by
  simp only [d3006, h 182 (by decide), agree12 p q h, agree3002 p q h]
theorem nonnegative3006 (p : Pattern) : 0 ≤ d3006 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3002 p)
def d3007 (p : Pattern) : Int := if p 204 then d1966 p else d107 p
theorem agree3007 (p q : Pattern) (h : Agree support p q) : d3007 p = d3007 q := by
  simp only [d3007, h 204 (by decide), agree1966 p q h, agree107 p q h]
theorem nonnegative3007 (p : Pattern) : 0 ≤ d3007 p :=
  nonnegative_ite (p 204) (nonnegative1966 p) (nonnegative107 p)
def d3008 (p : Pattern) : Int := if p 182 then d12 p else d3007 p
theorem agree3008 (p q : Pattern) (h : Agree support p q) : d3008 p = d3008 q := by
  simp only [d3008, h 182 (by decide), agree12 p q h, agree3007 p q h]
theorem nonnegative3008 (p : Pattern) : 0 ≤ d3008 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3007 p)
def d3009 (p : Pattern) : Int := if p 163 then d3008 p else d3006 p
theorem agree3009 (p q : Pattern) (h : Agree support p q) : d3009 p = d3009 q := by
  simp only [d3009, h 163 (by decide), agree3008 p q h, agree3006 p q h]
theorem nonnegative3009 (p : Pattern) : 0 ≤ d3009 p :=
  nonnegative_ite (p 163) (nonnegative3008 p) (nonnegative3006 p)
def d3010 (p : Pattern) : Int := if p 162 then d3009 p else d3005 p
theorem agree3010 (p q : Pattern) (h : Agree support p q) : d3010 p = d3010 q := by
  simp only [d3010, h 162 (by decide), agree3009 p q h, agree3005 p q h]
theorem nonnegative3010 (p : Pattern) : 0 ≤ d3010 p :=
  nonnegative_ite (p 162) (nonnegative3009 p) (nonnegative3005 p)
def d3011 (p : Pattern) : Int := if p 163 then d12 p else d2940 p
theorem agree3011 (p q : Pattern) (h : Agree support p q) : d3011 p = d3011 q := by
  simp only [d3011, h 163 (by decide), agree12 p q h, agree2940 p q h]
theorem nonnegative3011 (p : Pattern) : 0 ≤ d3011 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2940 p)
def d3012 (p : Pattern) : Int := if p 162 then d3011 p else d3009 p
theorem agree3012 (p q : Pattern) (h : Agree support p q) : d3012 p = d3012 q := by
  simp only [d3012, h 162 (by decide), agree3011 p q h, agree3009 p q h]
theorem nonnegative3012 (p : Pattern) : 0 ≤ d3012 p :=
  nonnegative_ite (p 162) (nonnegative3011 p) (nonnegative3009 p)
def d3013 (p : Pattern) : Int := if p 161 then d3012 p else d3010 p
theorem agree3013 (p q : Pattern) (h : Agree support p q) : d3013 p = d3013 q := by
  simp only [d3013, h 161 (by decide), agree3012 p q h, agree3010 p q h]
theorem nonnegative3013 (p : Pattern) : 0 ≤ d3013 p :=
  nonnegative_ite (p 161) (nonnegative3012 p) (nonnegative3010 p)
def d3014 (p : Pattern) : Int := if p 160 then d3013 p else d3001 p
theorem agree3014 (p q : Pattern) (h : Agree support p q) : d3014 p = d3014 q := by
  simp only [d3014, h 160 (by decide), agree3013 p q h, agree3001 p q h]
theorem nonnegative3014 (p : Pattern) : 0 ≤ d3014 p :=
  nonnegative_ite (p 160) (nonnegative3013 p) (nonnegative3001 p)
def d3015 (p : Pattern) : Int := if p 204 then d2125 p else d116 p
theorem agree3015 (p q : Pattern) (h : Agree support p q) : d3015 p = d3015 q := by
  simp only [d3015, h 204 (by decide), agree2125 p q h, agree116 p q h]
theorem nonnegative3015 (p : Pattern) : 0 ≤ d3015 p :=
  nonnegative_ite (p 204) (nonnegative2125 p) (nonnegative116 p)
def d3016 (p : Pattern) : Int := if p 182 then d1922 p else d3015 p
theorem agree3016 (p q : Pattern) (h : Agree support p q) : d3016 p = d3016 q := by
  simp only [d3016, h 182 (by decide), agree1922 p q h, agree3015 p q h]
theorem nonnegative3016 (p : Pattern) : 0 ≤ d3016 p :=
  nonnegative_ite (p 182) (nonnegative1922 p) (nonnegative3015 p)
def d3017 (p : Pattern) : Int := if p 163 then d3016 p else d2994 p
theorem agree3017 (p q : Pattern) (h : Agree support p q) : d3017 p = d3017 q := by
  simp only [d3017, h 163 (by decide), agree3016 p q h, agree2994 p q h]
theorem nonnegative3017 (p : Pattern) : 0 ≤ d3017 p :=
  nonnegative_ite (p 163) (nonnegative3016 p) (nonnegative2994 p)
def d3018 (p : Pattern) : Int := if p 163 then d2928 p else d2996 p
theorem agree3018 (p q : Pattern) (h : Agree support p q) : d3018 p = d3018 q := by
  simp only [d3018, h 163 (by decide), agree2928 p q h, agree2996 p q h]
theorem nonnegative3018 (p : Pattern) : 0 ≤ d3018 p :=
  nonnegative_ite (p 163) (nonnegative2928 p) (nonnegative2996 p)
def d3019 (p : Pattern) : Int := if p 162 then d3018 p else d3017 p
theorem agree3019 (p q : Pattern) (h : Agree support p q) : d3019 p = d3019 q := by
  simp only [d3019, h 162 (by decide), agree3018 p q h, agree3017 p q h]
theorem nonnegative3019 (p : Pattern) : 0 ≤ d3019 p :=
  nonnegative_ite (p 162) (nonnegative3018 p) (nonnegative3017 p)
def d3020 (p : Pattern) : Int := if p 163 then d2931 p else d2996 p
theorem agree3020 (p q : Pattern) (h : Agree support p q) : d3020 p = d3020 q := by
  simp only [d3020, h 163 (by decide), agree2931 p q h, agree2996 p q h]
theorem nonnegative3020 (p : Pattern) : 0 ≤ d3020 p :=
  nonnegative_ite (p 163) (nonnegative2931 p) (nonnegative2996 p)
def d3021 (p : Pattern) : Int := if p 162 then d12 p else d3020 p
theorem agree3021 (p q : Pattern) (h : Agree support p q) : d3021 p = d3021 q := by
  simp only [d3021, h 162 (by decide), agree12 p q h, agree3020 p q h]
theorem nonnegative3021 (p : Pattern) : 0 ≤ d3021 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3020 p)
def d3022 (p : Pattern) : Int := if p 161 then d3021 p else d3019 p
theorem agree3022 (p q : Pattern) (h : Agree support p q) : d3022 p = d3022 q := by
  simp only [d3022, h 161 (by decide), agree3021 p q h, agree3019 p q h]
theorem nonnegative3022 (p : Pattern) : 0 ≤ d3022 p :=
  nonnegative_ite (p 161) (nonnegative3021 p) (nonnegative3019 p)
def d3023 (p : Pattern) : Int := if p 204 then d1898 p else d116 p
theorem agree3023 (p q : Pattern) (h : Agree support p q) : d3023 p = d3023 q := by
  simp only [d3023, h 204 (by decide), agree1898 p q h, agree116 p q h]
theorem nonnegative3023 (p : Pattern) : 0 ≤ d3023 p :=
  nonnegative_ite (p 204) (nonnegative1898 p) (nonnegative116 p)
def d3024 (p : Pattern) : Int := if p 182 then d12 p else d3023 p
theorem agree3024 (p q : Pattern) (h : Agree support p q) : d3024 p = d3024 q := by
  simp only [d3024, h 182 (by decide), agree12 p q h, agree3023 p q h]
theorem nonnegative3024 (p : Pattern) : 0 ≤ d3024 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3023 p)
def d3025 (p : Pattern) : Int := if p 163 then d3024 p else d3004 p
theorem agree3025 (p q : Pattern) (h : Agree support p q) : d3025 p = d3025 q := by
  simp only [d3025, h 163 (by decide), agree3024 p q h, agree3004 p q h]
theorem nonnegative3025 (p : Pattern) : 0 ≤ d3025 p :=
  nonnegative_ite (p 163) (nonnegative3024 p) (nonnegative3004 p)
def d3026 (p : Pattern) : Int := if p 163 then d2940 p else d3008 p
theorem agree3026 (p q : Pattern) (h : Agree support p q) : d3026 p = d3026 q := by
  simp only [d3026, h 163 (by decide), agree2940 p q h, agree3008 p q h]
theorem nonnegative3026 (p : Pattern) : 0 ≤ d3026 p :=
  nonnegative_ite (p 163) (nonnegative2940 p) (nonnegative3008 p)
def d3027 (p : Pattern) : Int := if p 162 then d3026 p else d3025 p
theorem agree3027 (p q : Pattern) (h : Agree support p q) : d3027 p = d3027 q := by
  simp only [d3027, h 162 (by decide), agree3026 p q h, agree3025 p q h]
theorem nonnegative3027 (p : Pattern) : 0 ≤ d3027 p :=
  nonnegative_ite (p 162) (nonnegative3026 p) (nonnegative3025 p)
def d3028 (p : Pattern) : Int := if p 163 then d2942 p else d3008 p
theorem agree3028 (p q : Pattern) (h : Agree support p q) : d3028 p = d3028 q := by
  simp only [d3028, h 163 (by decide), agree2942 p q h, agree3008 p q h]
theorem nonnegative3028 (p : Pattern) : 0 ≤ d3028 p :=
  nonnegative_ite (p 163) (nonnegative2942 p) (nonnegative3008 p)
def d3029 (p : Pattern) : Int := if p 162 then d12 p else d3028 p
theorem agree3029 (p q : Pattern) (h : Agree support p q) : d3029 p = d3029 q := by
  simp only [d3029, h 162 (by decide), agree12 p q h, agree3028 p q h]
theorem nonnegative3029 (p : Pattern) : 0 ≤ d3029 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3028 p)
def d3030 (p : Pattern) : Int := if p 161 then d3029 p else d3027 p
theorem agree3030 (p q : Pattern) (h : Agree support p q) : d3030 p = d3030 q := by
  simp only [d3030, h 161 (by decide), agree3029 p q h, agree3027 p q h]
theorem nonnegative3030 (p : Pattern) : 0 ≤ d3030 p :=
  nonnegative_ite (p 161) (nonnegative3029 p) (nonnegative3027 p)
def d3031 (p : Pattern) : Int := if p 160 then d3030 p else d3022 p
theorem agree3031 (p q : Pattern) (h : Agree support p q) : d3031 p = d3031 q := by
  simp only [d3031, h 160 (by decide), agree3030 p q h, agree3022 p q h]
theorem nonnegative3031 (p : Pattern) : 0 ≤ d3031 p :=
  nonnegative_ite (p 160) (nonnegative3030 p) (nonnegative3022 p)
def d3032 (p : Pattern) : Int := if p 141 then d3031 p else d3014 p
theorem agree3032 (p q : Pattern) (h : Agree support p q) : d3032 p = d3032 q := by
  simp only [d3032, h 141 (by decide), agree3031 p q h, agree3014 p q h]
theorem nonnegative3032 (p : Pattern) : 0 ≤ d3032 p :=
  nonnegative_ite (p 141) (nonnegative3031 p) (nonnegative3014 p)
def d3033 (p : Pattern) : Int := if p 204 then d2108 p else d103 p
theorem agree3033 (p q : Pattern) (h : Agree support p q) : d3033 p = d3033 q := by
  simp only [d3033, h 204 (by decide), agree2108 p q h, agree103 p q h]
theorem nonnegative3033 (p : Pattern) : 0 ≤ d3033 p :=
  nonnegative_ite (p 204) (nonnegative2108 p) (nonnegative103 p)
def d3034 (p : Pattern) : Int := if p 182 then d1943 p else d3033 p
theorem agree3034 (p q : Pattern) (h : Agree support p q) : d3034 p = d3034 q := by
  simp only [d3034, h 182 (by decide), agree1943 p q h, agree3033 p q h]
theorem nonnegative3034 (p : Pattern) : 0 ≤ d3034 p :=
  nonnegative_ite (p 182) (nonnegative1943 p) (nonnegative3033 p)
def d3035 (p : Pattern) : Int := if p 247 then d11 p else d1 p
theorem agree3035 (p q : Pattern) (h : Agree support p q) : d3035 p = d3035 q := by
  simp only [d3035, h 247 (by decide), agree11 p q h, agree1 p q h]
theorem nonnegative3035 (p : Pattern) : 0 ≤ d3035 p :=
  nonnegative_ite (p 247) (nonnegative11 p) (nonnegative1 p)
def d3036 (p : Pattern) : Int := if p 246 then d57 p else d3035 p
theorem agree3036 (p q : Pattern) (h : Agree support p q) : d3036 p = d3036 q := by
  simp only [d3036, h 246 (by decide), agree57 p q h, agree3035 p q h]
theorem nonnegative3036 (p : Pattern) : 0 ≤ d3036 p :=
  nonnegative_ite (p 246) (nonnegative57 p) (nonnegative3035 p)
def d3037 (p : Pattern) : Int := if p 225 then d3036 p else d1940 p
theorem agree3037 (p q : Pattern) (h : Agree support p q) : d3037 p = d3037 q := by
  simp only [d3037, h 225 (by decide), agree3036 p q h, agree1940 p q h]
theorem nonnegative3037 (p : Pattern) : 0 ≤ d3037 p :=
  nonnegative_ite (p 225) (nonnegative3036 p) (nonnegative1940 p)
def d3038 (p : Pattern) : Int := if p 224 then d3037 p else d1947 p
theorem agree3038 (p q : Pattern) (h : Agree support p q) : d3038 p = d3038 q := by
  simp only [d3038, h 224 (by decide), agree3037 p q h, agree1947 p q h]
theorem nonnegative3038 (p : Pattern) : 0 ≤ d3038 p :=
  nonnegative_ite (p 224) (nonnegative3037 p) (nonnegative1947 p)
def d3039 (p : Pattern) : Int := if p 204 then d3038 p else d103 p
theorem agree3039 (p q : Pattern) (h : Agree support p q) : d3039 p = d3039 q := by
  simp only [d3039, h 204 (by decide), agree3038 p q h, agree103 p q h]
theorem nonnegative3039 (p : Pattern) : 0 ≤ d3039 p :=
  nonnegative_ite (p 204) (nonnegative3038 p) (nonnegative103 p)
def d3040 (p : Pattern) : Int := if p 182 then d1952 p else d3039 p
theorem agree3040 (p q : Pattern) (h : Agree support p q) : d3040 p = d3040 q := by
  simp only [d3040, h 182 (by decide), agree1952 p q h, agree3039 p q h]
theorem nonnegative3040 (p : Pattern) : 0 ≤ d3040 p :=
  nonnegative_ite (p 182) (nonnegative1952 p) (nonnegative3039 p)
def d3041 (p : Pattern) : Int := if p 163 then d3040 p else d3034 p
theorem agree3041 (p q : Pattern) (h : Agree support p q) : d3041 p = d3041 q := by
  simp only [d3041, h 163 (by decide), agree3040 p q h, agree3034 p q h]
theorem nonnegative3041 (p : Pattern) : 0 ≤ d3041 p :=
  nonnegative_ite (p 163) (nonnegative3040 p) (nonnegative3034 p)
def d3042 (p : Pattern) : Int := if p 182 then d1958 p else d3002 p
theorem agree3042 (p q : Pattern) (h : Agree support p q) : d3042 p = d3042 q := by
  simp only [d3042, h 182 (by decide), agree1958 p q h, agree3002 p q h]
theorem nonnegative3042 (p : Pattern) : 0 ≤ d3042 p :=
  nonnegative_ite (p 182) (nonnegative1958 p) (nonnegative3002 p)
def d3043 (p : Pattern) : Int := if p 182 then d1967 p else d3007 p
theorem agree3043 (p q : Pattern) (h : Agree support p q) : d3043 p = d3043 q := by
  simp only [d3043, h 182 (by decide), agree1967 p q h, agree3007 p q h]
theorem nonnegative3043 (p : Pattern) : 0 ≤ d3043 p :=
  nonnegative_ite (p 182) (nonnegative1967 p) (nonnegative3007 p)
def d3044 (p : Pattern) : Int := if p 163 then d3043 p else d3042 p
theorem agree3044 (p q : Pattern) (h : Agree support p q) : d3044 p = d3044 q := by
  simp only [d3044, h 163 (by decide), agree3043 p q h, agree3042 p q h]
theorem nonnegative3044 (p : Pattern) : 0 ≤ d3044 p :=
  nonnegative_ite (p 163) (nonnegative3043 p) (nonnegative3042 p)
def d3045 (p : Pattern) : Int := if p 162 then d3044 p else d3041 p
theorem agree3045 (p q : Pattern) (h : Agree support p q) : d3045 p = d3045 q := by
  simp only [d3045, h 162 (by decide), agree3044 p q h, agree3041 p q h]
theorem nonnegative3045 (p : Pattern) : 0 ≤ d3045 p :=
  nonnegative_ite (p 162) (nonnegative3044 p) (nonnegative3041 p)
def d3046 (p : Pattern) : Int := if p 162 then d2999 p else d3044 p
theorem agree3046 (p q : Pattern) (h : Agree support p q) : d3046 p = d3046 q := by
  simp only [d3046, h 162 (by decide), agree2999 p q h, agree3044 p q h]
theorem nonnegative3046 (p : Pattern) : 0 ≤ d3046 p :=
  nonnegative_ite (p 162) (nonnegative2999 p) (nonnegative3044 p)
def d3047 (p : Pattern) : Int := if p 161 then d3046 p else d3045 p
theorem agree3047 (p q : Pattern) (h : Agree support p q) : d3047 p = d3047 q := by
  simp only [d3047, h 161 (by decide), agree3046 p q h, agree3045 p q h]
theorem nonnegative3047 (p : Pattern) : 0 ≤ d3047 p :=
  nonnegative_ite (p 161) (nonnegative3046 p) (nonnegative3045 p)
def d3048 (p : Pattern) : Int := if p 182 then d1899 p else d3023 p
theorem agree3048 (p q : Pattern) (h : Agree support p q) : d3048 p = d3048 q := by
  simp only [d3048, h 182 (by decide), agree1899 p q h, agree3023 p q h]
theorem nonnegative3048 (p : Pattern) : 0 ≤ d3048 p :=
  nonnegative_ite (p 182) (nonnegative1899 p) (nonnegative3023 p)
def d3049 (p : Pattern) : Int := if p 204 then d1905 p else d120 p
theorem agree3049 (p q : Pattern) (h : Agree support p q) : d3049 p = d3049 q := by
  simp only [d3049, h 204 (by decide), agree1905 p q h, agree120 p q h]
theorem nonnegative3049 (p : Pattern) : 0 ≤ d3049 p :=
  nonnegative_ite (p 204) (nonnegative1905 p) (nonnegative120 p)
def d3050 (p : Pattern) : Int := if p 182 then d1906 p else d3049 p
theorem agree3050 (p q : Pattern) (h : Agree support p q) : d3050 p = d3050 q := by
  simp only [d3050, h 182 (by decide), agree1906 p q h, agree3049 p q h]
theorem nonnegative3050 (p : Pattern) : 0 ≤ d3050 p :=
  nonnegative_ite (p 182) (nonnegative1906 p) (nonnegative3049 p)
def d3051 (p : Pattern) : Int := if p 163 then d3050 p else d3048 p
theorem agree3051 (p q : Pattern) (h : Agree support p q) : d3051 p = d3051 q := by
  simp only [d3051, h 163 (by decide), agree3050 p q h, agree3048 p q h]
theorem nonnegative3051 (p : Pattern) : 0 ≤ d3051 p :=
  nonnegative_ite (p 163) (nonnegative3050 p) (nonnegative3048 p)
def d3052 (p : Pattern) : Int := if p 162 then d12 p else d3051 p
theorem agree3052 (p q : Pattern) (h : Agree support p q) : d3052 p = d3052 q := by
  simp only [d3052, h 162 (by decide), agree12 p q h, agree3051 p q h]
theorem nonnegative3052 (p : Pattern) : 0 ≤ d3052 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3051 p)
def d3053 (p : Pattern) : Int := if p 161 then d12 p else d3052 p
theorem agree3053 (p q : Pattern) (h : Agree support p q) : d3053 p = d3053 q := by
  simp only [d3053, h 161 (by decide), agree12 p q h, agree3052 p q h]
theorem nonnegative3053 (p : Pattern) : 0 ≤ d3053 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3052 p)
def d3054 (p : Pattern) : Int := if p 160 then d3053 p else d3047 p
theorem agree3054 (p q : Pattern) (h : Agree support p q) : d3054 p = d3054 q := by
  simp only [d3054, h 160 (by decide), agree3053 p q h, agree3047 p q h]
theorem nonnegative3054 (p : Pattern) : 0 ≤ d3054 p :=
  nonnegative_ite (p 160) (nonnegative3053 p) (nonnegative3047 p)
def d3055 (p : Pattern) : Int := if p 163 then d3048 p else d3040 p
theorem agree3055 (p q : Pattern) (h : Agree support p q) : d3055 p = d3055 q := by
  simp only [d3055, h 163 (by decide), agree3048 p q h, agree3040 p q h]
theorem nonnegative3055 (p : Pattern) : 0 ≤ d3055 p :=
  nonnegative_ite (p 163) (nonnegative3048 p) (nonnegative3040 p)
def d3056 (p : Pattern) : Int := if p 163 then d2928 p else d3043 p
theorem agree3056 (p q : Pattern) (h : Agree support p q) : d3056 p = d3056 q := by
  simp only [d3056, h 163 (by decide), agree2928 p q h, agree3043 p q h]
theorem nonnegative3056 (p : Pattern) : 0 ≤ d3056 p :=
  nonnegative_ite (p 163) (nonnegative2928 p) (nonnegative3043 p)
def d3057 (p : Pattern) : Int := if p 162 then d3056 p else d3055 p
theorem agree3057 (p q : Pattern) (h : Agree support p q) : d3057 p = d3057 q := by
  simp only [d3057, h 162 (by decide), agree3056 p q h, agree3055 p q h]
theorem nonnegative3057 (p : Pattern) : 0 ≤ d3057 p :=
  nonnegative_ite (p 162) (nonnegative3056 p) (nonnegative3055 p)
def d3058 (p : Pattern) : Int := if p 163 then d2931 p else d3043 p
theorem agree3058 (p q : Pattern) (h : Agree support p q) : d3058 p = d3058 q := by
  simp only [d3058, h 163 (by decide), agree2931 p q h, agree3043 p q h]
theorem nonnegative3058 (p : Pattern) : 0 ≤ d3058 p :=
  nonnegative_ite (p 163) (nonnegative2931 p) (nonnegative3043 p)
def d3059 (p : Pattern) : Int := if p 162 then d12 p else d3058 p
theorem agree3059 (p q : Pattern) (h : Agree support p q) : d3059 p = d3059 q := by
  simp only [d3059, h 162 (by decide), agree12 p q h, agree3058 p q h]
theorem nonnegative3059 (p : Pattern) : 0 ≤ d3059 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3058 p)
def d3060 (p : Pattern) : Int := if p 161 then d3059 p else d3057 p
theorem agree3060 (p q : Pattern) (h : Agree support p q) : d3060 p = d3060 q := by
  simp only [d3060, h 161 (by decide), agree3059 p q h, agree3057 p q h]
theorem nonnegative3060 (p : Pattern) : 0 ≤ d3060 p :=
  nonnegative_ite (p 161) (nonnegative3059 p) (nonnegative3057 p)
def d3061 (p : Pattern) : Int := if p 163 then d12 p else d3050 p
theorem agree3061 (p q : Pattern) (h : Agree support p q) : d3061 p = d3061 q := by
  simp only [d3061, h 163 (by decide), agree12 p q h, agree3050 p q h]
theorem nonnegative3061 (p : Pattern) : 0 ≤ d3061 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3050 p)
def d3062 (p : Pattern) : Int := if p 162 then d12 p else d3061 p
theorem agree3062 (p q : Pattern) (h : Agree support p q) : d3062 p = d3062 q := by
  simp only [d3062, h 162 (by decide), agree12 p q h, agree3061 p q h]
theorem nonnegative3062 (p : Pattern) : 0 ≤ d3062 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3061 p)
def d3063 (p : Pattern) : Int := if p 161 then d12 p else d3062 p
theorem agree3063 (p q : Pattern) (h : Agree support p q) : d3063 p = d3063 q := by
  simp only [d3063, h 161 (by decide), agree12 p q h, agree3062 p q h]
theorem nonnegative3063 (p : Pattern) : 0 ≤ d3063 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3062 p)
def d3064 (p : Pattern) : Int := if p 160 then d3063 p else d3060 p
theorem agree3064 (p q : Pattern) (h : Agree support p q) : d3064 p = d3064 q := by
  simp only [d3064, h 160 (by decide), agree3063 p q h, agree3060 p q h]
theorem nonnegative3064 (p : Pattern) : 0 ≤ d3064 p :=
  nonnegative_ite (p 160) (nonnegative3063 p) (nonnegative3060 p)
def d3065 (p : Pattern) : Int := if p 141 then d3064 p else d3054 p
theorem agree3065 (p q : Pattern) (h : Agree support p q) : d3065 p = d3065 q := by
  simp only [d3065, h 141 (by decide), agree3064 p q h, agree3054 p q h]
theorem nonnegative3065 (p : Pattern) : 0 ≤ d3065 p :=
  nonnegative_ite (p 141) (nonnegative3064 p) (nonnegative3054 p)
def d3066 (p : Pattern) : Int := if p 138 then d3065 p else d3032 p
theorem agree3066 (p q : Pattern) (h : Agree support p q) : d3066 p = d3066 q := by
  simp only [d3066, h 138 (by decide), agree3065 p q h, agree3032 p q h]
theorem nonnegative3066 (p : Pattern) : 0 ≤ d3066 p :=
  nonnegative_ite (p 138) (nonnegative3065 p) (nonnegative3032 p)
def d3067 (p : Pattern) : Int := if p 162 then d12 p else d2999 p
theorem agree3067 (p q : Pattern) (h : Agree support p q) : d3067 p = d3067 q := by
  simp only [d3067, h 162 (by decide), agree12 p q h, agree2999 p q h]
theorem nonnegative3067 (p : Pattern) : 0 ≤ d3067 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2999 p)
def d3068 (p : Pattern) : Int := if p 161 then d12 p else d3067 p
theorem agree3068 (p q : Pattern) (h : Agree support p q) : d3068 p = d3068 q := by
  simp only [d3068, h 161 (by decide), agree12 p q h, agree3067 p q h]
theorem nonnegative3068 (p : Pattern) : 0 ≤ d3068 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3067 p)
def d3069 (p : Pattern) : Int := if p 160 then d12 p else d3068 p
theorem agree3069 (p q : Pattern) (h : Agree support p q) : d3069 p = d3069 q := by
  simp only [d3069, h 160 (by decide), agree12 p q h, agree3068 p q h]
theorem nonnegative3069 (p : Pattern) : 0 ≤ d3069 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative3068 p)
def d3070 (p : Pattern) : Int := if p 141 then d12 p else d3069 p
theorem agree3070 (p q : Pattern) (h : Agree support p q) : d3070 p = d3070 q := by
  simp only [d3070, h 141 (by decide), agree12 p q h, agree3069 p q h]
theorem nonnegative3070 (p : Pattern) : 0 ≤ d3070 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative3069 p)
def d3071 (p : Pattern) : Int := if p 138 then d3070 p else d3065 p
theorem agree3071 (p q : Pattern) (h : Agree support p q) : d3071 p = d3071 q := by
  simp only [d3071, h 138 (by decide), agree3070 p q h, agree3065 p q h]
theorem nonnegative3071 (p : Pattern) : 0 ≤ d3071 p :=
  nonnegative_ite (p 138) (nonnegative3070 p) (nonnegative3065 p)
def d3072 (p : Pattern) : Int := if p 116 then d3071 p else d3066 p
theorem agree3072 (p q : Pattern) (h : Agree support p q) : d3072 p = d3072 q := by
  simp only [d3072, h 116 (by decide), agree3071 p q h, agree3066 p q h]
theorem nonnegative3072 (p : Pattern) : 0 ≤ d3072 p :=
  nonnegative_ite (p 116) (nonnegative3071 p) (nonnegative3066 p)
def d3073 (p : Pattern) : Int := if p 138 then d12 p else d3065 p
theorem agree3073 (p q : Pattern) (h : Agree support p q) : d3073 p = d3073 q := by
  simp only [d3073, h 138 (by decide), agree12 p q h, agree3065 p q h]
theorem nonnegative3073 (p : Pattern) : 0 ≤ d3073 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3065 p)
def d3074 (p : Pattern) : Int := if p 116 then d3073 p else d3066 p
theorem agree3074 (p q : Pattern) (h : Agree support p q) : d3074 p = d3074 q := by
  simp only [d3074, h 116 (by decide), agree3073 p q h, agree3066 p q h]
theorem nonnegative3074 (p : Pattern) : 0 ≤ d3074 p :=
  nonnegative_ite (p 116) (nonnegative3073 p) (nonnegative3066 p)
def d3075 (p : Pattern) : Int := if p 115 then d3074 p else d3072 p
theorem agree3075 (p q : Pattern) (h : Agree support p q) : d3075 p = d3075 q := by
  simp only [d3075, h 115 (by decide), agree3074 p q h, agree3072 p q h]
theorem nonnegative3075 (p : Pattern) : 0 ≤ d3075 p :=
  nonnegative_ite (p 115) (nonnegative3074 p) (nonnegative3072 p)
def d3076 (p : Pattern) : Int := if p 71 then d3075 p else d2992 p
theorem agree3076 (p q : Pattern) (h : Agree support p q) : d3076 p = d3076 q := by
  simp only [d3076, h 71 (by decide), agree3075 p q h, agree2992 p q h]
theorem nonnegative3076 (p : Pattern) : 0 ≤ d3076 p :=
  nonnegative_ite (p 71) (nonnegative3075 p) (nonnegative2992 p)
def d3077 (p : Pattern) : Int := if p 49 then d3076 p else d2992 p
theorem agree3077 (p q : Pattern) (h : Agree support p q) : d3077 p = d3077 q := by
  simp only [d3077, h 49 (by decide), agree3076 p q h, agree2992 p q h]
theorem nonnegative3077 (p : Pattern) : 0 ≤ d3077 p :=
  nonnegative_ite (p 49) (nonnegative3076 p) (nonnegative2992 p)
def d3078 (p : Pattern) : Int := if p 225 then d1792 p else d1795 p
theorem agree3078 (p q : Pattern) (h : Agree support p q) : d3078 p = d3078 q := by
  simp only [d3078, h 225 (by decide), agree1792 p q h, agree1795 p q h]
theorem nonnegative3078 (p : Pattern) : 0 ≤ d3078 p :=
  nonnegative_ite (p 225) (nonnegative1792 p) (nonnegative1795 p)
def d3079 (p : Pattern) : Int := if p 224 then d3078 p else d1793 p
theorem agree3079 (p q : Pattern) (h : Agree support p q) : d3079 p = d3079 q := by
  simp only [d3079, h 224 (by decide), agree3078 p q h, agree1793 p q h]
theorem nonnegative3079 (p : Pattern) : 0 ≤ d3079 p :=
  nonnegative_ite (p 224) (nonnegative3078 p) (nonnegative1793 p)
def d3080 (p : Pattern) : Int := if p 204 then d3079 p else d18 p
theorem agree3080 (p q : Pattern) (h : Agree support p q) : d3080 p = d3080 q := by
  simp only [d3080, h 204 (by decide), agree3079 p q h, agree18 p q h]
theorem nonnegative3080 (p : Pattern) : 0 ≤ d3080 p :=
  nonnegative_ite (p 204) (nonnegative3079 p) (nonnegative18 p)
def d3081 (p : Pattern) : Int := if p 182 then d2013 p else d3080 p
theorem agree3081 (p q : Pattern) (h : Agree support p q) : d3081 p = d3081 q := by
  simp only [d3081, h 182 (by decide), agree2013 p q h, agree3080 p q h]
theorem nonnegative3081 (p : Pattern) : 0 ≤ d3081 p :=
  nonnegative_ite (p 182) (nonnegative2013 p) (nonnegative3080 p)
def d3082 (p : Pattern) : Int := if p 163 then d3081 p else d2949 p
theorem agree3082 (p q : Pattern) (h : Agree support p q) : d3082 p = d3082 q := by
  simp only [d3082, h 163 (by decide), agree3081 p q h, agree2949 p q h]
theorem nonnegative3082 (p : Pattern) : 0 ≤ d3082 p :=
  nonnegative_ite (p 163) (nonnegative3081 p) (nonnegative2949 p)
def d3083 (p : Pattern) : Int := if p 162 then d3082 p else d2949 p
theorem agree3083 (p q : Pattern) (h : Agree support p q) : d3083 p = d3083 q := by
  simp only [d3083, h 162 (by decide), agree3082 p q h, agree2949 p q h]
theorem nonnegative3083 (p : Pattern) : 0 ≤ d3083 p :=
  nonnegative_ite (p 162) (nonnegative3082 p) (nonnegative2949 p)
def d3084 (p : Pattern) : Int := if p 162 then d2958 p else d3082 p
theorem agree3084 (p q : Pattern) (h : Agree support p q) : d3084 p = d3084 q := by
  simp only [d3084, h 162 (by decide), agree2958 p q h, agree3082 p q h]
theorem nonnegative3084 (p : Pattern) : 0 ≤ d3084 p :=
  nonnegative_ite (p 162) (nonnegative2958 p) (nonnegative3082 p)
def d3085 (p : Pattern) : Int := if p 161 then d3084 p else d3083 p
theorem agree3085 (p q : Pattern) (h : Agree support p q) : d3085 p = d3085 q := by
  simp only [d3085, h 161 (by decide), agree3084 p q h, agree3083 p q h]
theorem nonnegative3085 (p : Pattern) : 0 ≤ d3085 p :=
  nonnegative_ite (p 161) (nonnegative3084 p) (nonnegative3083 p)
def d3086 (p : Pattern) : Int := if p 182 then d1725 p else d2935 p
theorem agree3086 (p q : Pattern) (h : Agree support p q) : d3086 p = d3086 q := by
  simp only [d3086, h 182 (by decide), agree1725 p q h, agree2935 p q h]
theorem nonnegative3086 (p : Pattern) : 0 ≤ d3086 p :=
  nonnegative_ite (p 182) (nonnegative1725 p) (nonnegative2935 p)
def d3087 (p : Pattern) : Int := if p 163 then d3086 p else d2961 p
theorem agree3087 (p q : Pattern) (h : Agree support p q) : d3087 p = d3087 q := by
  simp only [d3087, h 163 (by decide), agree3086 p q h, agree2961 p q h]
theorem nonnegative3087 (p : Pattern) : 0 ≤ d3087 p :=
  nonnegative_ite (p 163) (nonnegative3086 p) (nonnegative2961 p)
def d3088 (p : Pattern) : Int := if p 182 then d1730 p else d2935 p
theorem agree3088 (p q : Pattern) (h : Agree support p q) : d3088 p = d3088 q := by
  simp only [d3088, h 182 (by decide), agree1730 p q h, agree2935 p q h]
theorem nonnegative3088 (p : Pattern) : 0 ≤ d3088 p :=
  nonnegative_ite (p 182) (nonnegative1730 p) (nonnegative2935 p)
def d3089 (p : Pattern) : Int := if p 182 then d12 p else d2962 p
theorem agree3089 (p q : Pattern) (h : Agree support p q) : d3089 p = d3089 q := by
  simp only [d3089, h 182 (by decide), agree12 p q h, agree2962 p q h]
theorem nonnegative3089 (p : Pattern) : 0 ≤ d3089 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2962 p)
def d3090 (p : Pattern) : Int := if p 163 then d3089 p else d3088 p
theorem agree3090 (p q : Pattern) (h : Agree support p q) : d3090 p = d3090 q := by
  simp only [d3090, h 163 (by decide), agree3089 p q h, agree3088 p q h]
theorem nonnegative3090 (p : Pattern) : 0 ≤ d3090 p :=
  nonnegative_ite (p 163) (nonnegative3089 p) (nonnegative3088 p)
def d3091 (p : Pattern) : Int := if p 162 then d3090 p else d3087 p
theorem agree3091 (p q : Pattern) (h : Agree support p q) : d3091 p = d3091 q := by
  simp only [d3091, h 162 (by decide), agree3090 p q h, agree3087 p q h]
theorem nonnegative3091 (p : Pattern) : 0 ≤ d3091 p :=
  nonnegative_ite (p 162) (nonnegative3090 p) (nonnegative3087 p)
def d3092 (p : Pattern) : Int := if p 163 then d3089 p else d2936 p
theorem agree3092 (p q : Pattern) (h : Agree support p q) : d3092 p = d3092 q := by
  simp only [d3092, h 163 (by decide), agree3089 p q h, agree2936 p q h]
theorem nonnegative3092 (p : Pattern) : 0 ≤ d3092 p :=
  nonnegative_ite (p 163) (nonnegative3089 p) (nonnegative2936 p)
def d3093 (p : Pattern) : Int := if p 162 then d2943 p else d3092 p
theorem agree3093 (p q : Pattern) (h : Agree support p q) : d3093 p = d3093 q := by
  simp only [d3093, h 162 (by decide), agree2943 p q h, agree3092 p q h]
theorem nonnegative3093 (p : Pattern) : 0 ≤ d3093 p :=
  nonnegative_ite (p 162) (nonnegative2943 p) (nonnegative3092 p)
def d3094 (p : Pattern) : Int := if p 161 then d3093 p else d3091 p
theorem agree3094 (p q : Pattern) (h : Agree support p q) : d3094 p = d3094 q := by
  simp only [d3094, h 161 (by decide), agree3093 p q h, agree3091 p q h]
theorem nonnegative3094 (p : Pattern) : 0 ≤ d3094 p :=
  nonnegative_ite (p 161) (nonnegative3093 p) (nonnegative3091 p)
def d3095 (p : Pattern) : Int := if p 160 then d3094 p else d3085 p
theorem agree3095 (p q : Pattern) (h : Agree support p q) : d3095 p = d3095 q := by
  simp only [d3095, h 160 (by decide), agree3094 p q h, agree3085 p q h]
theorem nonnegative3095 (p : Pattern) : 0 ≤ d3095 p :=
  nonnegative_ite (p 160) (nonnegative3094 p) (nonnegative3085 p)
def d3096 (p : Pattern) : Int := if p 225 then d1711 p else d1714 p
theorem agree3096 (p q : Pattern) (h : Agree support p q) : d3096 p = d3096 q := by
  simp only [d3096, h 225 (by decide), agree1711 p q h, agree1714 p q h]
theorem nonnegative3096 (p : Pattern) : 0 ≤ d3096 p :=
  nonnegative_ite (p 225) (nonnegative1711 p) (nonnegative1714 p)
def d3097 (p : Pattern) : Int := if p 224 then d3096 p else d1712 p
theorem agree3097 (p q : Pattern) (h : Agree support p q) : d3097 p = d3097 q := by
  simp only [d3097, h 224 (by decide), agree3096 p q h, agree1712 p q h]
theorem nonnegative3097 (p : Pattern) : 0 ≤ d3097 p :=
  nonnegative_ite (p 224) (nonnegative3096 p) (nonnegative1712 p)
def d3098 (p : Pattern) : Int := if p 204 then d3097 p else d31 p
theorem agree3098 (p q : Pattern) (h : Agree support p q) : d3098 p = d3098 q := by
  simp only [d3098, h 204 (by decide), agree3097 p q h, agree31 p q h]
theorem nonnegative3098 (p : Pattern) : 0 ≤ d3098 p :=
  nonnegative_ite (p 204) (nonnegative3097 p) (nonnegative31 p)
def d3099 (p : Pattern) : Int := if p 182 then d2031 p else d3098 p
theorem agree3099 (p q : Pattern) (h : Agree support p q) : d3099 p = d3099 q := by
  simp only [d3099, h 182 (by decide), agree2031 p q h, agree3098 p q h]
theorem nonnegative3099 (p : Pattern) : 0 ≤ d3099 p :=
  nonnegative_ite (p 182) (nonnegative2031 p) (nonnegative3098 p)
def d3100 (p : Pattern) : Int := if p 163 then d3099 p else d2949 p
theorem agree3100 (p q : Pattern) (h : Agree support p q) : d3100 p = d3100 q := by
  simp only [d3100, h 163 (by decide), agree3099 p q h, agree2949 p q h]
theorem nonnegative3100 (p : Pattern) : 0 ≤ d3100 p :=
  nonnegative_ite (p 163) (nonnegative3099 p) (nonnegative2949 p)
def d3101 (p : Pattern) : Int := if p 163 then d2957 p else d3081 p
theorem agree3101 (p q : Pattern) (h : Agree support p q) : d3101 p = d3101 q := by
  simp only [d3101, h 163 (by decide), agree2957 p q h, agree3081 p q h]
theorem nonnegative3101 (p : Pattern) : 0 ≤ d3101 p :=
  nonnegative_ite (p 163) (nonnegative2957 p) (nonnegative3081 p)
def d3102 (p : Pattern) : Int := if p 162 then d3101 p else d3100 p
theorem agree3102 (p q : Pattern) (h : Agree support p q) : d3102 p = d3102 q := by
  simp only [d3102, h 162 (by decide), agree3101 p q h, agree3100 p q h]
theorem nonnegative3102 (p : Pattern) : 0 ≤ d3102 p :=
  nonnegative_ite (p 162) (nonnegative3101 p) (nonnegative3100 p)
def d3103 (p : Pattern) : Int := if p 163 then d2928 p else d3081 p
theorem agree3103 (p q : Pattern) (h : Agree support p q) : d3103 p = d3103 q := by
  simp only [d3103, h 163 (by decide), agree2928 p q h, agree3081 p q h]
theorem nonnegative3103 (p : Pattern) : 0 ≤ d3103 p :=
  nonnegative_ite (p 163) (nonnegative2928 p) (nonnegative3081 p)
def d3104 (p : Pattern) : Int := if p 162 then d2932 p else d3103 p
theorem agree3104 (p q : Pattern) (h : Agree support p q) : d3104 p = d3104 q := by
  simp only [d3104, h 162 (by decide), agree2932 p q h, agree3103 p q h]
theorem nonnegative3104 (p : Pattern) : 0 ≤ d3104 p :=
  nonnegative_ite (p 162) (nonnegative2932 p) (nonnegative3103 p)
def d3105 (p : Pattern) : Int := if p 161 then d3104 p else d3102 p
theorem agree3105 (p q : Pattern) (h : Agree support p q) : d3105 p = d3105 q := by
  simp only [d3105, h 161 (by decide), agree3104 p q h, agree3102 p q h]
theorem nonnegative3105 (p : Pattern) : 0 ≤ d3105 p :=
  nonnegative_ite (p 161) (nonnegative3104 p) (nonnegative3102 p)
def d3106 (p : Pattern) : Int := if p 163 then d2912 p else d3086 p
theorem agree3106 (p q : Pattern) (h : Agree support p q) : d3106 p = d3106 q := by
  simp only [d3106, h 163 (by decide), agree2912 p q h, agree3086 p q h]
theorem nonnegative3106 (p : Pattern) : 0 ≤ d3106 p :=
  nonnegative_ite (p 163) (nonnegative2912 p) (nonnegative3086 p)
def d3107 (p : Pattern) : Int := if p 163 then d2942 p else d3089 p
theorem agree3107 (p q : Pattern) (h : Agree support p q) : d3107 p = d3107 q := by
  simp only [d3107, h 163 (by decide), agree2942 p q h, agree3089 p q h]
theorem nonnegative3107 (p : Pattern) : 0 ≤ d3107 p :=
  nonnegative_ite (p 163) (nonnegative2942 p) (nonnegative3089 p)
def d3108 (p : Pattern) : Int := if p 162 then d3107 p else d3106 p
theorem agree3108 (p q : Pattern) (h : Agree support p q) : d3108 p = d3108 q := by
  simp only [d3108, h 162 (by decide), agree3107 p q h, agree3106 p q h]
theorem nonnegative3108 (p : Pattern) : 0 ≤ d3108 p :=
  nonnegative_ite (p 162) (nonnegative3107 p) (nonnegative3106 p)
def d3109 (p : Pattern) : Int := if p 163 then d12 p else d3089 p
theorem agree3109 (p q : Pattern) (h : Agree support p q) : d3109 p = d3109 q := by
  simp only [d3109, h 163 (by decide), agree12 p q h, agree3089 p q h]
theorem nonnegative3109 (p : Pattern) : 0 ≤ d3109 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3089 p)
def d3110 (p : Pattern) : Int := if p 162 then d12 p else d3109 p
theorem agree3110 (p q : Pattern) (h : Agree support p q) : d3110 p = d3110 q := by
  simp only [d3110, h 162 (by decide), agree12 p q h, agree3109 p q h]
theorem nonnegative3110 (p : Pattern) : 0 ≤ d3110 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3109 p)
def d3111 (p : Pattern) : Int := if p 161 then d3110 p else d3108 p
theorem agree3111 (p q : Pattern) (h : Agree support p q) : d3111 p = d3111 q := by
  simp only [d3111, h 161 (by decide), agree3110 p q h, agree3108 p q h]
theorem nonnegative3111 (p : Pattern) : 0 ≤ d3111 p :=
  nonnegative_ite (p 161) (nonnegative3110 p) (nonnegative3108 p)
def d3112 (p : Pattern) : Int := if p 160 then d3111 p else d3105 p
theorem agree3112 (p q : Pattern) (h : Agree support p q) : d3112 p = d3112 q := by
  simp only [d3112, h 160 (by decide), agree3111 p q h, agree3105 p q h]
theorem nonnegative3112 (p : Pattern) : 0 ≤ d3112 p :=
  nonnegative_ite (p 160) (nonnegative3111 p) (nonnegative3105 p)
def d3113 (p : Pattern) : Int := if p 141 then d3112 p else d3095 p
theorem agree3113 (p q : Pattern) (h : Agree support p q) : d3113 p = d3113 q := by
  simp only [d3113, h 141 (by decide), agree3112 p q h, agree3095 p q h]
theorem nonnegative3113 (p : Pattern) : 0 ≤ d3113 p :=
  nonnegative_ite (p 141) (nonnegative3112 p) (nonnegative3095 p)
def d3114 (p : Pattern) : Int := if p 204 then d1781 p else d14 p
theorem agree3114 (p q : Pattern) (h : Agree support p q) : d3114 p = d3114 q := by
  simp only [d3114, h 204 (by decide), agree1781 p q h, agree14 p q h]
theorem nonnegative3114 (p : Pattern) : 0 ≤ d3114 p :=
  nonnegative_ite (p 204) (nonnegative1781 p) (nonnegative14 p)
def d3115 (p : Pattern) : Int := if p 182 then d2049 p else d3114 p
theorem agree3115 (p q : Pattern) (h : Agree support p q) : d3115 p = d3115 q := by
  simp only [d3115, h 182 (by decide), agree2049 p q h, agree3114 p q h]
theorem nonnegative3115 (p : Pattern) : 0 ≤ d3115 p :=
  nonnegative_ite (p 182) (nonnegative2049 p) (nonnegative3114 p)
def d3116 (p : Pattern) : Int := if p 182 then d2055 p else d2906 p
theorem agree3116 (p q : Pattern) (h : Agree support p q) : d3116 p = d3116 q := by
  simp only [d3116, h 182 (by decide), agree2055 p q h, agree2906 p q h]
theorem nonnegative3116 (p : Pattern) : 0 ≤ d3116 p :=
  nonnegative_ite (p 182) (nonnegative2055 p) (nonnegative2906 p)
def d3117 (p : Pattern) : Int := if p 163 then d3116 p else d3115 p
theorem agree3117 (p q : Pattern) (h : Agree support p q) : d3117 p = d3117 q := by
  simp only [d3117, h 163 (by decide), agree3116 p q h, agree3115 p q h]
theorem nonnegative3117 (p : Pattern) : 0 ≤ d3117 p :=
  nonnegative_ite (p 163) (nonnegative3116 p) (nonnegative3115 p)
def d3118 (p : Pattern) : Int := if p 162 then d2964 p else d3117 p
theorem agree3118 (p q : Pattern) (h : Agree support p q) : d3118 p = d3118 q := by
  simp only [d3118, h 162 (by decide), agree2964 p q h, agree3117 p q h]
theorem nonnegative3118 (p : Pattern) : 0 ≤ d3118 p :=
  nonnegative_ite (p 162) (nonnegative2964 p) (nonnegative3117 p)
def d3119 (p : Pattern) : Int := if p 161 then d2965 p else d3118 p
theorem agree3119 (p q : Pattern) (h : Agree support p q) : d3119 p = d3119 q := by
  simp only [d3119, h 161 (by decide), agree2965 p q h, agree3118 p q h]
theorem nonnegative3119 (p : Pattern) : 0 ≤ d3119 p :=
  nonnegative_ite (p 161) (nonnegative2965 p) (nonnegative3118 p)
end NetHack.Sokoban22Refined85
