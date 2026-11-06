/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes25
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d3120 (p : Pattern) : Int := if p 204 then d2061 p else d191 p
theorem agree3120 (p q : Pattern) (h : Agree support p q) : d3120 p = d3120 q := by
  simp only [d3120, h 204 (by decide), agree2061 p q h, agree191 p q h]
theorem nonnegative3120 (p : Pattern) : 0 ≤ d3120 p :=
  nonnegative_ite (p 204) (nonnegative2061 p) (nonnegative191 p)
def d3121 (p : Pattern) : Int := if p 182 then d2062 p else d3120 p
theorem agree3121 (p q : Pattern) (h : Agree support p q) : d3121 p = d3121 q := by
  simp only [d3121, h 182 (by decide), agree2062 p q h, agree3120 p q h]
theorem nonnegative3121 (p : Pattern) : 0 ≤ d3121 p :=
  nonnegative_ite (p 182) (nonnegative2062 p) (nonnegative3120 p)
def d3122 (p : Pattern) : Int := if p 163 then d3121 p else d2954 p
theorem agree3122 (p q : Pattern) (h : Agree support p q) : d3122 p = d3122 q := by
  simp only [d3122, h 163 (by decide), agree3121 p q h, agree2954 p q h]
theorem nonnegative3122 (p : Pattern) : 0 ≤ d3122 p :=
  nonnegative_ite (p 163) (nonnegative3121 p) (nonnegative2954 p)
def d3123 (p : Pattern) : Int := if p 162 then d12 p else d3122 p
theorem agree3123 (p q : Pattern) (h : Agree support p q) : d3123 p = d3123 q := by
  simp only [d3123, h 162 (by decide), agree12 p q h, agree3122 p q h]
theorem nonnegative3123 (p : Pattern) : 0 ≤ d3123 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3122 p)
def d3124 (p : Pattern) : Int := if p 161 then d12 p else d3123 p
theorem agree3124 (p q : Pattern) (h : Agree support p q) : d3124 p = d3124 q := by
  simp only [d3124, h 161 (by decide), agree12 p q h, agree3123 p q h]
theorem nonnegative3124 (p : Pattern) : 0 ≤ d3124 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3123 p)
def d3125 (p : Pattern) : Int := if p 160 then d3124 p else d3119 p
theorem agree3125 (p q : Pattern) (h : Agree support p q) : d3125 p = d3125 q := by
  simp only [d3125, h 160 (by decide), agree3124 p q h, agree3119 p q h]
theorem nonnegative3125 (p : Pattern) : 0 ≤ d3125 p :=
  nonnegative_ite (p 160) (nonnegative3124 p) (nonnegative3119 p)
def d3126 (p : Pattern) : Int := if p 182 then d2072 p else d2935 p
theorem agree3126 (p q : Pattern) (h : Agree support p q) : d3126 p = d3126 q := by
  simp only [d3126, h 182 (by decide), agree2072 p q h, agree2935 p q h]
theorem nonnegative3126 (p : Pattern) : 0 ≤ d3126 p :=
  nonnegative_ite (p 182) (nonnegative2072 p) (nonnegative2935 p)
def d3127 (p : Pattern) : Int := if p 163 then d2961 p else d3126 p
theorem agree3127 (p q : Pattern) (h : Agree support p q) : d3127 p = d3127 q := by
  simp only [d3127, h 163 (by decide), agree2961 p q h, agree3126 p q h]
theorem nonnegative3127 (p : Pattern) : 0 ≤ d3127 p :=
  nonnegative_ite (p 163) (nonnegative2961 p) (nonnegative3126 p)
def d3128 (p : Pattern) : Int := if p 163 then d2931 p else d2954 p
theorem agree3128 (p q : Pattern) (h : Agree support p q) : d3128 p = d3128 q := by
  simp only [d3128, h 163 (by decide), agree2931 p q h, agree2954 p q h]
theorem nonnegative3128 (p : Pattern) : 0 ≤ d3128 p :=
  nonnegative_ite (p 163) (nonnegative2931 p) (nonnegative2954 p)
def d3129 (p : Pattern) : Int := if p 162 then d3128 p else d3127 p
theorem agree3129 (p q : Pattern) (h : Agree support p q) : d3129 p = d3129 q := by
  simp only [d3129, h 162 (by decide), agree3128 p q h, agree3127 p q h]
theorem nonnegative3129 (p : Pattern) : 0 ≤ d3129 p :=
  nonnegative_ite (p 162) (nonnegative3128 p) (nonnegative3127 p)
def d3130 (p : Pattern) : Int := if p 161 then d2975 p else d3129 p
theorem agree3130 (p q : Pattern) (h : Agree support p q) : d3130 p = d3130 q := by
  simp only [d3130, h 161 (by decide), agree2975 p q h, agree3129 p q h]
theorem nonnegative3130 (p : Pattern) : 0 ≤ d3130 p :=
  nonnegative_ite (p 161) (nonnegative2975 p) (nonnegative3129 p)
def d3131 (p : Pattern) : Int := if p 163 then d12 p else d3121 p
theorem agree3131 (p q : Pattern) (h : Agree support p q) : d3131 p = d3131 q := by
  simp only [d3131, h 163 (by decide), agree12 p q h, agree3121 p q h]
theorem nonnegative3131 (p : Pattern) : 0 ≤ d3131 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3121 p)
def d3132 (p : Pattern) : Int := if p 162 then d12 p else d3131 p
theorem agree3132 (p q : Pattern) (h : Agree support p q) : d3132 p = d3132 q := by
  simp only [d3132, h 162 (by decide), agree12 p q h, agree3131 p q h]
theorem nonnegative3132 (p : Pattern) : 0 ≤ d3132 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3131 p)
def d3133 (p : Pattern) : Int := if p 161 then d12 p else d3132 p
theorem agree3133 (p q : Pattern) (h : Agree support p q) : d3133 p = d3133 q := by
  simp only [d3133, h 161 (by decide), agree12 p q h, agree3132 p q h]
theorem nonnegative3133 (p : Pattern) : 0 ≤ d3133 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3132 p)
def d3134 (p : Pattern) : Int := if p 160 then d3133 p else d3130 p
theorem agree3134 (p q : Pattern) (h : Agree support p q) : d3134 p = d3134 q := by
  simp only [d3134, h 160 (by decide), agree3133 p q h, agree3130 p q h]
theorem nonnegative3134 (p : Pattern) : 0 ≤ d3134 p :=
  nonnegative_ite (p 160) (nonnegative3133 p) (nonnegative3130 p)
def d3135 (p : Pattern) : Int := if p 141 then d3134 p else d3125 p
theorem agree3135 (p q : Pattern) (h : Agree support p q) : d3135 p = d3135 q := by
  simp only [d3135, h 141 (by decide), agree3134 p q h, agree3125 p q h]
theorem nonnegative3135 (p : Pattern) : 0 ≤ d3135 p :=
  nonnegative_ite (p 141) (nonnegative3134 p) (nonnegative3125 p)
def d3136 (p : Pattern) : Int := if p 138 then d3135 p else d3113 p
theorem agree3136 (p q : Pattern) (h : Agree support p q) : d3136 p = d3136 q := by
  simp only [d3136, h 138 (by decide), agree3135 p q h, agree3113 p q h]
theorem nonnegative3136 (p : Pattern) : 0 ≤ d3136 p :=
  nonnegative_ite (p 138) (nonnegative3135 p) (nonnegative3113 p)
def d3137 (p : Pattern) : Int := if p 138 then d12 p else d3135 p
theorem agree3137 (p q : Pattern) (h : Agree support p q) : d3137 p = d3137 q := by
  simp only [d3137, h 138 (by decide), agree12 p q h, agree3135 p q h]
theorem nonnegative3137 (p : Pattern) : 0 ≤ d3137 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3135 p)
def d3138 (p : Pattern) : Int := if p 116 then d3137 p else d3136 p
theorem agree3138 (p q : Pattern) (h : Agree support p q) : d3138 p = d3138 q := by
  simp only [d3138, h 116 (by decide), agree3137 p q h, agree3136 p q h]
theorem nonnegative3138 (p : Pattern) : 0 ≤ d3138 p :=
  nonnegative_ite (p 116) (nonnegative3137 p) (nonnegative3136 p)
def d3139 (p : Pattern) : Int := if p 115 then d3138 p else d2989 p
theorem agree3139 (p q : Pattern) (h : Agree support p q) : d3139 p = d3139 q := by
  simp only [d3139, h 115 (by decide), agree3138 p q h, agree2989 p q h]
theorem nonnegative3139 (p : Pattern) : 0 ≤ d3139 p :=
  nonnegative_ite (p 115) (nonnegative3138 p) (nonnegative2989 p)
def d3140 (p : Pattern) : Int := if p 71 then d3139 p else d2992 p
theorem agree3140 (p q : Pattern) (h : Agree support p q) : d3140 p = d3140 q := by
  simp only [d3140, h 71 (by decide), agree3139 p q h, agree2992 p q h]
theorem nonnegative3140 (p : Pattern) : 0 ≤ d3140 p :=
  nonnegative_ite (p 71) (nonnegative3139 p) (nonnegative2992 p)
def d3141 (p : Pattern) : Int := if p 163 then d12 p else d2996 p
theorem agree3141 (p q : Pattern) (h : Agree support p q) : d3141 p = d3141 q := by
  simp only [d3141, h 163 (by decide), agree12 p q h, agree2996 p q h]
theorem nonnegative3141 (p : Pattern) : 0 ≤ d3141 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2996 p)
def d3142 (p : Pattern) : Int := if p 162 then d3141 p else d3017 p
theorem agree3142 (p q : Pattern) (h : Agree support p q) : d3142 p = d3142 q := by
  simp only [d3142, h 162 (by decide), agree3141 p q h, agree3017 p q h]
theorem nonnegative3142 (p : Pattern) : 0 ≤ d3142 p :=
  nonnegative_ite (p 162) (nonnegative3141 p) (nonnegative3017 p)
def d3143 (p : Pattern) : Int := if p 162 then d12 p else d3141 p
theorem agree3143 (p q : Pattern) (h : Agree support p q) : d3143 p = d3143 q := by
  simp only [d3143, h 162 (by decide), agree12 p q h, agree3141 p q h]
theorem nonnegative3143 (p : Pattern) : 0 ≤ d3143 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3141 p)
def d3144 (p : Pattern) : Int := if p 161 then d3143 p else d3142 p
theorem agree3144 (p q : Pattern) (h : Agree support p q) : d3144 p = d3144 q := by
  simp only [d3144, h 161 (by decide), agree3143 p q h, agree3142 p q h]
theorem nonnegative3144 (p : Pattern) : 0 ≤ d3144 p :=
  nonnegative_ite (p 161) (nonnegative3143 p) (nonnegative3142 p)
def d3145 (p : Pattern) : Int := if p 163 then d12 p else d3008 p
theorem agree3145 (p q : Pattern) (h : Agree support p q) : d3145 p = d3145 q := by
  simp only [d3145, h 163 (by decide), agree12 p q h, agree3008 p q h]
theorem nonnegative3145 (p : Pattern) : 0 ≤ d3145 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3008 p)
def d3146 (p : Pattern) : Int := if p 162 then d3145 p else d3025 p
theorem agree3146 (p q : Pattern) (h : Agree support p q) : d3146 p = d3146 q := by
  simp only [d3146, h 162 (by decide), agree3145 p q h, agree3025 p q h]
theorem nonnegative3146 (p : Pattern) : 0 ≤ d3146 p :=
  nonnegative_ite (p 162) (nonnegative3145 p) (nonnegative3025 p)
def d3147 (p : Pattern) : Int := if p 162 then d12 p else d3145 p
theorem agree3147 (p q : Pattern) (h : Agree support p q) : d3147 p = d3147 q := by
  simp only [d3147, h 162 (by decide), agree12 p q h, agree3145 p q h]
theorem nonnegative3147 (p : Pattern) : 0 ≤ d3147 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3145 p)
def d3148 (p : Pattern) : Int := if p 161 then d3147 p else d3146 p
theorem agree3148 (p q : Pattern) (h : Agree support p q) : d3148 p = d3148 q := by
  simp only [d3148, h 161 (by decide), agree3147 p q h, agree3146 p q h]
theorem nonnegative3148 (p : Pattern) : 0 ≤ d3148 p :=
  nonnegative_ite (p 161) (nonnegative3147 p) (nonnegative3146 p)
def d3149 (p : Pattern) : Int := if p 160 then d3148 p else d3144 p
theorem agree3149 (p q : Pattern) (h : Agree support p q) : d3149 p = d3149 q := by
  simp only [d3149, h 160 (by decide), agree3148 p q h, agree3144 p q h]
theorem nonnegative3149 (p : Pattern) : 0 ≤ d3149 p :=
  nonnegative_ite (p 160) (nonnegative3148 p) (nonnegative3144 p)
def d3150 (p : Pattern) : Int := if p 141 then d3149 p else d3014 p
theorem agree3150 (p q : Pattern) (h : Agree support p q) : d3150 p = d3150 q := by
  simp only [d3150, h 141 (by decide), agree3149 p q h, agree3014 p q h]
theorem nonnegative3150 (p : Pattern) : 0 ≤ d3150 p :=
  nonnegative_ite (p 141) (nonnegative3149 p) (nonnegative3014 p)
def d3151 (p : Pattern) : Int := if p 163 then d12 p else d3043 p
theorem agree3151 (p q : Pattern) (h : Agree support p q) : d3151 p = d3151 q := by
  simp only [d3151, h 163 (by decide), agree12 p q h, agree3043 p q h]
theorem nonnegative3151 (p : Pattern) : 0 ≤ d3151 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3043 p)
def d3152 (p : Pattern) : Int := if p 162 then d3151 p else d3055 p
theorem agree3152 (p q : Pattern) (h : Agree support p q) : d3152 p = d3152 q := by
  simp only [d3152, h 162 (by decide), agree3151 p q h, agree3055 p q h]
theorem nonnegative3152 (p : Pattern) : 0 ≤ d3152 p :=
  nonnegative_ite (p 162) (nonnegative3151 p) (nonnegative3055 p)
def d3153 (p : Pattern) : Int := if p 162 then d12 p else d3151 p
theorem agree3153 (p q : Pattern) (h : Agree support p q) : d3153 p = d3153 q := by
  simp only [d3153, h 162 (by decide), agree12 p q h, agree3151 p q h]
theorem nonnegative3153 (p : Pattern) : 0 ≤ d3153 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3151 p)
def d3154 (p : Pattern) : Int := if p 161 then d3153 p else d3152 p
theorem agree3154 (p q : Pattern) (h : Agree support p q) : d3154 p = d3154 q := by
  simp only [d3154, h 161 (by decide), agree3153 p q h, agree3152 p q h]
theorem nonnegative3154 (p : Pattern) : 0 ≤ d3154 p :=
  nonnegative_ite (p 161) (nonnegative3153 p) (nonnegative3152 p)
def d3155 (p : Pattern) : Int := if p 160 then d3063 p else d3154 p
theorem agree3155 (p q : Pattern) (h : Agree support p q) : d3155 p = d3155 q := by
  simp only [d3155, h 160 (by decide), agree3063 p q h, agree3154 p q h]
theorem nonnegative3155 (p : Pattern) : 0 ≤ d3155 p :=
  nonnegative_ite (p 160) (nonnegative3063 p) (nonnegative3154 p)
def d3156 (p : Pattern) : Int := if p 141 then d3155 p else d3054 p
theorem agree3156 (p q : Pattern) (h : Agree support p q) : d3156 p = d3156 q := by
  simp only [d3156, h 141 (by decide), agree3155 p q h, agree3054 p q h]
theorem nonnegative3156 (p : Pattern) : 0 ≤ d3156 p :=
  nonnegative_ite (p 141) (nonnegative3155 p) (nonnegative3054 p)
def d3157 (p : Pattern) : Int := if p 138 then d3156 p else d3150 p
theorem agree3157 (p q : Pattern) (h : Agree support p q) : d3157 p = d3157 q := by
  simp only [d3157, h 138 (by decide), agree3156 p q h, agree3150 p q h]
theorem nonnegative3157 (p : Pattern) : 0 ≤ d3157 p :=
  nonnegative_ite (p 138) (nonnegative3156 p) (nonnegative3150 p)
def d3158 (p : Pattern) : Int := if p 138 then d3070 p else d3156 p
theorem agree3158 (p q : Pattern) (h : Agree support p q) : d3158 p = d3158 q := by
  simp only [d3158, h 138 (by decide), agree3070 p q h, agree3156 p q h]
theorem nonnegative3158 (p : Pattern) : 0 ≤ d3158 p :=
  nonnegative_ite (p 138) (nonnegative3070 p) (nonnegative3156 p)
def d3159 (p : Pattern) : Int := if p 116 then d3158 p else d3157 p
theorem agree3159 (p q : Pattern) (h : Agree support p q) : d3159 p = d3159 q := by
  simp only [d3159, h 116 (by decide), agree3158 p q h, agree3157 p q h]
theorem nonnegative3159 (p : Pattern) : 0 ≤ d3159 p :=
  nonnegative_ite (p 116) (nonnegative3158 p) (nonnegative3157 p)
def d3160 (p : Pattern) : Int := if p 204 then d1951 p else d103 p
theorem agree3160 (p q : Pattern) (h : Agree support p q) : d3160 p = d3160 q := by
  simp only [d3160, h 204 (by decide), agree1951 p q h, agree103 p q h]
theorem nonnegative3160 (p : Pattern) : 0 ≤ d3160 p :=
  nonnegative_ite (p 204) (nonnegative1951 p) (nonnegative103 p)
def d3161 (p : Pattern) : Int := if p 182 then d2109 p else d3160 p
theorem agree3161 (p q : Pattern) (h : Agree support p q) : d3161 p = d3161 q := by
  simp only [d3161, h 182 (by decide), agree2109 p q h, agree3160 p q h]
theorem nonnegative3161 (p : Pattern) : 0 ≤ d3161 p :=
  nonnegative_ite (p 182) (nonnegative2109 p) (nonnegative3160 p)
def d3162 (p : Pattern) : Int := if p 163 then d3043 p else d3161 p
theorem agree3162 (p q : Pattern) (h : Agree support p q) : d3162 p = d3162 q := by
  simp only [d3162, h 163 (by decide), agree3043 p q h, agree3161 p q h]
theorem nonnegative3162 (p : Pattern) : 0 ≤ d3162 p :=
  nonnegative_ite (p 163) (nonnegative3043 p) (nonnegative3161 p)
def d3163 (p : Pattern) : Int := if p 162 then d3162 p else d3034 p
theorem agree3163 (p q : Pattern) (h : Agree support p q) : d3163 p = d3163 q := by
  simp only [d3163, h 162 (by decide), agree3162 p q h, agree3034 p q h]
theorem nonnegative3163 (p : Pattern) : 0 ≤ d3163 p :=
  nonnegative_ite (p 162) (nonnegative3162 p) (nonnegative3034 p)
def d3164 (p : Pattern) : Int := if p 163 then d3043 p else d3040 p
theorem agree3164 (p q : Pattern) (h : Agree support p q) : d3164 p = d3164 q := by
  simp only [d3164, h 163 (by decide), agree3043 p q h, agree3040 p q h]
theorem nonnegative3164 (p : Pattern) : 0 ≤ d3164 p :=
  nonnegative_ite (p 163) (nonnegative3043 p) (nonnegative3040 p)
def d3165 (p : Pattern) : Int := if p 162 then d2999 p else d3164 p
theorem agree3165 (p q : Pattern) (h : Agree support p q) : d3165 p = d3165 q := by
  simp only [d3165, h 162 (by decide), agree2999 p q h, agree3164 p q h]
theorem nonnegative3165 (p : Pattern) : 0 ≤ d3165 p :=
  nonnegative_ite (p 162) (nonnegative2999 p) (nonnegative3164 p)
def d3166 (p : Pattern) : Int := if p 161 then d3165 p else d3163 p
theorem agree3166 (p q : Pattern) (h : Agree support p q) : d3166 p = d3166 q := by
  simp only [d3166, h 161 (by decide), agree3165 p q h, agree3163 p q h]
theorem nonnegative3166 (p : Pattern) : 0 ≤ d3166 p :=
  nonnegative_ite (p 161) (nonnegative3165 p) (nonnegative3163 p)
def d3167 (p : Pattern) : Int := if p 182 then d1906 p else d3023 p
theorem agree3167 (p q : Pattern) (h : Agree support p q) : d3167 p = d3167 q := by
  simp only [d3167, h 182 (by decide), agree1906 p q h, agree3023 p q h]
theorem nonnegative3167 (p : Pattern) : 0 ≤ d3167 p :=
  nonnegative_ite (p 182) (nonnegative1906 p) (nonnegative3023 p)
def d3168 (p : Pattern) : Int := if p 163 then d3167 p else d3048 p
theorem agree3168 (p q : Pattern) (h : Agree support p q) : d3168 p = d3168 q := by
  simp only [d3168, h 163 (by decide), agree3167 p q h, agree3048 p q h]
theorem nonnegative3168 (p : Pattern) : 0 ≤ d3168 p :=
  nonnegative_ite (p 163) (nonnegative3167 p) (nonnegative3048 p)
def d3169 (p : Pattern) : Int := if p 162 then d3145 p else d3168 p
theorem agree3169 (p q : Pattern) (h : Agree support p q) : d3169 p = d3169 q := by
  simp only [d3169, h 162 (by decide), agree3145 p q h, agree3168 p q h]
theorem nonnegative3169 (p : Pattern) : 0 ≤ d3169 p :=
  nonnegative_ite (p 162) (nonnegative3145 p) (nonnegative3168 p)
def d3170 (p : Pattern) : Int := if p 182 then d12 p else d3049 p
theorem agree3170 (p q : Pattern) (h : Agree support p q) : d3170 p = d3170 q := by
  simp only [d3170, h 182 (by decide), agree12 p q h, agree3049 p q h]
theorem nonnegative3170 (p : Pattern) : 0 ≤ d3170 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3049 p)
def d3171 (p : Pattern) : Int := if p 163 then d12 p else d3170 p
theorem agree3171 (p q : Pattern) (h : Agree support p q) : d3171 p = d3171 q := by
  simp only [d3171, h 163 (by decide), agree12 p q h, agree3170 p q h]
theorem nonnegative3171 (p : Pattern) : 0 ≤ d3171 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3170 p)
def d3172 (p : Pattern) : Int := if p 162 then d12 p else d3171 p
theorem agree3172 (p q : Pattern) (h : Agree support p q) : d3172 p = d3172 q := by
  simp only [d3172, h 162 (by decide), agree12 p q h, agree3171 p q h]
theorem nonnegative3172 (p : Pattern) : 0 ≤ d3172 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3171 p)
def d3173 (p : Pattern) : Int := if p 161 then d3172 p else d3169 p
theorem agree3173 (p q : Pattern) (h : Agree support p q) : d3173 p = d3173 q := by
  simp only [d3173, h 161 (by decide), agree3172 p q h, agree3169 p q h]
theorem nonnegative3173 (p : Pattern) : 0 ≤ d3173 p :=
  nonnegative_ite (p 161) (nonnegative3172 p) (nonnegative3169 p)
def d3174 (p : Pattern) : Int := if p 160 then d3173 p else d3166 p
theorem agree3174 (p q : Pattern) (h : Agree support p q) : d3174 p = d3174 q := by
  simp only [d3174, h 160 (by decide), agree3173 p q h, agree3166 p q h]
theorem nonnegative3174 (p : Pattern) : 0 ≤ d3174 p :=
  nonnegative_ite (p 160) (nonnegative3173 p) (nonnegative3166 p)
def d3175 (p : Pattern) : Int := if p 225 then d1892 p else d1895 p
theorem agree3175 (p q : Pattern) (h : Agree support p q) : d3175 p = d3175 q := by
  simp only [d3175, h 225 (by decide), agree1892 p q h, agree1895 p q h]
theorem nonnegative3175 (p : Pattern) : 0 ≤ d3175 p :=
  nonnegative_ite (p 225) (nonnegative1892 p) (nonnegative1895 p)
def d3176 (p : Pattern) : Int := if p 224 then d3175 p else d1893 p
theorem agree3176 (p q : Pattern) (h : Agree support p q) : d3176 p = d3176 q := by
  simp only [d3176, h 224 (by decide), agree3175 p q h, agree1893 p q h]
theorem nonnegative3176 (p : Pattern) : 0 ≤ d3176 p :=
  nonnegative_ite (p 224) (nonnegative3175 p) (nonnegative1893 p)
def d3177 (p : Pattern) : Int := if p 204 then d3176 p else d116 p
theorem agree3177 (p q : Pattern) (h : Agree support p q) : d3177 p = d3177 q := by
  simp only [d3177, h 204 (by decide), agree3176 p q h, agree116 p q h]
theorem nonnegative3177 (p : Pattern) : 0 ≤ d3177 p :=
  nonnegative_ite (p 204) (nonnegative3176 p) (nonnegative116 p)
def d3178 (p : Pattern) : Int := if p 182 then d2126 p else d3177 p
theorem agree3178 (p q : Pattern) (h : Agree support p q) : d3178 p = d3178 q := by
  simp only [d3178, h 182 (by decide), agree2126 p q h, agree3177 p q h]
theorem nonnegative3178 (p : Pattern) : 0 ≤ d3178 p :=
  nonnegative_ite (p 182) (nonnegative2126 p) (nonnegative3177 p)
def d3179 (p : Pattern) : Int := if p 163 then d3178 p else d3161 p
theorem agree3179 (p q : Pattern) (h : Agree support p q) : d3179 p = d3179 q := by
  simp only [d3179, h 163 (by decide), agree3178 p q h, agree3161 p q h]
theorem nonnegative3179 (p : Pattern) : 0 ≤ d3179 p :=
  nonnegative_ite (p 163) (nonnegative3178 p) (nonnegative3161 p)
def d3180 (p : Pattern) : Int := if p 204 then d2136 p else d107 p
theorem agree3180 (p q : Pattern) (h : Agree support p q) : d3180 p = d3180 q := by
  simp only [d3180, h 204 (by decide), agree2136 p q h, agree107 p q h]
theorem nonnegative3180 (p : Pattern) : 0 ≤ d3180 p :=
  nonnegative_ite (p 204) (nonnegative2136 p) (nonnegative107 p)
def d3181 (p : Pattern) : Int := if p 182 then d2131 p else d3180 p
theorem agree3181 (p q : Pattern) (h : Agree support p q) : d3181 p = d3181 q := by
  simp only [d3181, h 182 (by decide), agree2131 p q h, agree3180 p q h]
theorem nonnegative3181 (p : Pattern) : 0 ≤ d3181 p :=
  nonnegative_ite (p 182) (nonnegative2131 p) (nonnegative3180 p)
def d3182 (p : Pattern) : Int := if p 163 then d12 p else d3181 p
theorem agree3182 (p q : Pattern) (h : Agree support p q) : d3182 p = d3182 q := by
  simp only [d3182, h 163 (by decide), agree12 p q h, agree3181 p q h]
theorem nonnegative3182 (p : Pattern) : 0 ≤ d3182 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3181 p)
def d3183 (p : Pattern) : Int := if p 162 then d3182 p else d3179 p
theorem agree3183 (p q : Pattern) (h : Agree support p q) : d3183 p = d3183 q := by
  simp only [d3183, h 162 (by decide), agree3182 p q h, agree3179 p q h]
theorem nonnegative3183 (p : Pattern) : 0 ≤ d3183 p :=
  nonnegative_ite (p 162) (nonnegative3182 p) (nonnegative3179 p)
def d3184 (p : Pattern) : Int := if p 182 then d2137 p else d3007 p
theorem agree3184 (p q : Pattern) (h : Agree support p q) : d3184 p = d3184 q := by
  simp only [d3184, h 182 (by decide), agree2137 p q h, agree3007 p q h]
theorem nonnegative3184 (p : Pattern) : 0 ≤ d3184 p :=
  nonnegative_ite (p 182) (nonnegative2137 p) (nonnegative3007 p)
def d3185 (p : Pattern) : Int := if p 163 then d12 p else d3184 p
theorem agree3185 (p q : Pattern) (h : Agree support p q) : d3185 p = d3185 q := by
  simp only [d3185, h 163 (by decide), agree12 p q h, agree3184 p q h]
theorem nonnegative3185 (p : Pattern) : 0 ≤ d3185 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3184 p)
def d3186 (p : Pattern) : Int := if p 162 then d12 p else d3185 p
theorem agree3186 (p q : Pattern) (h : Agree support p q) : d3186 p = d3186 q := by
  simp only [d3186, h 162 (by decide), agree12 p q h, agree3185 p q h]
theorem nonnegative3186 (p : Pattern) : 0 ≤ d3186 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3185 p)
def d3187 (p : Pattern) : Int := if p 161 then d3186 p else d3183 p
theorem agree3187 (p q : Pattern) (h : Agree support p q) : d3187 p = d3187 q := by
  simp only [d3187, h 161 (by decide), agree3186 p q h, agree3183 p q h]
theorem nonnegative3187 (p : Pattern) : 0 ≤ d3187 p :=
  nonnegative_ite (p 161) (nonnegative3186 p) (nonnegative3183 p)
def d3188 (p : Pattern) : Int := if p 182 then d1906 p else d3007 p
theorem agree3188 (p q : Pattern) (h : Agree support p q) : d3188 p = d3188 q := by
  simp only [d3188, h 182 (by decide), agree1906 p q h, agree3007 p q h]
theorem nonnegative3188 (p : Pattern) : 0 ≤ d3188 p :=
  nonnegative_ite (p 182) (nonnegative1906 p) (nonnegative3007 p)
def d3189 (p : Pattern) : Int := if p 163 then d3008 p else d3188 p
theorem agree3189 (p q : Pattern) (h : Agree support p q) : d3189 p = d3189 q := by
  simp only [d3189, h 163 (by decide), agree3008 p q h, agree3188 p q h]
theorem nonnegative3189 (p : Pattern) : 0 ≤ d3189 p :=
  nonnegative_ite (p 163) (nonnegative3008 p) (nonnegative3188 p)
def d3190 (p : Pattern) : Int := if p 162 then d3171 p else d3189 p
theorem agree3190 (p q : Pattern) (h : Agree support p q) : d3190 p = d3190 q := by
  simp only [d3190, h 162 (by decide), agree3171 p q h, agree3189 p q h]
theorem nonnegative3190 (p : Pattern) : 0 ≤ d3190 p :=
  nonnegative_ite (p 162) (nonnegative3171 p) (nonnegative3189 p)
def d3191 (p : Pattern) : Int := if p 162 then d12 p else d2918 p
theorem agree3191 (p q : Pattern) (h : Agree support p q) : d3191 p = d3191 q := by
  simp only [d3191, h 162 (by decide), agree12 p q h, agree2918 p q h]
theorem nonnegative3191 (p : Pattern) : 0 ≤ d3191 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2918 p)
def d3192 (p : Pattern) : Int := if p 161 then d3191 p else d3190 p
theorem agree3192 (p q : Pattern) (h : Agree support p q) : d3192 p = d3192 q := by
  simp only [d3192, h 161 (by decide), agree3191 p q h, agree3190 p q h]
theorem nonnegative3192 (p : Pattern) : 0 ≤ d3192 p :=
  nonnegative_ite (p 161) (nonnegative3191 p) (nonnegative3190 p)
def d3193 (p : Pattern) : Int := if p 160 then d3192 p else d3187 p
theorem agree3193 (p q : Pattern) (h : Agree support p q) : d3193 p = d3193 q := by
  simp only [d3193, h 160 (by decide), agree3192 p q h, agree3187 p q h]
theorem nonnegative3193 (p : Pattern) : 0 ≤ d3193 p :=
  nonnegative_ite (p 160) (nonnegative3192 p) (nonnegative3187 p)
def d3194 (p : Pattern) : Int := if p 141 then d3193 p else d3174 p
theorem agree3194 (p q : Pattern) (h : Agree support p q) : d3194 p = d3194 q := by
  simp only [d3194, h 141 (by decide), agree3193 p q h, agree3174 p q h]
theorem nonnegative3194 (p : Pattern) : 0 ≤ d3194 p :=
  nonnegative_ite (p 141) (nonnegative3193 p) (nonnegative3174 p)
def d3195 (p : Pattern) : Int := if p 163 then d3042 p else d3040 p
theorem agree3195 (p q : Pattern) (h : Agree support p q) : d3195 p = d3195 q := by
  simp only [d3195, h 163 (by decide), agree3042 p q h, agree3040 p q h]
theorem nonnegative3195 (p : Pattern) : 0 ≤ d3195 p :=
  nonnegative_ite (p 163) (nonnegative3042 p) (nonnegative3040 p)
def d3196 (p : Pattern) : Int := if p 163 then d2931 p else d3048 p
theorem agree3196 (p q : Pattern) (h : Agree support p q) : d3196 p = d3196 q := by
  simp only [d3196, h 163 (by decide), agree2931 p q h, agree3048 p q h]
theorem nonnegative3196 (p : Pattern) : 0 ≤ d3196 p :=
  nonnegative_ite (p 163) (nonnegative2931 p) (nonnegative3048 p)
def d3197 (p : Pattern) : Int := if p 162 then d3196 p else d3195 p
theorem agree3197 (p q : Pattern) (h : Agree support p q) : d3197 p = d3197 q := by
  simp only [d3197, h 162 (by decide), agree3196 p q h, agree3195 p q h]
theorem nonnegative3197 (p : Pattern) : 0 ≤ d3197 p :=
  nonnegative_ite (p 162) (nonnegative3196 p) (nonnegative3195 p)
def d3198 (p : Pattern) : Int := if p 161 then d3059 p else d3197 p
theorem agree3198 (p q : Pattern) (h : Agree support p q) : d3198 p = d3198 q := by
  simp only [d3198, h 161 (by decide), agree3059 p q h, agree3197 p q h]
theorem nonnegative3198 (p : Pattern) : 0 ≤ d3198 p :=
  nonnegative_ite (p 161) (nonnegative3059 p) (nonnegative3197 p)
def d3199 (p : Pattern) : Int := if p 160 then d3063 p else d3198 p
theorem agree3199 (p q : Pattern) (h : Agree support p q) : d3199 p = d3199 q := by
  simp only [d3199, h 160 (by decide), agree3063 p q h, agree3198 p q h]
theorem nonnegative3199 (p : Pattern) : 0 ≤ d3199 p :=
  nonnegative_ite (p 160) (nonnegative3063 p) (nonnegative3198 p)
def d3200 (p : Pattern) : Int := if p 182 then d2158 p else d3023 p
theorem agree3200 (p q : Pattern) (h : Agree support p q) : d3200 p = d3200 q := by
  simp only [d3200, h 182 (by decide), agree2158 p q h, agree3023 p q h]
theorem nonnegative3200 (p : Pattern) : 0 ≤ d3200 p :=
  nonnegative_ite (p 182) (nonnegative2158 p) (nonnegative3023 p)
def d3201 (p : Pattern) : Int := if p 163 then d3048 p else d3200 p
theorem agree3201 (p q : Pattern) (h : Agree support p q) : d3201 p = d3201 q := by
  simp only [d3201, h 163 (by decide), agree3048 p q h, agree3200 p q h]
theorem nonnegative3201 (p : Pattern) : 0 ≤ d3201 p :=
  nonnegative_ite (p 163) (nonnegative3048 p) (nonnegative3200 p)
def d3202 (p : Pattern) : Int := if p 162 then d3151 p else d3201 p
theorem agree3202 (p q : Pattern) (h : Agree support p q) : d3202 p = d3202 q := by
  simp only [d3202, h 162 (by decide), agree3151 p q h, agree3201 p q h]
theorem nonnegative3202 (p : Pattern) : 0 ≤ d3202 p :=
  nonnegative_ite (p 162) (nonnegative3151 p) (nonnegative3201 p)
def d3203 (p : Pattern) : Int := if p 161 then d3062 p else d3202 p
theorem agree3203 (p q : Pattern) (h : Agree support p q) : d3203 p = d3203 q := by
  simp only [d3203, h 161 (by decide), agree3062 p q h, agree3202 p q h]
theorem nonnegative3203 (p : Pattern) : 0 ≤ d3203 p :=
  nonnegative_ite (p 161) (nonnegative3062 p) (nonnegative3202 p)
def d3204 (p : Pattern) : Int := if p 162 then d12 p else d2958 p
theorem agree3204 (p q : Pattern) (h : Agree support p q) : d3204 p = d3204 q := by
  simp only [d3204, h 162 (by decide), agree12 p q h, agree2958 p q h]
theorem nonnegative3204 (p : Pattern) : 0 ≤ d3204 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2958 p)
def d3205 (p : Pattern) : Int := if p 161 then d12 p else d3204 p
theorem agree3205 (p q : Pattern) (h : Agree support p q) : d3205 p = d3205 q := by
  simp only [d3205, h 161 (by decide), agree12 p q h, agree3204 p q h]
theorem nonnegative3205 (p : Pattern) : 0 ≤ d3205 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3204 p)
def d3206 (p : Pattern) : Int := if p 160 then d3205 p else d3203 p
theorem agree3206 (p q : Pattern) (h : Agree support p q) : d3206 p = d3206 q := by
  simp only [d3206, h 160 (by decide), agree3205 p q h, agree3203 p q h]
theorem nonnegative3206 (p : Pattern) : 0 ≤ d3206 p :=
  nonnegative_ite (p 160) (nonnegative3205 p) (nonnegative3203 p)
def d3207 (p : Pattern) : Int := if p 141 then d3206 p else d3199 p
theorem agree3207 (p q : Pattern) (h : Agree support p q) : d3207 p = d3207 q := by
  simp only [d3207, h 141 (by decide), agree3206 p q h, agree3199 p q h]
theorem nonnegative3207 (p : Pattern) : 0 ≤ d3207 p :=
  nonnegative_ite (p 141) (nonnegative3206 p) (nonnegative3199 p)
def d3208 (p : Pattern) : Int := if p 138 then d3207 p else d3194 p
theorem agree3208 (p q : Pattern) (h : Agree support p q) : d3208 p = d3208 q := by
  simp only [d3208, h 138 (by decide), agree3207 p q h, agree3194 p q h]
theorem nonnegative3208 (p : Pattern) : 0 ≤ d3208 p :=
  nonnegative_ite (p 138) (nonnegative3207 p) (nonnegative3194 p)
def d3209 (p : Pattern) : Int := if p 163 then d2957 p else d3048 p
theorem agree3209 (p q : Pattern) (h : Agree support p q) : d3209 p = d3209 q := by
  simp only [d3209, h 163 (by decide), agree2957 p q h, agree3048 p q h]
theorem nonnegative3209 (p : Pattern) : 0 ≤ d3209 p :=
  nonnegative_ite (p 163) (nonnegative2957 p) (nonnegative3048 p)
def d3210 (p : Pattern) : Int := if p 162 then d3209 p else d3195 p
theorem agree3210 (p q : Pattern) (h : Agree support p q) : d3210 p = d3210 q := by
  simp only [d3210, h 162 (by decide), agree3209 p q h, agree3195 p q h]
theorem nonnegative3210 (p : Pattern) : 0 ≤ d3210 p :=
  nonnegative_ite (p 162) (nonnegative3209 p) (nonnegative3195 p)
def d3211 (p : Pattern) : Int := if p 163 then d2957 p else d3043 p
theorem agree3211 (p q : Pattern) (h : Agree support p q) : d3211 p = d3211 q := by
  simp only [d3211, h 163 (by decide), agree2957 p q h, agree3043 p q h]
theorem nonnegative3211 (p : Pattern) : 0 ≤ d3211 p :=
  nonnegative_ite (p 163) (nonnegative2957 p) (nonnegative3043 p)
def d3212 (p : Pattern) : Int := if p 162 then d12 p else d3211 p
theorem agree3212 (p q : Pattern) (h : Agree support p q) : d3212 p = d3212 q := by
  simp only [d3212, h 162 (by decide), agree12 p q h, agree3211 p q h]
theorem nonnegative3212 (p : Pattern) : 0 ≤ d3212 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3211 p)
def d3213 (p : Pattern) : Int := if p 161 then d3212 p else d3210 p
theorem agree3213 (p q : Pattern) (h : Agree support p q) : d3213 p = d3213 q := by
  simp only [d3213, h 161 (by decide), agree3212 p q h, agree3210 p q h]
theorem nonnegative3213 (p : Pattern) : 0 ≤ d3213 p :=
  nonnegative_ite (p 161) (nonnegative3212 p) (nonnegative3210 p)
def d3214 (p : Pattern) : Int := if p 163 then d2931 p else d3050 p
theorem agree3214 (p q : Pattern) (h : Agree support p q) : d3214 p = d3214 q := by
  simp only [d3214, h 163 (by decide), agree2931 p q h, agree3050 p q h]
theorem nonnegative3214 (p : Pattern) : 0 ≤ d3214 p :=
  nonnegative_ite (p 163) (nonnegative2931 p) (nonnegative3050 p)
def d3215 (p : Pattern) : Int := if p 162 then d12 p else d3214 p
theorem agree3215 (p q : Pattern) (h : Agree support p q) : d3215 p = d3215 q := by
  simp only [d3215, h 162 (by decide), agree12 p q h, agree3214 p q h]
theorem nonnegative3215 (p : Pattern) : 0 ≤ d3215 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3214 p)
def d3216 (p : Pattern) : Int := if p 161 then d12 p else d3215 p
theorem agree3216 (p q : Pattern) (h : Agree support p q) : d3216 p = d3216 q := by
  simp only [d3216, h 161 (by decide), agree12 p q h, agree3215 p q h]
theorem nonnegative3216 (p : Pattern) : 0 ≤ d3216 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3215 p)
def d3217 (p : Pattern) : Int := if p 160 then d3216 p else d3213 p
theorem agree3217 (p q : Pattern) (h : Agree support p q) : d3217 p = d3217 q := by
  simp only [d3217, h 160 (by decide), agree3216 p q h, agree3213 p q h]
theorem nonnegative3217 (p : Pattern) : 0 ≤ d3217 p :=
  nonnegative_ite (p 160) (nonnegative3216 p) (nonnegative3213 p)
def d3218 (p : Pattern) : Int := if p 141 then d3206 p else d3217 p
theorem agree3218 (p q : Pattern) (h : Agree support p q) : d3218 p = d3218 q := by
  simp only [d3218, h 141 (by decide), agree3206 p q h, agree3217 p q h]
theorem nonnegative3218 (p : Pattern) : 0 ≤ d3218 p :=
  nonnegative_ite (p 141) (nonnegative3206 p) (nonnegative3217 p)
def d3219 (p : Pattern) : Int := if p 138 then d12 p else d3218 p
theorem agree3219 (p q : Pattern) (h : Agree support p q) : d3219 p = d3219 q := by
  simp only [d3219, h 138 (by decide), agree12 p q h, agree3218 p q h]
theorem nonnegative3219 (p : Pattern) : 0 ≤ d3219 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3218 p)
def d3220 (p : Pattern) : Int := if p 116 then d3219 p else d3208 p
theorem agree3220 (p q : Pattern) (h : Agree support p q) : d3220 p = d3220 q := by
  simp only [d3220, h 116 (by decide), agree3219 p q h, agree3208 p q h]
theorem nonnegative3220 (p : Pattern) : 0 ≤ d3220 p :=
  nonnegative_ite (p 116) (nonnegative3219 p) (nonnegative3208 p)
def d3221 (p : Pattern) : Int := if p 115 then d3220 p else d3159 p
theorem agree3221 (p q : Pattern) (h : Agree support p q) : d3221 p = d3221 q := by
  simp only [d3221, h 115 (by decide), agree3220 p q h, agree3159 p q h]
theorem nonnegative3221 (p : Pattern) : 0 ≤ d3221 p :=
  nonnegative_ite (p 115) (nonnegative3220 p) (nonnegative3159 p)
def d3222 (p : Pattern) : Int := if p 71 then d3221 p else d2992 p
theorem agree3222 (p q : Pattern) (h : Agree support p q) : d3222 p = d3222 q := by
  simp only [d3222, h 71 (by decide), agree3221 p q h, agree2992 p q h]
theorem nonnegative3222 (p : Pattern) : 0 ≤ d3222 p :=
  nonnegative_ite (p 71) (nonnegative3221 p) (nonnegative2992 p)
def d3223 (p : Pattern) : Int := if p 49 then d3222 p else d3140 p
theorem agree3223 (p q : Pattern) (h : Agree support p q) : d3223 p = d3223 q := by
  simp only [d3223, h 49 (by decide), agree3222 p q h, agree3140 p q h]
theorem nonnegative3223 (p : Pattern) : 0 ≤ d3223 p :=
  nonnegative_ite (p 49) (nonnegative3222 p) (nonnegative3140 p)
def d3224 (p : Pattern) : Int := if p 48 then d3223 p else d3077 p
theorem agree3224 (p q : Pattern) (h : Agree support p q) : d3224 p = d3224 q := by
  simp only [d3224, h 48 (by decide), agree3223 p q h, agree3077 p q h]
theorem nonnegative3224 (p : Pattern) : 0 ≤ d3224 p :=
  nonnegative_ite (p 48) (nonnegative3223 p) (nonnegative3077 p)
def d3225 (p : Pattern) : Int := if p 246 then d190 p else d0 p
theorem agree3225 (p q : Pattern) (h : Agree support p q) : d3225 p = d3225 q := by
  simp only [d3225, h 246 (by decide), agree190 p q h, agree0 p q h]
theorem nonnegative3225 (p : Pattern) : 0 ≤ d3225 p :=
  nonnegative_ite (p 246) (nonnegative190 p) (nonnegative0 p)
def d3226 (p : Pattern) : Int := if p 246 then d12 p else d0 p
theorem agree3226 (p q : Pattern) (h : Agree support p q) : d3226 p = d3226 q := by
  simp only [d3226, h 246 (by decide), agree12 p q h, agree0 p q h]
theorem nonnegative3226 (p : Pattern) : 0 ≤ d3226 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative0 p)
def d3227 (p : Pattern) : Int := if p 225 then d3226 p else d3225 p
theorem agree3227 (p q : Pattern) (h : Agree support p q) : d3227 p = d3227 q := by
  simp only [d3227, h 225 (by decide), agree3226 p q h, agree3225 p q h]
theorem nonnegative3227 (p : Pattern) : 0 ≤ d3227 p :=
  nonnegative_ite (p 225) (nonnegative3226 p) (nonnegative3225 p)
def d3228 (p : Pattern) : Int := if p 224 then d3226 p else d3227 p
theorem agree3228 (p q : Pattern) (h : Agree support p q) : d3228 p = d3228 q := by
  simp only [d3228, h 224 (by decide), agree3226 p q h, agree3227 p q h]
theorem nonnegative3228 (p : Pattern) : 0 ≤ d3228 p :=
  nonnegative_ite (p 224) (nonnegative3226 p) (nonnegative3227 p)
def d3229 (p : Pattern) : Int := if p 204 then d3226 p else d3228 p
theorem agree3229 (p q : Pattern) (h : Agree support p q) : d3229 p = d3229 q := by
  simp only [d3229, h 204 (by decide), agree3226 p q h, agree3228 p q h]
theorem nonnegative3229 (p : Pattern) : 0 ≤ d3229 p :=
  nonnegative_ite (p 204) (nonnegative3226 p) (nonnegative3228 p)
def d3230 (p : Pattern) : Int := if p 204 then d12 p else d3226 p
theorem agree3230 (p q : Pattern) (h : Agree support p q) : d3230 p = d3230 q := by
  simp only [d3230, h 204 (by decide), agree12 p q h, agree3226 p q h]
theorem nonnegative3230 (p : Pattern) : 0 ≤ d3230 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3226 p)
def d3231 (p : Pattern) : Int := if p 182 then d3230 p else d3229 p
theorem agree3231 (p q : Pattern) (h : Agree support p q) : d3231 p = d3231 q := by
  simp only [d3231, h 182 (by decide), agree3230 p q h, agree3229 p q h]
theorem nonnegative3231 (p : Pattern) : 0 ≤ d3231 p :=
  nonnegative_ite (p 182) (nonnegative3230 p) (nonnegative3229 p)
def d3232 (p : Pattern) : Int := if p 246 then d39 p else d0 p
theorem agree3232 (p q : Pattern) (h : Agree support p q) : d3232 p = d3232 q := by
  simp only [d3232, h 246 (by decide), agree39 p q h, agree0 p q h]
theorem nonnegative3232 (p : Pattern) : 0 ≤ d3232 p :=
  nonnegative_ite (p 246) (nonnegative39 p) (nonnegative0 p)
def d3233 (p : Pattern) : Int := if p 225 then d3226 p else d3232 p
theorem agree3233 (p q : Pattern) (h : Agree support p q) : d3233 p = d3233 q := by
  simp only [d3233, h 225 (by decide), agree3226 p q h, agree3232 p q h]
theorem nonnegative3233 (p : Pattern) : 0 ≤ d3233 p :=
  nonnegative_ite (p 225) (nonnegative3226 p) (nonnegative3232 p)
def d3234 (p : Pattern) : Int := if p 224 then d3226 p else d3233 p
theorem agree3234 (p q : Pattern) (h : Agree support p q) : d3234 p = d3234 q := by
  simp only [d3234, h 224 (by decide), agree3226 p q h, agree3233 p q h]
theorem nonnegative3234 (p : Pattern) : 0 ≤ d3234 p :=
  nonnegative_ite (p 224) (nonnegative3226 p) (nonnegative3233 p)
def d3235 (p : Pattern) : Int := if p 204 then d3226 p else d3234 p
theorem agree3235 (p q : Pattern) (h : Agree support p q) : d3235 p = d3235 q := by
  simp only [d3235, h 204 (by decide), agree3226 p q h, agree3234 p q h]
theorem nonnegative3235 (p : Pattern) : 0 ≤ d3235 p :=
  nonnegative_ite (p 204) (nonnegative3226 p) (nonnegative3234 p)
def d3236 (p : Pattern) : Int := if p 182 then d3230 p else d3235 p
theorem agree3236 (p q : Pattern) (h : Agree support p q) : d3236 p = d3236 q := by
  simp only [d3236, h 182 (by decide), agree3230 p q h, agree3235 p q h]
theorem nonnegative3236 (p : Pattern) : 0 ≤ d3236 p :=
  nonnegative_ite (p 182) (nonnegative3230 p) (nonnegative3235 p)
def d3237 (p : Pattern) : Int := if p 163 then d3236 p else d3231 p
theorem agree3237 (p q : Pattern) (h : Agree support p q) : d3237 p = d3237 q := by
  simp only [d3237, h 163 (by decide), agree3236 p q h, agree3231 p q h]
theorem nonnegative3237 (p : Pattern) : 0 ≤ d3237 p :=
  nonnegative_ite (p 163) (nonnegative3236 p) (nonnegative3231 p)
def d3238 (p : Pattern) : Int := if p 182 then d3230 p else d3226 p
theorem agree3238 (p q : Pattern) (h : Agree support p q) : d3238 p = d3238 q := by
  simp only [d3238, h 182 (by decide), agree3230 p q h, agree3226 p q h]
theorem nonnegative3238 (p : Pattern) : 0 ≤ d3238 p :=
  nonnegative_ite (p 182) (nonnegative3230 p) (nonnegative3226 p)
def d3239 (p : Pattern) : Int := if p 246 then d12 p else d4 p
theorem agree3239 (p q : Pattern) (h : Agree support p q) : d3239 p = d3239 q := by
  simp only [d3239, h 246 (by decide), agree12 p q h, agree4 p q h]
theorem nonnegative3239 (p : Pattern) : 0 ≤ d3239 p :=
  nonnegative_ite (p 246) (nonnegative12 p) (nonnegative4 p)
end NetHack.Sokoban22Refined85
