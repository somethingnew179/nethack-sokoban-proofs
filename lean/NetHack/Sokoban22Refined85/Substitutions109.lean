/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions108
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub13080 (p : Pattern) : d3187 (change p 10000 (some 204)) = d7214 p := by
  change (if p 161 then d3186 (change p 10000 (some 204)) else d3183 (change p 10000 (some 204))) = d7214 p
  rw [sub13079, sub13075]
  rfl
theorem sub13081 (p : Pattern) : d3188 (change p 10000 (some 204)) = d7088 p := by
  change (if p 182 then d1906 (change p 10000 (some 204)) else d3007 (change p 10000 (some 204))) = d7088 p
  rw [sub12839, sub12849]
  rfl
theorem sub13082 (p : Pattern) : d3189 (change p 10000 (some 204)) = d7088 p := by
  change (if p 163 then d3008 (change p 10000 (some 204)) else d3188 (change p 10000 (some 204))) = d7088 p
  rw [sub12850, sub13081]
  simp only [ite_self]
theorem sub13083 (p : Pattern) : d3190 (change p 10000 (some 204)) = d7215 p := by
  change (if p 162 then d3171 (change p 10000 (some 204)) else d3189 (change p 10000 (some 204))) = d7215 p
  rw [sub13059, sub13082]
  rfl
theorem sub13084 (p : Pattern) : d3191 (change p 10000 (some 204)) = d7216 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d2918 (change p 10000 (some 204))) = d7216 p
  rw [sub12617, sub12686]
  rfl
theorem sub13085 (p : Pattern) : d3192 (change p 10000 (some 204)) = d7217 p := by
  change (if p 161 then d3191 (change p 10000 (some 204)) else d3190 (change p 10000 (some 204))) = d7217 p
  rw [sub13084, sub13083]
  rfl
theorem sub13086 (p : Pattern) : d3193 (change p 10000 (some 204)) = d7218 p := by
  change (if p 160 then d3192 (change p 10000 (some 204)) else d3187 (change p 10000 (some 204))) = d7218 p
  rw [sub13085, sub13080]
  rfl
theorem sub13087 (p : Pattern) : d3194 (change p 10000 (some 204)) = d7219 p := by
  change (if p 141 then d3193 (change p 10000 (some 204)) else d3174 (change p 10000 (some 204))) = d7219 p
  rw [sub13086, sub13062]
  rfl
theorem sub13088 (p : Pattern) : d3195 (change p 10000 (some 204)) = d7220 p := by
  change (if p 163 then d3042 (change p 10000 (some 204)) else d3040 (change p 10000 (some 204))) = d7220 p
  rw [sub12903, sub12900]
  rfl
theorem sub13089 (p : Pattern) : d3196 (change p 10000 (some 204)) = d7221 p := by
  change (if p 163 then d2931 (change p 10000 (some 204)) else d3048 (change p 10000 (some 204))) = d7221 p
  rw [sub12717, sub12910]
  rfl
theorem sub13090 (p : Pattern) : d3197 (change p 10000 (some 204)) = d7222 p := by
  change (if p 162 then d3196 (change p 10000 (some 204)) else d3195 (change p 10000 (some 204))) = d7222 p
  rw [sub13089, sub13088]
  rfl
theorem sub13091 (p : Pattern) : d3198 (change p 10000 (some 204)) = d7223 p := by
  change (if p 161 then d3059 (change p 10000 (some 204)) else d3197 (change p 10000 (some 204))) = d7223 p
  rw [sub12928, sub13090]
  rfl
theorem sub13092 (p : Pattern) : d3199 (change p 10000 (some 204)) = d7224 p := by
  change (if p 160 then d3063 (change p 10000 (some 204)) else d3198 (change p 10000 (some 204))) = d7224 p
  rw [sub12932, sub13091]
  rfl
theorem sub13093 (p : Pattern) : d2158 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub13094 (p : Pattern) : d3200 (change p 10000 (some 204)) = d7101 p := by
  change (if p 182 then d2158 (change p 10000 (some 204)) else d3023 (change p 10000 (some 204))) = d7101 p
  rw [sub13093, sub12879]
  rfl
theorem sub13095 (p : Pattern) : d3201 (change p 10000 (some 204)) = d7101 p := by
  change (if p 163 then d3048 (change p 10000 (some 204)) else d3200 (change p 10000 (some 204))) = d7101 p
  rw [sub12910, sub13094]
  simp only [ite_self]
theorem sub13096 (p : Pattern) : d3202 (change p 10000 (some 204)) = d7206 p := by
  change (if p 162 then d3151 (change p 10000 (some 204)) else d3201 (change p 10000 (some 204))) = d7206 p
  rw [sub13034, sub13095]
  rfl
theorem sub13097 (p : Pattern) : d3203 (change p 10000 (some 204)) = d7207 p := by
  change (if p 161 then d3062 (change p 10000 (some 204)) else d3202 (change p 10000 (some 204))) = d7207 p
  rw [sub12931, sub13096]
  rfl
theorem sub13098 (p : Pattern) : d3204 (change p 10000 (some 204)) = d7216 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d2958 (change p 10000 (some 204))) = d7216 p
  rw [sub12617, sub12761]
  rfl
theorem sub13099 (p : Pattern) : d3205 (change p 10000 (some 204)) = d7225 p := by
  change (if p 161 then d12 (change p 10000 (some 204)) else d3204 (change p 10000 (some 204))) = d7225 p
  rw [sub12617, sub13098]
  rfl
theorem sub13100 (p : Pattern) : d3206 (change p 10000 (some 204)) = d7226 p := by
  change (if p 160 then d3205 (change p 10000 (some 204)) else d3203 (change p 10000 (some 204))) = d7226 p
  rw [sub13099, sub13097]
  rfl
theorem sub13101 (p : Pattern) : d3207 (change p 10000 (some 204)) = d7227 p := by
  change (if p 141 then d3206 (change p 10000 (some 204)) else d3199 (change p 10000 (some 204))) = d7227 p
  rw [sub13100, sub13092]
  rfl
theorem sub13102 (p : Pattern) : d3208 (change p 10000 (some 204)) = d7228 p := by
  change (if p 138 then d3207 (change p 10000 (some 204)) else d3194 (change p 10000 (some 204))) = d7228 p
  rw [sub13101, sub13087]
  rfl
theorem sub13103 (p : Pattern) : d3209 (change p 10000 (some 204)) = d7229 p := by
  change (if p 163 then d2957 (change p 10000 (some 204)) else d3048 (change p 10000 (some 204))) = d7229 p
  rw [sub12760, sub12910]
  rfl
theorem sub13104 (p : Pattern) : d3210 (change p 10000 (some 204)) = d7230 p := by
  change (if p 162 then d3209 (change p 10000 (some 204)) else d3195 (change p 10000 (some 204))) = d7230 p
  rw [sub13103, sub13088]
  rfl
theorem sub13105 (p : Pattern) : d3211 (change p 10000 (some 204)) = d7231 p := by
  change (if p 163 then d2957 (change p 10000 (some 204)) else d3043 (change p 10000 (some 204))) = d7231 p
  rw [sub12760, sub12905]
  rfl
theorem sub13106 (p : Pattern) : d3212 (change p 10000 (some 204)) = d7232 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d3211 (change p 10000 (some 204))) = d7232 p
  rw [sub12617, sub13105]
  rfl
theorem sub13107 (p : Pattern) : d3213 (change p 10000 (some 204)) = d7233 p := by
  change (if p 161 then d3212 (change p 10000 (some 204)) else d3210 (change p 10000 (some 204))) = d7233 p
  rw [sub13106, sub13104]
  rfl
theorem sub13108 (p : Pattern) : d3214 (change p 10000 (some 204)) = d7234 p := by
  change (if p 163 then d2931 (change p 10000 (some 204)) else d3050 (change p 10000 (some 204))) = d7234 p
  rw [sub12717, sub12919]
  rfl
theorem sub13109 (p : Pattern) : d3215 (change p 10000 (some 204)) = d7235 p := by
  change (if p 162 then d12 (change p 10000 (some 204)) else d3214 (change p 10000 (some 204))) = d7235 p
  rw [sub12617, sub13108]
  rfl
theorem sub13110 (p : Pattern) : d3216 (change p 10000 (some 204)) = d7236 p := by
  change (if p 161 then d12 (change p 10000 (some 204)) else d3215 (change p 10000 (some 204))) = d7236 p
  rw [sub12617, sub13109]
  rfl
theorem sub13111 (p : Pattern) : d3217 (change p 10000 (some 204)) = d7237 p := by
  change (if p 160 then d3216 (change p 10000 (some 204)) else d3213 (change p 10000 (some 204))) = d7237 p
  rw [sub13110, sub13107]
  rfl
theorem sub13112 (p : Pattern) : d3218 (change p 10000 (some 204)) = d7238 p := by
  change (if p 141 then d3206 (change p 10000 (some 204)) else d3217 (change p 10000 (some 204))) = d7238 p
  rw [sub13100, sub13111]
  rfl
theorem sub13113 (p : Pattern) : d3219 (change p 10000 (some 204)) = d7239 p := by
  change (if p 138 then d12 (change p 10000 (some 204)) else d3218 (change p 10000 (some 204))) = d7239 p
  rw [sub12617, sub13112]
  rfl
theorem sub13114 (p : Pattern) : d3220 (change p 10000 (some 204)) = d7240 p := by
  change (if p 116 then d3219 (change p 10000 (some 204)) else d3208 (change p 10000 (some 204))) = d7240 p
  rw [sub13113, sub13102]
  rfl
theorem sub13115 (p : Pattern) : d3221 (change p 10000 (some 204)) = d7241 p := by
  change (if p 115 then d3220 (change p 10000 (some 204)) else d3159 (change p 10000 (some 204))) = d7241 p
  rw [sub13114, sub13042]
  rfl
theorem sub13116 (p : Pattern) : d3222 (change p 10000 (some 204)) = d7242 p := by
  change (if p 71 then d3221 (change p 10000 (some 204)) else d2992 (change p 10000 (some 204))) = d7242 p
  rw [sub13115, sub12802]
  rfl
theorem sub13117 (p : Pattern) : d3223 (change p 10000 (some 204)) = d7243 p := by
  change (if p 49 then d3222 (change p 10000 (some 204)) else d3140 (change p 10000 (some 204))) = d7243 p
  rw [sub13116, sub13023]
  rfl
theorem sub13118 (p : Pattern) : d3224 (change p 10000 (some 204)) = d7244 p := by
  change (if p 48 then d3223 (change p 10000 (some 204)) else d3077 (change p 10000 (some 204))) = d7244 p
  rw [sub13117, sub12946]
  rfl
theorem sub13119 (p : Pattern) : d0 (change p 247 (some 246)) = d0 p := by
  rfl
theorem sub13120 (p : Pattern) : d13 (change p 247 (some 246)) = d0 p := by
  change d0 (change p 247 (some 246)) = d0 p
  exact sub13119 p
theorem sub13121 (p : Pattern) : d3540 (change p 247 (some 246)) = d0 p := by
  change d13 (change p 247 (some 246)) = d0 p
  exact sub13120 p
theorem sub13122 (p : Pattern) : d3541 (change p 247 (some 246)) = d0 p := by
  change (if p 225 then d13 (change p 247 (some 246)) else d3540 (change p 247 (some 246))) = d0 p
  rw [sub13120, sub13121]
  simp only [ite_self]
theorem sub13123 (p : Pattern) : d3542 (change p 247 (some 246)) = d0 p := by
  change (if p 224 then d13 (change p 247 (some 246)) else d3541 (change p 247 (some 246))) = d0 p
  rw [sub13120, sub13122]
  simp only [ite_self]
theorem sub13124 (p : Pattern) : d4 (change p 247 (some 246)) = d4 p := by
  rfl
theorem sub13125 (p : Pattern) : d17 (change p 247 (some 246)) = d4 p := by
  change d4 (change p 247 (some 246)) = d4 p
  exact sub13124 p
theorem sub13126 (p : Pattern) : d3543 (change p 247 (some 246)) = d4 p := by
  change d17 (change p 247 (some 246)) = d4 p
  exact sub13125 p
theorem sub13127 (p : Pattern) : d3544 (change p 247 (some 246)) = d7245 p := by
  change (if p 225 then d3543 (change p 247 (some 246)) else d13 (change p 247 (some 246))) = d7245 p
  rw [sub13126, sub13120]
  rfl
theorem sub13128 (p : Pattern) : d3545 (change p 247 (some 246)) = d7246 p := by
  change (if p 224 then d3543 (change p 247 (some 246)) else d3544 (change p 247 (some 246))) = d7246 p
  rw [sub13126, sub13127]
  rfl
theorem sub13129 (p : Pattern) : d3546 (change p 247 (some 246)) = d7247 p := by
  change (if p 204 then d3545 (change p 247 (some 246)) else d3542 (change p 247 (some 246))) = d7247 p
  rw [sub13128, sub13123]
  rfl
theorem sub13130 (p : Pattern) : d2 (change p 247 (some 246)) = d2 p := by
  rfl
theorem sub13131 (p : Pattern) : d30 (change p 247 (some 246)) = d2 p := by
  change d2 (change p 247 (some 246)) = d2 p
  exact sub13130 p
theorem sub13132 (p : Pattern) : d3547 (change p 247 (some 246)) = d2 p := by
  change d30 (change p 247 (some 246)) = d2 p
  exact sub13131 p
theorem sub13133 (p : Pattern) : d3548 (change p 247 (some 246)) = d7248 p := by
  change (if p 225 then d3547 (change p 247 (some 246)) else d13 (change p 247 (some 246))) = d7248 p
  rw [sub13132, sub13120]
  rfl
theorem sub13134 (p : Pattern) : d3549 (change p 247 (some 246)) = d7249 p := by
  change (if p 224 then d3547 (change p 247 (some 246)) else d3548 (change p 247 (some 246))) = d7249 p
  rw [sub13132, sub13133]
  rfl
theorem sub13135 (p : Pattern) : d12 (change p 247 (some 246)) = d12 p := by
  rfl
theorem sub13136 (p : Pattern) : d3550 (change p 247 (some 246)) = d7250 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3549 (change p 247 (some 246))) = d7250 p
  rw [sub13135, sub13134]
  rfl
theorem sub13137 (p : Pattern) : d3551 (change p 247 (some 246)) = d7251 p := by
  change (if p 182 then d3550 (change p 247 (some 246)) else d3546 (change p 247 (some 246))) = d7251 p
  rw [sub13136, sub13129]
  rfl
theorem sub13138 (p : Pattern) : d3552 (change p 247 (some 246)) = d7247 p := by
  change (if p 204 then d3545 (change p 247 (some 246)) else d13 (change p 247 (some 246))) = d7247 p
  rw [sub13128, sub13120]
  rfl
theorem sub13139 (p : Pattern) : d3553 (change p 247 (some 246)) = d7251 p := by
  change (if p 182 then d3550 (change p 247 (some 246)) else d3552 (change p 247 (some 246))) = d7251 p
  rw [sub13136, sub13138]
  rfl
theorem sub13140 (p : Pattern) : d3554 (change p 247 (some 246)) = d7251 p := by
  change (if p 163 then d3553 (change p 247 (some 246)) else d3551 (change p 247 (some 246))) = d7251 p
  rw [sub13139, sub13137]
  simp only [ite_self]
theorem sub13141 (p : Pattern) : d8 (change p 247 (some 246)) = d8 p := by
  rfl
theorem sub13142 (p : Pattern) : d190 (change p 247 (some 246)) = d8 p := by
  change d8 (change p 247 (some 246)) = d8 p
  exact sub13141 p
theorem sub13143 (p : Pattern) : d3555 (change p 247 (some 246)) = d8 p := by
  change d190 (change p 247 (some 246)) = d8 p
  exact sub13142 p
theorem sub13144 (p : Pattern) : d3556 (change p 247 (some 246)) = d7252 p := by
  change (if p 225 then d3555 (change p 247 (some 246)) else d17 (change p 247 (some 246))) = d7252 p
  rw [sub13143, sub13125]
  rfl
theorem sub13145 (p : Pattern) : d3557 (change p 247 (some 246)) = d7253 p := by
  change (if p 224 then d3555 (change p 247 (some 246)) else d3556 (change p 247 (some 246))) = d7253 p
  rw [sub13143, sub13144]
  rfl
theorem sub13146 (p : Pattern) : d3558 (change p 247 (some 246)) = d7254 p := by
  change (if p 204 then d3557 (change p 247 (some 246)) else d17 (change p 247 (some 246))) = d7254 p
  rw [sub13145, sub13125]
  rfl
theorem sub13147 (p : Pattern) : d6 (change p 247 (some 246)) = d6 p := by
  rfl
theorem sub13148 (p : Pattern) : d34 (change p 247 (some 246)) = d6 p := by
  change d6 (change p 247 (some 246)) = d6 p
  exact sub13147 p
theorem sub13149 (p : Pattern) : d3559 (change p 247 (some 246)) = d6 p := by
  change d34 (change p 247 (some 246)) = d6 p
  exact sub13148 p
theorem sub13150 (p : Pattern) : d3560 (change p 247 (some 246)) = d7255 p := by
  change (if p 225 then d3559 (change p 247 (some 246)) else d17 (change p 247 (some 246))) = d7255 p
  rw [sub13149, sub13125]
  rfl
theorem sub13151 (p : Pattern) : d3561 (change p 247 (some 246)) = d7256 p := by
  change (if p 224 then d3559 (change p 247 (some 246)) else d3560 (change p 247 (some 246))) = d7256 p
  rw [sub13149, sub13150]
  rfl
theorem sub13152 (p : Pattern) : d3562 (change p 247 (some 246)) = d7257 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3561 (change p 247 (some 246))) = d7257 p
  rw [sub13135, sub13151]
  rfl
theorem sub13153 (p : Pattern) : d3563 (change p 247 (some 246)) = d7258 p := by
  change (if p 182 then d3562 (change p 247 (some 246)) else d3558 (change p 247 (some 246))) = d7258 p
  rw [sub13152, sub13146]
  rfl
theorem sub13154 (p : Pattern) : d3564 (change p 247 (some 246)) = d7259 p := by
  change (if p 163 then d3563 (change p 247 (some 246)) else d3553 (change p 247 (some 246))) = d7259 p
  rw [sub13153, sub13139]
  rfl
theorem sub13155 (p : Pattern) : d3565 (change p 247 (some 246)) = d7260 p := by
  change (if p 162 then d3564 (change p 247 (some 246)) else d3554 (change p 247 (some 246))) = d7260 p
  rw [sub13154, sub13140]
  rfl
theorem sub13156 (p : Pattern) : d9 (change p 247 (some 246)) = d9 p := by
  rfl
theorem sub13157 (p : Pattern) : d23 (change p 247 (some 246)) = d9 p := by
  change d9 (change p 247 (some 246)) = d9 p
  exact sub13156 p
theorem sub13158 (p : Pattern) : d356 (change p 247 (some 246)) = d12 p := by
  change d12 (change p 247 (some 246)) = d12 p
  exact sub13135 p
theorem sub13159 (p : Pattern) : d3566 (change p 247 (some 246)) = d7261 p := by
  change (if p 225 then d356 (change p 247 (some 246)) else d23 (change p 247 (some 246))) = d7261 p
  rw [sub13158, sub13157]
  rfl
theorem sub13160 (p : Pattern) : d3567 (change p 247 (some 246)) = d7262 p := by
  change (if p 224 then d356 (change p 247 (some 246)) else d3566 (change p 247 (some 246))) = d7262 p
  rw [sub13158, sub13159]
  rfl
theorem sub13161 (p : Pattern) : d3568 (change p 247 (some 246)) = d7263 p := by
  change (if p 204 then d3567 (change p 247 (some 246)) else d23 (change p 247 (some 246))) = d7263 p
  rw [sub13160, sub13157]
  rfl
theorem sub13162 (p : Pattern) : d11 (change p 247 (some 246)) = d11 p := by
  rfl
theorem sub13163 (p : Pattern) : d39 (change p 247 (some 246)) = d11 p := by
  change d11 (change p 247 (some 246)) = d11 p
  exact sub13162 p
theorem sub13164 (p : Pattern) : d3569 (change p 247 (some 246)) = d11 p := by
  change d39 (change p 247 (some 246)) = d11 p
  exact sub13163 p
theorem sub13165 (p : Pattern) : d3570 (change p 247 (some 246)) = d7264 p := by
  change (if p 225 then d3569 (change p 247 (some 246)) else d23 (change p 247 (some 246))) = d7264 p
  rw [sub13164, sub13157]
  rfl
theorem sub13166 (p : Pattern) : d3571 (change p 247 (some 246)) = d7265 p := by
  change (if p 224 then d3569 (change p 247 (some 246)) else d3570 (change p 247 (some 246))) = d7265 p
  rw [sub13164, sub13165]
  rfl
theorem sub13167 (p : Pattern) : d3572 (change p 247 (some 246)) = d7266 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3571 (change p 247 (some 246))) = d7266 p
  rw [sub13135, sub13166]
  rfl
theorem sub13168 (p : Pattern) : d3573 (change p 247 (some 246)) = d7267 p := by
  change (if p 182 then d3572 (change p 247 (some 246)) else d3568 (change p 247 (some 246))) = d7267 p
  rw [sub13167, sub13161]
  rfl
theorem sub13169 (p : Pattern) : d3574 (change p 247 (some 246)) = d7268 p := by
  change (if p 163 then d12 (change p 247 (some 246)) else d3573 (change p 247 (some 246))) = d7268 p
  rw [sub13135, sub13168]
  rfl
theorem sub13170 (p : Pattern) : d3575 (change p 247 (some 246)) = d7269 p := by
  change (if p 162 then d3574 (change p 247 (some 246)) else d3564 (change p 247 (some 246))) = d7269 p
  rw [sub13169, sub13154]
  rfl
theorem sub13171 (p : Pattern) : d3576 (change p 247 (some 246)) = d7270 p := by
  change (if p 161 then d3575 (change p 247 (some 246)) else d3565 (change p 247 (some 246))) = d7270 p
  rw [sub13170, sub13155]
  rfl
theorem sub13172 (p : Pattern) : d3577 (change p 247 (some 246)) = d6 p := by
  change d34 (change p 247 (some 246)) = d6 p
  exact sub13148 p
theorem sub13173 (p : Pattern) : d3578 (change p 247 (some 246)) = d7271 p := by
  change (if p 225 then d3577 (change p 247 (some 246)) else d13 (change p 247 (some 246))) = d7271 p
  rw [sub13172, sub13120]
  rfl
theorem sub13174 (p : Pattern) : d3579 (change p 247 (some 246)) = d9 p := by
  change d23 (change p 247 (some 246)) = d9 p
  exact sub13157 p
theorem sub13175 (p : Pattern) : d3580 (change p 247 (some 246)) = d7272 p := by
  change (if p 225 then d3579 (change p 247 (some 246)) else d3543 (change p 247 (some 246))) = d7272 p
  rw [sub13174, sub13126]
  rfl
theorem sub13176 (p : Pattern) : d3581 (change p 247 (some 246)) = d7273 p := by
  change (if p 224 then d3580 (change p 247 (some 246)) else d3578 (change p 247 (some 246))) = d7273 p
  rw [sub13175, sub13173]
  rfl
theorem sub13177 (p : Pattern) : d3582 (change p 247 (some 246)) = d7274 p := by
  change (if p 204 then d3581 (change p 247 (some 246)) else d13 (change p 247 (some 246))) = d7274 p
  rw [sub13176, sub13120]
  rfl
theorem sub13178 (p : Pattern) : d3583 (change p 247 (some 246)) = d8 p := by
  change d190 (change p 247 (some 246)) = d8 p
  exact sub13142 p
theorem sub13179 (p : Pattern) : d3584 (change p 247 (some 246)) = d7275 p := by
  change (if p 225 then d3583 (change p 247 (some 246)) else d30 (change p 247 (some 246))) = d7275 p
  rw [sub13178, sub13131]
  rfl
theorem sub13180 (p : Pattern) : d3585 (change p 247 (some 246)) = d6 p := by
  change d34 (change p 247 (some 246)) = d6 p
  exact sub13148 p
theorem sub13181 (p : Pattern) : d1715 (change p 247 (some 246)) = d11 p := by
  change d39 (change p 247 (some 246)) = d11 p
  exact sub13163 p
theorem sub13182 (p : Pattern) : d3586 (change p 247 (some 246)) = d7276 p := by
  change (if p 225 then d1715 (change p 247 (some 246)) else d3585 (change p 247 (some 246))) = d7276 p
  rw [sub13181, sub13180]
  rfl
theorem sub13183 (p : Pattern) : d3587 (change p 247 (some 246)) = d7277 p := by
  change (if p 224 then d3586 (change p 247 (some 246)) else d3584 (change p 247 (some 246))) = d7277 p
  rw [sub13182, sub13179]
  rfl
theorem sub13184 (p : Pattern) : d3588 (change p 247 (some 246)) = d7278 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3587 (change p 247 (some 246))) = d7278 p
  rw [sub13135, sub13183]
  rfl
theorem sub13185 (p : Pattern) : d3589 (change p 247 (some 246)) = d7279 p := by
  change (if p 182 then d3588 (change p 247 (some 246)) else d3582 (change p 247 (some 246))) = d7279 p
  rw [sub13184, sub13177]
  rfl
theorem sub13186 (p : Pattern) : d364 (change p 247 (some 246)) = d12 p := by
  change d12 (change p 247 (some 246)) = d12 p
  exact sub13135 p
theorem sub13187 (p : Pattern) : d3590 (change p 247 (some 246)) = d7280 p := by
  change (if p 225 then d364 (change p 247 (some 246)) else d34 (change p 247 (some 246))) = d7280 p
  rw [sub13186, sub13148]
  rfl
theorem sub13188 (p : Pattern) : d10 (change p 247 (some 246)) = d10 p := by
  rfl
theorem sub13189 (p : Pattern) : d57 (change p 247 (some 246)) = d10 p := by
  change d10 (change p 247 (some 246)) = d10 p
  exact sub13188 p
theorem sub13190 (p : Pattern) : d3591 (change p 247 (some 246)) = d10 p := by
  change d57 (change p 247 (some 246)) = d10 p
  exact sub13189 p
theorem sub13191 (p : Pattern) : d3592 (change p 247 (some 246)) = d7281 p := by
  change (if p 225 then d364 (change p 247 (some 246)) else d3591 (change p 247 (some 246))) = d7281 p
  rw [sub13186, sub13190]
  rfl
theorem sub13192 (p : Pattern) : d3593 (change p 247 (some 246)) = d7282 p := by
  change (if p 224 then d3592 (change p 247 (some 246)) else d3590 (change p 247 (some 246))) = d7282 p
  rw [sub13191, sub13187]
  rfl
theorem sub13193 (p : Pattern) : d3594 (change p 247 (some 246)) = d7283 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3593 (change p 247 (some 246))) = d7283 p
  rw [sub13135, sub13192]
  rfl
theorem sub13194 (p : Pattern) : d3595 (change p 247 (some 246)) = d7284 p := by
  change (if p 182 then d3594 (change p 247 (some 246)) else d3582 (change p 247 (some 246))) = d7284 p
  rw [sub13193, sub13177]
  rfl
theorem sub13195 (p : Pattern) : d3596 (change p 247 (some 246)) = d7285 p := by
  change (if p 163 then d3595 (change p 247 (some 246)) else d3589 (change p 247 (some 246))) = d7285 p
  rw [sub13194, sub13185]
  rfl
theorem sub13196 (p : Pattern) : d327 (change p 247 (some 246)) = d12 p := by
  change d12 (change p 247 (some 246)) = d12 p
  exact sub13135 p
theorem sub13197 (p : Pattern) : d3597 (change p 247 (some 246)) = d7286 p := by
  change (if p 225 then d327 (change p 247 (some 246)) else d39 (change p 247 (some 246))) = d7286 p
  rw [sub13196, sub13163]
  rfl
theorem sub13198 (p : Pattern) : d3598 (change p 247 (some 246)) = d7287 p := by
  change (if p 224 then d327 (change p 247 (some 246)) else d3597 (change p 247 (some 246))) = d7287 p
  rw [sub13196, sub13197]
  rfl
theorem sub13199 (p : Pattern) : d3599 (change p 247 (some 246)) = d7288 p := by
  change (if p 204 then d12 (change p 247 (some 246)) else d3598 (change p 247 (some 246))) = d7288 p
  rw [sub13135, sub13198]
  rfl
end NetHack.Sokoban22Refined85
