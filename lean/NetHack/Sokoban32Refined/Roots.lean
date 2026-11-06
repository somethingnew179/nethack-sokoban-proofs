/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def bonus (player : Cell) (p : Pattern) : Int :=
  if ([28, 29, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 79, 88, 105, 108, 109, 110, 114, 131, 135, 136, 137, 157, 162, 163, 165, 166, 183, 188, 189, 192, 209, 210, 211, 212, 213, 214, 215, 216, 218, 235, 239, 241, 242, 243, 244, 245, 261, 262, 263, 265, 266, 267, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 317, 318, 320, 321] : List Cell).contains player then d134 p else
  if ([80] : List Cell).contains player then d173 p else
  if ([86] : List Cell).contains player then d176 p else
  if ([106] : List Cell).contains player then d183 p else
  if ([112] : List Cell).contains player then d227 p else
  if ([113] : List Cell).contains player then d255 p else
  if ([132] : List Cell).contains player then d292 p else
  if ([133] : List Cell).contains player then d327 p else
  if ([134] : List Cell).contains player then d388 p else
  if ([138] : List Cell).contains player then d455 p else
  if ([139] : List Cell).contains player then d537 p else
  if ([158] : List Cell).contains player then d652 p else
  if ([159] : List Cell).contains player then d696 p else
  if ([160] : List Cell).contains player then d742 p else
  if ([161] : List Cell).contains player then d825 p else
  0
theorem at28 (p : Pattern) : bonus 28 p = d134 p := rfl
theorem at29 (p : Pattern) : bonus 29 p = d134 p := rfl
theorem at42 (p : Pattern) : bonus 42 p = d0 p := rfl
theorem at43 (p : Pattern) : bonus 43 p = d0 p := rfl
theorem at44 (p : Pattern) : bonus 44 p = d0 p := rfl
theorem at45 (p : Pattern) : bonus 45 p = d0 p := rfl
theorem at46 (p : Pattern) : bonus 46 p = d0 p := rfl
theorem at47 (p : Pattern) : bonus 47 p = d0 p := rfl
theorem at48 (p : Pattern) : bonus 48 p = d0 p := rfl
theorem at49 (p : Pattern) : bonus 49 p = d0 p := rfl
theorem at50 (p : Pattern) : bonus 50 p = d0 p := rfl
theorem at53 (p : Pattern) : bonus 53 p = d134 p := rfl
theorem at54 (p : Pattern) : bonus 54 p = d134 p := rfl
theorem at55 (p : Pattern) : bonus 55 p = d134 p := rfl
theorem at56 (p : Pattern) : bonus 56 p = d134 p := rfl
theorem at57 (p : Pattern) : bonus 57 p = d134 p := rfl
theorem at58 (p : Pattern) : bonus 58 p = d134 p := rfl
theorem at59 (p : Pattern) : bonus 59 p = d134 p := rfl
theorem at60 (p : Pattern) : bonus 60 p = d134 p := rfl
theorem at61 (p : Pattern) : bonus 61 p = d134 p := rfl
theorem at62 (p : Pattern) : bonus 62 p = d134 p := rfl
theorem at68 (p : Pattern) : bonus 68 p = d0 p := rfl
theorem at69 (p : Pattern) : bonus 69 p = d0 p := rfl
theorem at70 (p : Pattern) : bonus 70 p = d0 p := rfl
theorem at71 (p : Pattern) : bonus 71 p = d0 p := rfl
theorem at72 (p : Pattern) : bonus 72 p = d0 p := rfl
theorem at73 (p : Pattern) : bonus 73 p = d0 p := rfl
theorem at74 (p : Pattern) : bonus 74 p = d0 p := rfl
theorem at75 (p : Pattern) : bonus 75 p = d0 p := rfl
theorem at76 (p : Pattern) : bonus 76 p = d0 p := rfl
theorem at79 (p : Pattern) : bonus 79 p = d134 p := rfl
theorem at80 (p : Pattern) : bonus 80 p = d173 p := rfl
theorem at86 (p : Pattern) : bonus 86 p = d176 p := rfl
theorem at88 (p : Pattern) : bonus 88 p = d134 p := rfl
theorem at94 (p : Pattern) : bonus 94 p = d0 p := rfl
theorem at95 (p : Pattern) : bonus 95 p = d0 p := rfl
theorem at96 (p : Pattern) : bonus 96 p = d0 p := rfl
theorem at97 (p : Pattern) : bonus 97 p = d0 p := rfl
theorem at98 (p : Pattern) : bonus 98 p = d0 p := rfl
theorem at99 (p : Pattern) : bonus 99 p = d0 p := rfl
theorem at100 (p : Pattern) : bonus 100 p = d0 p := rfl
theorem at101 (p : Pattern) : bonus 101 p = d0 p := rfl
theorem at102 (p : Pattern) : bonus 102 p = d0 p := rfl
theorem at105 (p : Pattern) : bonus 105 p = d134 p := rfl
theorem at106 (p : Pattern) : bonus 106 p = d183 p := rfl
theorem at108 (p : Pattern) : bonus 108 p = d134 p := rfl
theorem at109 (p : Pattern) : bonus 109 p = d134 p := rfl
theorem at110 (p : Pattern) : bonus 110 p = d134 p := rfl
theorem at112 (p : Pattern) : bonus 112 p = d227 p := rfl
theorem at113 (p : Pattern) : bonus 113 p = d255 p := rfl
theorem at114 (p : Pattern) : bonus 114 p = d134 p := rfl
theorem at120 (p : Pattern) : bonus 120 p = d0 p := rfl
theorem at121 (p : Pattern) : bonus 121 p = d0 p := rfl
theorem at122 (p : Pattern) : bonus 122 p = d0 p := rfl
theorem at123 (p : Pattern) : bonus 123 p = d0 p := rfl
theorem at124 (p : Pattern) : bonus 124 p = d0 p := rfl
theorem at125 (p : Pattern) : bonus 125 p = d0 p := rfl
theorem at126 (p : Pattern) : bonus 126 p = d0 p := rfl
theorem at127 (p : Pattern) : bonus 127 p = d0 p := rfl
theorem at128 (p : Pattern) : bonus 128 p = d0 p := rfl
theorem at131 (p : Pattern) : bonus 131 p = d134 p := rfl
theorem at132 (p : Pattern) : bonus 132 p = d292 p := rfl
theorem at133 (p : Pattern) : bonus 133 p = d327 p := rfl
theorem at134 (p : Pattern) : bonus 134 p = d388 p := rfl
theorem at135 (p : Pattern) : bonus 135 p = d134 p := rfl
theorem at136 (p : Pattern) : bonus 136 p = d134 p := rfl
theorem at137 (p : Pattern) : bonus 137 p = d134 p := rfl
theorem at138 (p : Pattern) : bonus 138 p = d455 p := rfl
theorem at139 (p : Pattern) : bonus 139 p = d537 p := rfl
theorem at146 (p : Pattern) : bonus 146 p = d0 p := rfl
theorem at147 (p : Pattern) : bonus 147 p = d0 p := rfl
theorem at148 (p : Pattern) : bonus 148 p = d0 p := rfl
theorem at149 (p : Pattern) : bonus 149 p = d0 p := rfl
theorem at150 (p : Pattern) : bonus 150 p = d0 p := rfl
theorem at151 (p : Pattern) : bonus 151 p = d0 p := rfl
theorem at152 (p : Pattern) : bonus 152 p = d0 p := rfl
theorem at153 (p : Pattern) : bonus 153 p = d0 p := rfl
theorem at154 (p : Pattern) : bonus 154 p = d0 p := rfl
theorem at157 (p : Pattern) : bonus 157 p = d134 p := rfl
theorem at158 (p : Pattern) : bonus 158 p = d652 p := rfl
theorem at159 (p : Pattern) : bonus 159 p = d696 p := rfl
theorem at160 (p : Pattern) : bonus 160 p = d742 p := rfl
theorem at161 (p : Pattern) : bonus 161 p = d825 p := rfl
theorem at162 (p : Pattern) : bonus 162 p = d134 p := rfl
theorem at163 (p : Pattern) : bonus 163 p = d134 p := rfl
theorem at165 (p : Pattern) : bonus 165 p = d134 p := rfl
theorem at166 (p : Pattern) : bonus 166 p = d134 p := rfl
theorem at172 (p : Pattern) : bonus 172 p = d0 p := rfl
theorem at173 (p : Pattern) : bonus 173 p = d0 p := rfl
theorem at174 (p : Pattern) : bonus 174 p = d0 p := rfl
theorem at175 (p : Pattern) : bonus 175 p = d0 p := rfl
theorem at176 (p : Pattern) : bonus 176 p = d0 p := rfl
theorem at177 (p : Pattern) : bonus 177 p = d0 p := rfl
theorem at178 (p : Pattern) : bonus 178 p = d0 p := rfl
theorem at179 (p : Pattern) : bonus 179 p = d0 p := rfl
theorem at180 (p : Pattern) : bonus 180 p = d0 p := rfl
theorem at183 (p : Pattern) : bonus 183 p = d134 p := rfl
theorem at188 (p : Pattern) : bonus 188 p = d134 p := rfl
theorem at189 (p : Pattern) : bonus 189 p = d134 p := rfl
theorem at192 (p : Pattern) : bonus 192 p = d134 p := rfl
theorem at198 (p : Pattern) : bonus 198 p = d0 p := rfl
theorem at199 (p : Pattern) : bonus 199 p = d0 p := rfl
theorem at200 (p : Pattern) : bonus 200 p = d0 p := rfl
theorem at201 (p : Pattern) : bonus 201 p = d0 p := rfl
theorem at202 (p : Pattern) : bonus 202 p = d0 p := rfl
theorem at203 (p : Pattern) : bonus 203 p = d0 p := rfl
theorem at204 (p : Pattern) : bonus 204 p = d0 p := rfl
theorem at205 (p : Pattern) : bonus 205 p = d0 p := rfl
theorem at206 (p : Pattern) : bonus 206 p = d0 p := rfl
theorem at209 (p : Pattern) : bonus 209 p = d134 p := rfl
theorem at210 (p : Pattern) : bonus 210 p = d134 p := rfl
theorem at211 (p : Pattern) : bonus 211 p = d134 p := rfl
theorem at212 (p : Pattern) : bonus 212 p = d134 p := rfl
theorem at213 (p : Pattern) : bonus 213 p = d134 p := rfl
theorem at214 (p : Pattern) : bonus 214 p = d134 p := rfl
theorem at215 (p : Pattern) : bonus 215 p = d134 p := rfl
theorem at216 (p : Pattern) : bonus 216 p = d134 p := rfl
theorem at218 (p : Pattern) : bonus 218 p = d134 p := rfl
theorem at224 (p : Pattern) : bonus 224 p = d0 p := rfl
theorem at225 (p : Pattern) : bonus 225 p = d0 p := rfl
theorem at226 (p : Pattern) : bonus 226 p = d0 p := rfl
theorem at227 (p : Pattern) : bonus 227 p = d0 p := rfl
theorem at228 (p : Pattern) : bonus 228 p = d0 p := rfl
theorem at229 (p : Pattern) : bonus 229 p = d0 p := rfl
theorem at230 (p : Pattern) : bonus 230 p = d0 p := rfl
theorem at231 (p : Pattern) : bonus 231 p = d0 p := rfl
theorem at232 (p : Pattern) : bonus 232 p = d0 p := rfl
theorem at235 (p : Pattern) : bonus 235 p = d134 p := rfl
theorem at239 (p : Pattern) : bonus 239 p = d134 p := rfl
theorem at241 (p : Pattern) : bonus 241 p = d134 p := rfl
theorem at242 (p : Pattern) : bonus 242 p = d134 p := rfl
theorem at243 (p : Pattern) : bonus 243 p = d134 p := rfl
theorem at244 (p : Pattern) : bonus 244 p = d134 p := rfl
theorem at245 (p : Pattern) : bonus 245 p = d134 p := rfl
theorem at261 (p : Pattern) : bonus 261 p = d134 p := rfl
theorem at262 (p : Pattern) : bonus 262 p = d134 p := rfl
theorem at263 (p : Pattern) : bonus 263 p = d134 p := rfl
theorem at265 (p : Pattern) : bonus 265 p = d134 p := rfl
theorem at266 (p : Pattern) : bonus 266 p = d134 p := rfl
theorem at267 (p : Pattern) : bonus 267 p = d134 p := rfl
theorem at269 (p : Pattern) : bonus 269 p = d134 p := rfl
theorem at270 (p : Pattern) : bonus 270 p = d134 p := rfl
theorem at271 (p : Pattern) : bonus 271 p = d134 p := rfl
theorem at272 (p : Pattern) : bonus 272 p = d134 p := rfl
theorem at273 (p : Pattern) : bonus 273 p = d134 p := rfl
theorem at274 (p : Pattern) : bonus 274 p = d134 p := rfl
theorem at275 (p : Pattern) : bonus 275 p = d134 p := rfl
theorem at276 (p : Pattern) : bonus 276 p = d134 p := rfl
theorem at277 (p : Pattern) : bonus 277 p = d134 p := rfl
theorem at278 (p : Pattern) : bonus 278 p = d134 p := rfl
theorem at279 (p : Pattern) : bonus 279 p = d134 p := rfl
theorem at280 (p : Pattern) : bonus 280 p = d134 p := rfl
theorem at281 (p : Pattern) : bonus 281 p = d134 p := rfl
theorem at282 (p : Pattern) : bonus 282 p = d134 p := rfl
theorem at283 (p : Pattern) : bonus 283 p = d134 p := rfl
theorem at284 (p : Pattern) : bonus 284 p = d134 p := rfl
theorem at287 (p : Pattern) : bonus 287 p = d134 p := rfl
theorem at288 (p : Pattern) : bonus 288 p = d134 p := rfl
theorem at289 (p : Pattern) : bonus 289 p = d134 p := rfl
theorem at290 (p : Pattern) : bonus 290 p = d134 p := rfl
theorem at291 (p : Pattern) : bonus 291 p = d134 p := rfl
theorem at292 (p : Pattern) : bonus 292 p = d134 p := rfl
theorem at293 (p : Pattern) : bonus 293 p = d134 p := rfl
theorem at294 (p : Pattern) : bonus 294 p = d134 p := rfl
theorem at295 (p : Pattern) : bonus 295 p = d134 p := rfl
theorem at317 (p : Pattern) : bonus 317 p = d134 p := rfl
theorem at318 (p : Pattern) : bonus 318 p = d134 p := rfl
theorem at320 (p : Pattern) : bonus 320 p = d134 p := rfl
theorem at321 (p : Pattern) : bonus 321 p = d134 p := rfl
theorem respects (player : Cell) (p q : Pattern) (h : Agree support p q) : bonus player p = bonus player q := by
  unfold bonus
  rw [agree134 p q h, agree173 p q h, agree176 p q h, agree183 p q h, agree227 p q h, agree255 p q h, agree292 p q h, agree327 p q h, agree388 p q h, agree455 p q h, agree537 p q h, agree652 p q h, agree696 p q h, agree742 p q h, agree825 p q h]
theorem nonnegative (player : Cell) (p : Pattern) : 0 ≤ bonus player p :=
  nonnegative_ite (([28, 29, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 79, 88, 105, 108, 109, 110, 114, 131, 135, 136, 137, 157, 162, 163, 165, 166, 183, 188, 189, 192, 209, 210, 211, 212, 213, 214, 215, 216, 218, 235, 239, 241, 242, 243, 244, 245, 261, 262, 263, 265, 266, 267, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 317, 318, 320, 321] : List Cell).contains player) (nonnegative134 p) (nonnegative_ite (([80] : List Cell).contains player) (nonnegative173 p) (nonnegative_ite (([86] : List Cell).contains player) (nonnegative176 p) (nonnegative_ite (([106] : List Cell).contains player) (nonnegative183 p) (nonnegative_ite (([112] : List Cell).contains player) (nonnegative227 p) (nonnegative_ite (([113] : List Cell).contains player) (nonnegative255 p) (nonnegative_ite (([132] : List Cell).contains player) (nonnegative292 p) (nonnegative_ite (([133] : List Cell).contains player) (nonnegative327 p) (nonnegative_ite (([134] : List Cell).contains player) (nonnegative388 p) (nonnegative_ite (([138] : List Cell).contains player) (nonnegative455 p) (nonnegative_ite (([139] : List Cell).contains player) (nonnegative537 p) (nonnegative_ite (([158] : List Cell).contains player) (nonnegative652 p) (nonnegative_ite (([159] : List Cell).contains player) (nonnegative696 p) (nonnegative_ite (([160] : List Cell).contains player) (nonnegative742 p) (nonnegative_ite (([161] : List Cell).contains player) (nonnegative825 p) (nonnegative0 p)))))))))))))))
end NetHack.Sokoban32Refined
