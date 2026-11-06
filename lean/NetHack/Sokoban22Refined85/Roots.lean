/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes67
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def bonus (player : Cell) (p : Pattern) : Int :=
  if ([25, 45, 46, 47, 67, 69, 70, 89, 90, 91, 111, 113, 114, 133, 134, 135, 136, 155, 156, 157, 158, 159, 177, 180, 181, 199, 200, 201, 202, 223, 245] : List Cell).contains player then d267 p else
  if ([27, 28, 29, 30, 50, 51, 52, 73, 74, 76, 93, 94, 95, 96, 97, 98, 118, 119, 120] : List Cell).contains player then d312 p else
  if ([48] : List Cell).contains player then d481 p else
  if ([49] : List Cell).contains player then d484 p else
  if ([71] : List Cell).contains player then d488 p else
  if ([115] : List Cell).contains player then d498 p else
  if ([116] : List Cell).contains player then d516 p else
  if ([138] : List Cell).contains player then d652 p else
  if ([141] : List Cell).contains player then d709 p else
  if ([160] : List Cell).contains player then d789 p else
  if ([161] : List Cell).contains player then d948 p else
  if ([162] : List Cell).contains player then d1150 p else
  if ([163] : List Cell).contains player then d1398 p else
  if ([164, 184, 185, 186] : List Cell).contains player then d1503 p else
  if ([182] : List Cell).contains player then d1681 p else
  if ([204] : List Cell).contains player then d2183 p else
  if ([224] : List Cell).contains player then d2502 p else
  if ([225] : List Cell).contains player then d2894 p else
  if ([226, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell).contains player then d3224 p else
  if ([246] : List Cell).contains player then d3539 p else
  if ([247] : List Cell).contains player then d4036 p else
  0
theorem at25 (p : Pattern) : bonus 25 p = d267 p := rfl
theorem at27 (p : Pattern) : bonus 27 p = d312 p := rfl
theorem at28 (p : Pattern) : bonus 28 p = d312 p := rfl
theorem at29 (p : Pattern) : bonus 29 p = d312 p := rfl
theorem at30 (p : Pattern) : bonus 30 p = d312 p := rfl
theorem at45 (p : Pattern) : bonus 45 p = d267 p := rfl
theorem at46 (p : Pattern) : bonus 46 p = d267 p := rfl
theorem at47 (p : Pattern) : bonus 47 p = d267 p := rfl
theorem at48 (p : Pattern) : bonus 48 p = d481 p := rfl
theorem at49 (p : Pattern) : bonus 49 p = d484 p := rfl
theorem at50 (p : Pattern) : bonus 50 p = d312 p := rfl
theorem at51 (p : Pattern) : bonus 51 p = d312 p := rfl
theorem at52 (p : Pattern) : bonus 52 p = d312 p := rfl
theorem at67 (p : Pattern) : bonus 67 p = d267 p := rfl
theorem at69 (p : Pattern) : bonus 69 p = d267 p := rfl
theorem at70 (p : Pattern) : bonus 70 p = d267 p := rfl
theorem at71 (p : Pattern) : bonus 71 p = d488 p := rfl
theorem at73 (p : Pattern) : bonus 73 p = d312 p := rfl
theorem at74 (p : Pattern) : bonus 74 p = d312 p := rfl
theorem at76 (p : Pattern) : bonus 76 p = d312 p := rfl
theorem at78 (p : Pattern) : bonus 78 p = d0 p := rfl
theorem at79 (p : Pattern) : bonus 79 p = d0 p := rfl
theorem at80 (p : Pattern) : bonus 80 p = d0 p := rfl
theorem at81 (p : Pattern) : bonus 81 p = d0 p := rfl
theorem at82 (p : Pattern) : bonus 82 p = d0 p := rfl
theorem at83 (p : Pattern) : bonus 83 p = d0 p := rfl
theorem at84 (p : Pattern) : bonus 84 p = d0 p := rfl
theorem at89 (p : Pattern) : bonus 89 p = d267 p := rfl
theorem at90 (p : Pattern) : bonus 90 p = d267 p := rfl
theorem at91 (p : Pattern) : bonus 91 p = d267 p := rfl
theorem at93 (p : Pattern) : bonus 93 p = d312 p := rfl
theorem at94 (p : Pattern) : bonus 94 p = d312 p := rfl
theorem at95 (p : Pattern) : bonus 95 p = d312 p := rfl
theorem at96 (p : Pattern) : bonus 96 p = d312 p := rfl
theorem at97 (p : Pattern) : bonus 97 p = d312 p := rfl
theorem at98 (p : Pattern) : bonus 98 p = d312 p := rfl
theorem at100 (p : Pattern) : bonus 100 p = d0 p := rfl
theorem at101 (p : Pattern) : bonus 101 p = d0 p := rfl
theorem at102 (p : Pattern) : bonus 102 p = d0 p := rfl
theorem at103 (p : Pattern) : bonus 103 p = d0 p := rfl
theorem at104 (p : Pattern) : bonus 104 p = d0 p := rfl
theorem at105 (p : Pattern) : bonus 105 p = d0 p := rfl
theorem at106 (p : Pattern) : bonus 106 p = d0 p := rfl
theorem at111 (p : Pattern) : bonus 111 p = d267 p := rfl
theorem at113 (p : Pattern) : bonus 113 p = d267 p := rfl
theorem at114 (p : Pattern) : bonus 114 p = d267 p := rfl
theorem at115 (p : Pattern) : bonus 115 p = d498 p := rfl
theorem at116 (p : Pattern) : bonus 116 p = d516 p := rfl
theorem at118 (p : Pattern) : bonus 118 p = d312 p := rfl
theorem at119 (p : Pattern) : bonus 119 p = d312 p := rfl
theorem at120 (p : Pattern) : bonus 120 p = d312 p := rfl
theorem at122 (p : Pattern) : bonus 122 p = d0 p := rfl
theorem at123 (p : Pattern) : bonus 123 p = d0 p := rfl
theorem at124 (p : Pattern) : bonus 124 p = d0 p := rfl
theorem at125 (p : Pattern) : bonus 125 p = d0 p := rfl
theorem at126 (p : Pattern) : bonus 126 p = d0 p := rfl
theorem at127 (p : Pattern) : bonus 127 p = d0 p := rfl
theorem at128 (p : Pattern) : bonus 128 p = d0 p := rfl
theorem at133 (p : Pattern) : bonus 133 p = d267 p := rfl
theorem at134 (p : Pattern) : bonus 134 p = d267 p := rfl
theorem at135 (p : Pattern) : bonus 135 p = d267 p := rfl
theorem at136 (p : Pattern) : bonus 136 p = d267 p := rfl
theorem at138 (p : Pattern) : bonus 138 p = d652 p := rfl
theorem at141 (p : Pattern) : bonus 141 p = d709 p := rfl
theorem at144 (p : Pattern) : bonus 144 p = d0 p := rfl
theorem at145 (p : Pattern) : bonus 145 p = d0 p := rfl
theorem at146 (p : Pattern) : bonus 146 p = d0 p := rfl
theorem at147 (p : Pattern) : bonus 147 p = d0 p := rfl
theorem at148 (p : Pattern) : bonus 148 p = d0 p := rfl
theorem at149 (p : Pattern) : bonus 149 p = d0 p := rfl
theorem at150 (p : Pattern) : bonus 150 p = d0 p := rfl
theorem at155 (p : Pattern) : bonus 155 p = d267 p := rfl
theorem at156 (p : Pattern) : bonus 156 p = d267 p := rfl
theorem at157 (p : Pattern) : bonus 157 p = d267 p := rfl
theorem at158 (p : Pattern) : bonus 158 p = d267 p := rfl
theorem at159 (p : Pattern) : bonus 159 p = d267 p := rfl
theorem at160 (p : Pattern) : bonus 160 p = d789 p := rfl
theorem at161 (p : Pattern) : bonus 161 p = d948 p := rfl
theorem at162 (p : Pattern) : bonus 162 p = d1150 p := rfl
theorem at163 (p : Pattern) : bonus 163 p = d1398 p := rfl
theorem at164 (p : Pattern) : bonus 164 p = d1503 p := rfl
theorem at166 (p : Pattern) : bonus 166 p = d0 p := rfl
theorem at167 (p : Pattern) : bonus 167 p = d0 p := rfl
theorem at168 (p : Pattern) : bonus 168 p = d0 p := rfl
theorem at169 (p : Pattern) : bonus 169 p = d0 p := rfl
theorem at170 (p : Pattern) : bonus 170 p = d0 p := rfl
theorem at171 (p : Pattern) : bonus 171 p = d0 p := rfl
theorem at172 (p : Pattern) : bonus 172 p = d0 p := rfl
theorem at177 (p : Pattern) : bonus 177 p = d267 p := rfl
theorem at180 (p : Pattern) : bonus 180 p = d267 p := rfl
theorem at181 (p : Pattern) : bonus 181 p = d267 p := rfl
theorem at182 (p : Pattern) : bonus 182 p = d1681 p := rfl
theorem at184 (p : Pattern) : bonus 184 p = d1503 p := rfl
theorem at185 (p : Pattern) : bonus 185 p = d1503 p := rfl
theorem at186 (p : Pattern) : bonus 186 p = d1503 p := rfl
theorem at188 (p : Pattern) : bonus 188 p = d0 p := rfl
theorem at189 (p : Pattern) : bonus 189 p = d0 p := rfl
theorem at190 (p : Pattern) : bonus 190 p = d0 p := rfl
theorem at191 (p : Pattern) : bonus 191 p = d0 p := rfl
theorem at192 (p : Pattern) : bonus 192 p = d0 p := rfl
theorem at193 (p : Pattern) : bonus 193 p = d0 p := rfl
theorem at194 (p : Pattern) : bonus 194 p = d0 p := rfl
theorem at199 (p : Pattern) : bonus 199 p = d267 p := rfl
theorem at200 (p : Pattern) : bonus 200 p = d267 p := rfl
theorem at201 (p : Pattern) : bonus 201 p = d267 p := rfl
theorem at202 (p : Pattern) : bonus 202 p = d267 p := rfl
theorem at204 (p : Pattern) : bonus 204 p = d2183 p := rfl
theorem at210 (p : Pattern) : bonus 210 p = d0 p := rfl
theorem at211 (p : Pattern) : bonus 211 p = d0 p := rfl
theorem at212 (p : Pattern) : bonus 212 p = d0 p := rfl
theorem at213 (p : Pattern) : bonus 213 p = d0 p := rfl
theorem at214 (p : Pattern) : bonus 214 p = d0 p := rfl
theorem at215 (p : Pattern) : bonus 215 p = d0 p := rfl
theorem at216 (p : Pattern) : bonus 216 p = d0 p := rfl
theorem at218 (p : Pattern) : bonus 218 p = d0 p := rfl
theorem at223 (p : Pattern) : bonus 223 p = d267 p := rfl
theorem at224 (p : Pattern) : bonus 224 p = d2502 p := rfl
theorem at225 (p : Pattern) : bonus 225 p = d2894 p := rfl
theorem at226 (p : Pattern) : bonus 226 p = d3224 p := rfl
theorem at240 (p : Pattern) : bonus 240 p = d0 p := rfl
theorem at245 (p : Pattern) : bonus 245 p = d267 p := rfl
theorem at246 (p : Pattern) : bonus 246 p = d3539 p := rfl
theorem at247 (p : Pattern) : bonus 247 p = d4036 p := rfl
theorem at248 (p : Pattern) : bonus 248 p = d3224 p := rfl
theorem at249 (p : Pattern) : bonus 249 p = d3224 p := rfl
theorem at250 (p : Pattern) : bonus 250 p = d3224 p := rfl
theorem at251 (p : Pattern) : bonus 251 p = d3224 p := rfl
theorem at252 (p : Pattern) : bonus 252 p = d3224 p := rfl
theorem at253 (p : Pattern) : bonus 253 p = d3224 p := rfl
theorem at254 (p : Pattern) : bonus 254 p = d3224 p := rfl
theorem at255 (p : Pattern) : bonus 255 p = d3224 p := rfl
theorem at256 (p : Pattern) : bonus 256 p = d3224 p := rfl
theorem at257 (p : Pattern) : bonus 257 p = d3224 p := rfl
theorem at258 (p : Pattern) : bonus 258 p = d3224 p := rfl
theorem at259 (p : Pattern) : bonus 259 p = d3224 p := rfl
theorem at260 (p : Pattern) : bonus 260 p = d3224 p := rfl
theorem at262 (p : Pattern) : bonus 262 p = d0 p := rfl
theorem respects (player : Cell) (p q : Pattern) (h : Agree support p q) : bonus player p = bonus player q := by
  unfold bonus
  rw [agree267 p q h, agree312 p q h, agree481 p q h, agree484 p q h, agree488 p q h, agree498 p q h, agree516 p q h, agree652 p q h, agree709 p q h, agree789 p q h, agree948 p q h, agree1150 p q h, agree1398 p q h, agree1503 p q h, agree1681 p q h, agree2183 p q h, agree2502 p q h, agree2894 p q h, agree3224 p q h, agree3539 p q h, agree4036 p q h]
theorem nonnegative (player : Cell) (p : Pattern) : 0 ≤ bonus player p :=
  nonnegative_ite (([25, 45, 46, 47, 67, 69, 70, 89, 90, 91, 111, 113, 114, 133, 134, 135, 136, 155, 156, 157, 158, 159, 177, 180, 181, 199, 200, 201, 202, 223, 245] : List Cell).contains player) (nonnegative267 p) (nonnegative_ite (([27, 28, 29, 30, 50, 51, 52, 73, 74, 76, 93, 94, 95, 96, 97, 98, 118, 119, 120] : List Cell).contains player) (nonnegative312 p) (nonnegative_ite (([48] : List Cell).contains player) (nonnegative481 p) (nonnegative_ite (([49] : List Cell).contains player) (nonnegative484 p) (nonnegative_ite (([71] : List Cell).contains player) (nonnegative488 p) (nonnegative_ite (([115] : List Cell).contains player) (nonnegative498 p) (nonnegative_ite (([116] : List Cell).contains player) (nonnegative516 p) (nonnegative_ite (([138] : List Cell).contains player) (nonnegative652 p) (nonnegative_ite (([141] : List Cell).contains player) (nonnegative709 p) (nonnegative_ite (([160] : List Cell).contains player) (nonnegative789 p) (nonnegative_ite (([161] : List Cell).contains player) (nonnegative948 p) (nonnegative_ite (([162] : List Cell).contains player) (nonnegative1150 p) (nonnegative_ite (([163] : List Cell).contains player) (nonnegative1398 p) (nonnegative_ite (([164, 184, 185, 186] : List Cell).contains player) (nonnegative1503 p) (nonnegative_ite (([182] : List Cell).contains player) (nonnegative1681 p) (nonnegative_ite (([204] : List Cell).contains player) (nonnegative2183 p) (nonnegative_ite (([224] : List Cell).contains player) (nonnegative2502 p) (nonnegative_ite (([225] : List Cell).contains player) (nonnegative2894 p) (nonnegative_ite (([226, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell).contains player) (nonnegative3224 p) (nonnegative_ite (([246] : List Cell).contains player) (nonnegative3539 p) (nonnegative_ite (([247] : List Cell).contains player) (nonnegative4036 p) (nonnegative0 p)))))))))))))))))))))
end NetHack.Sokoban22Refined85
