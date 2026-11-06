/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Nodes11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def bonus (player : Cell) (p : Pattern) : Int :=
  if ([29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 55, 56, 76, 82, 102, 108, 128, 154, 180, 206, 232, 258, 284, 310, 336] : List Cell).contains player then d75 p else
  if ([105, 106, 131, 157] : List Cell).contains player then d161 p else
  if ([115, 116, 117, 142, 143, 169] : List Cell).contains player then d195 p else
  if ([132] : List Cell).contains player then d201 p else
  if ([133] : List Cell).contains player then d219 p else
  if ([134] : List Cell).contains player then d74 p else
  if ([135, 161] : List Cell).contains player then d236 p else
  if ([140, 163, 164, 166, 167, 184, 185, 189, 190, 191, 194, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 236, 237, 238, 239, 241, 242, 244, 245, 246, 262, 263, 264, 265, 270, 272, 288, 289, 290, 291, 292, 293, 294, 296, 297, 317, 318, 319, 320, 322, 345, 348, 370, 371, 372, 373, 374, 396, 397, 399, 400] : List Cell).contains player then d258 p else
  if ([141] : List Cell).contains player then d309 p else
  if ([158] : List Cell).contains player then d319 p else
  if ([159] : List Cell).contains player then d356 p else
  if ([160] : List Cell).contains player then d374 p else
  if ([168] : List Cell).contains player then d430 p else
  if ([186] : List Cell).contains player then d485 p else
  if ([187] : List Cell).contains player then d524 p else
  if ([192] : List Cell).contains player then d586 p else
  if ([193] : List Cell).contains player then d658 p else
  if ([271] : List Cell).contains player then d733 p else
  0
theorem at29 (p : Pattern) : bonus 29 p = d75 p := rfl
theorem at30 (p : Pattern) : bonus 30 p = d75 p := rfl
theorem at31 (p : Pattern) : bonus 31 p = d75 p := rfl
theorem at32 (p : Pattern) : bonus 32 p = d75 p := rfl
theorem at33 (p : Pattern) : bonus 33 p = d75 p := rfl
theorem at34 (p : Pattern) : bonus 34 p = d75 p := rfl
theorem at35 (p : Pattern) : bonus 35 p = d75 p := rfl
theorem at36 (p : Pattern) : bonus 36 p = d75 p := rfl
theorem at37 (p : Pattern) : bonus 37 p = d75 p := rfl
theorem at38 (p : Pattern) : bonus 38 p = d75 p := rfl
theorem at39 (p : Pattern) : bonus 39 p = d75 p := rfl
theorem at40 (p : Pattern) : bonus 40 p = d75 p := rfl
theorem at41 (p : Pattern) : bonus 41 p = d75 p := rfl
theorem at42 (p : Pattern) : bonus 42 p = d75 p := rfl
theorem at43 (p : Pattern) : bonus 43 p = d75 p := rfl
theorem at44 (p : Pattern) : bonus 44 p = d75 p := rfl
theorem at45 (p : Pattern) : bonus 45 p = d75 p := rfl
theorem at46 (p : Pattern) : bonus 46 p = d75 p := rfl
theorem at47 (p : Pattern) : bonus 47 p = d75 p := rfl
theorem at48 (p : Pattern) : bonus 48 p = d75 p := rfl
theorem at49 (p : Pattern) : bonus 49 p = d75 p := rfl
theorem at50 (p : Pattern) : bonus 50 p = d75 p := rfl
theorem at55 (p : Pattern) : bonus 55 p = d75 p := rfl
theorem at56 (p : Pattern) : bonus 56 p = d75 p := rfl
theorem at76 (p : Pattern) : bonus 76 p = d75 p := rfl
theorem at82 (p : Pattern) : bonus 82 p = d75 p := rfl
theorem at102 (p : Pattern) : bonus 102 p = d75 p := rfl
theorem at105 (p : Pattern) : bonus 105 p = d161 p := rfl
theorem at106 (p : Pattern) : bonus 106 p = d161 p := rfl
theorem at108 (p : Pattern) : bonus 108 p = d75 p := rfl
theorem at115 (p : Pattern) : bonus 115 p = d195 p := rfl
theorem at116 (p : Pattern) : bonus 116 p = d195 p := rfl
theorem at117 (p : Pattern) : bonus 117 p = d195 p := rfl
theorem at128 (p : Pattern) : bonus 128 p = d75 p := rfl
theorem at131 (p : Pattern) : bonus 131 p = d161 p := rfl
theorem at132 (p : Pattern) : bonus 132 p = d201 p := rfl
theorem at133 (p : Pattern) : bonus 133 p = d219 p := rfl
theorem at134 (p : Pattern) : bonus 134 p = d74 p := rfl
theorem at135 (p : Pattern) : bonus 135 p = d236 p := rfl
theorem at140 (p : Pattern) : bonus 140 p = d258 p := rfl
theorem at141 (p : Pattern) : bonus 141 p = d309 p := rfl
theorem at142 (p : Pattern) : bonus 142 p = d195 p := rfl
theorem at143 (p : Pattern) : bonus 143 p = d195 p := rfl
theorem at154 (p : Pattern) : bonus 154 p = d75 p := rfl
theorem at157 (p : Pattern) : bonus 157 p = d161 p := rfl
theorem at158 (p : Pattern) : bonus 158 p = d319 p := rfl
theorem at159 (p : Pattern) : bonus 159 p = d356 p := rfl
theorem at160 (p : Pattern) : bonus 160 p = d374 p := rfl
theorem at161 (p : Pattern) : bonus 161 p = d236 p := rfl
theorem at163 (p : Pattern) : bonus 163 p = d258 p := rfl
theorem at164 (p : Pattern) : bonus 164 p = d258 p := rfl
theorem at166 (p : Pattern) : bonus 166 p = d258 p := rfl
theorem at167 (p : Pattern) : bonus 167 p = d258 p := rfl
theorem at168 (p : Pattern) : bonus 168 p = d430 p := rfl
theorem at169 (p : Pattern) : bonus 169 p = d195 p := rfl
theorem at180 (p : Pattern) : bonus 180 p = d75 p := rfl
theorem at184 (p : Pattern) : bonus 184 p = d258 p := rfl
theorem at185 (p : Pattern) : bonus 185 p = d258 p := rfl
theorem at186 (p : Pattern) : bonus 186 p = d485 p := rfl
theorem at187 (p : Pattern) : bonus 187 p = d524 p := rfl
theorem at189 (p : Pattern) : bonus 189 p = d258 p := rfl
theorem at190 (p : Pattern) : bonus 190 p = d258 p := rfl
theorem at191 (p : Pattern) : bonus 191 p = d258 p := rfl
theorem at192 (p : Pattern) : bonus 192 p = d586 p := rfl
theorem at193 (p : Pattern) : bonus 193 p = d658 p := rfl
theorem at194 (p : Pattern) : bonus 194 p = d258 p := rfl
theorem at206 (p : Pattern) : bonus 206 p = d75 p := rfl
theorem at210 (p : Pattern) : bonus 210 p = d258 p := rfl
theorem at211 (p : Pattern) : bonus 211 p = d258 p := rfl
theorem at212 (p : Pattern) : bonus 212 p = d258 p := rfl
theorem at213 (p : Pattern) : bonus 213 p = d258 p := rfl
theorem at214 (p : Pattern) : bonus 214 p = d258 p := rfl
theorem at215 (p : Pattern) : bonus 215 p = d258 p := rfl
theorem at216 (p : Pattern) : bonus 216 p = d258 p := rfl
theorem at218 (p : Pattern) : bonus 218 p = d258 p := rfl
theorem at219 (p : Pattern) : bonus 219 p = d258 p := rfl
theorem at220 (p : Pattern) : bonus 220 p = d258 p := rfl
theorem at232 (p : Pattern) : bonus 232 p = d75 p := rfl
theorem at236 (p : Pattern) : bonus 236 p = d258 p := rfl
theorem at237 (p : Pattern) : bonus 237 p = d258 p := rfl
theorem at238 (p : Pattern) : bonus 238 p = d258 p := rfl
theorem at239 (p : Pattern) : bonus 239 p = d258 p := rfl
theorem at241 (p : Pattern) : bonus 241 p = d258 p := rfl
theorem at242 (p : Pattern) : bonus 242 p = d258 p := rfl
theorem at244 (p : Pattern) : bonus 244 p = d258 p := rfl
theorem at245 (p : Pattern) : bonus 245 p = d258 p := rfl
theorem at246 (p : Pattern) : bonus 246 p = d258 p := rfl
theorem at252 (p : Pattern) : bonus 252 p = d0 p := rfl
theorem at253 (p : Pattern) : bonus 253 p = d0 p := rfl
theorem at254 (p : Pattern) : bonus 254 p = d0 p := rfl
theorem at255 (p : Pattern) : bonus 255 p = d0 p := rfl
theorem at256 (p : Pattern) : bonus 256 p = d0 p := rfl
theorem at258 (p : Pattern) : bonus 258 p = d75 p := rfl
theorem at262 (p : Pattern) : bonus 262 p = d258 p := rfl
theorem at263 (p : Pattern) : bonus 263 p = d258 p := rfl
theorem at264 (p : Pattern) : bonus 264 p = d258 p := rfl
theorem at265 (p : Pattern) : bonus 265 p = d258 p := rfl
theorem at270 (p : Pattern) : bonus 270 p = d258 p := rfl
theorem at271 (p : Pattern) : bonus 271 p = d733 p := rfl
theorem at272 (p : Pattern) : bonus 272 p = d258 p := rfl
theorem at276 (p : Pattern) : bonus 276 p = d0 p := rfl
theorem at278 (p : Pattern) : bonus 278 p = d0 p := rfl
theorem at279 (p : Pattern) : bonus 279 p = d0 p := rfl
theorem at280 (p : Pattern) : bonus 280 p = d0 p := rfl
theorem at281 (p : Pattern) : bonus 281 p = d0 p := rfl
theorem at282 (p : Pattern) : bonus 282 p = d0 p := rfl
theorem at284 (p : Pattern) : bonus 284 p = d75 p := rfl
theorem at288 (p : Pattern) : bonus 288 p = d258 p := rfl
theorem at289 (p : Pattern) : bonus 289 p = d258 p := rfl
theorem at290 (p : Pattern) : bonus 290 p = d258 p := rfl
theorem at291 (p : Pattern) : bonus 291 p = d258 p := rfl
theorem at292 (p : Pattern) : bonus 292 p = d258 p := rfl
theorem at293 (p : Pattern) : bonus 293 p = d258 p := rfl
theorem at294 (p : Pattern) : bonus 294 p = d258 p := rfl
theorem at296 (p : Pattern) : bonus 296 p = d258 p := rfl
theorem at297 (p : Pattern) : bonus 297 p = d258 p := rfl
theorem at304 (p : Pattern) : bonus 304 p = d0 p := rfl
theorem at305 (p : Pattern) : bonus 305 p = d0 p := rfl
theorem at306 (p : Pattern) : bonus 306 p = d0 p := rfl
theorem at307 (p : Pattern) : bonus 307 p = d0 p := rfl
theorem at308 (p : Pattern) : bonus 308 p = d0 p := rfl
theorem at310 (p : Pattern) : bonus 310 p = d75 p := rfl
theorem at317 (p : Pattern) : bonus 317 p = d258 p := rfl
theorem at318 (p : Pattern) : bonus 318 p = d258 p := rfl
theorem at319 (p : Pattern) : bonus 319 p = d258 p := rfl
theorem at320 (p : Pattern) : bonus 320 p = d258 p := rfl
theorem at322 (p : Pattern) : bonus 322 p = d258 p := rfl
theorem at328 (p : Pattern) : bonus 328 p = d0 p := rfl
theorem at330 (p : Pattern) : bonus 330 p = d0 p := rfl
theorem at331 (p : Pattern) : bonus 331 p = d0 p := rfl
theorem at332 (p : Pattern) : bonus 332 p = d0 p := rfl
theorem at333 (p : Pattern) : bonus 333 p = d0 p := rfl
theorem at334 (p : Pattern) : bonus 334 p = d0 p := rfl
theorem at336 (p : Pattern) : bonus 336 p = d75 p := rfl
theorem at345 (p : Pattern) : bonus 345 p = d258 p := rfl
theorem at348 (p : Pattern) : bonus 348 p = d258 p := rfl
theorem at356 (p : Pattern) : bonus 356 p = d0 p := rfl
theorem at357 (p : Pattern) : bonus 357 p = d0 p := rfl
theorem at358 (p : Pattern) : bonus 358 p = d0 p := rfl
theorem at359 (p : Pattern) : bonus 359 p = d0 p := rfl
theorem at360 (p : Pattern) : bonus 360 p = d0 p := rfl
theorem at370 (p : Pattern) : bonus 370 p = d258 p := rfl
theorem at371 (p : Pattern) : bonus 371 p = d258 p := rfl
theorem at372 (p : Pattern) : bonus 372 p = d258 p := rfl
theorem at373 (p : Pattern) : bonus 373 p = d258 p := rfl
theorem at374 (p : Pattern) : bonus 374 p = d258 p := rfl
theorem at380 (p : Pattern) : bonus 380 p = d0 p := rfl
theorem at382 (p : Pattern) : bonus 382 p = d0 p := rfl
theorem at383 (p : Pattern) : bonus 383 p = d0 p := rfl
theorem at384 (p : Pattern) : bonus 384 p = d0 p := rfl
theorem at385 (p : Pattern) : bonus 385 p = d0 p := rfl
theorem at386 (p : Pattern) : bonus 386 p = d0 p := rfl
theorem at396 (p : Pattern) : bonus 396 p = d258 p := rfl
theorem at397 (p : Pattern) : bonus 397 p = d258 p := rfl
theorem at399 (p : Pattern) : bonus 399 p = d258 p := rfl
theorem at400 (p : Pattern) : bonus 400 p = d258 p := rfl
theorem at408 (p : Pattern) : bonus 408 p = d0 p := rfl
theorem at409 (p : Pattern) : bonus 409 p = d0 p := rfl
theorem at410 (p : Pattern) : bonus 410 p = d0 p := rfl
theorem at411 (p : Pattern) : bonus 411 p = d0 p := rfl
theorem at412 (p : Pattern) : bonus 412 p = d0 p := rfl
theorem respects (player : Cell) (p q : Pattern) (h : Agree support p q) : bonus player p = bonus player q := by
  unfold bonus
  rw [agree75 p q h, agree161 p q h, agree195 p q h, agree201 p q h, agree219 p q h, agree74 p q h, agree236 p q h, agree258 p q h, agree309 p q h, agree319 p q h, agree356 p q h, agree374 p q h, agree430 p q h, agree485 p q h, agree524 p q h, agree586 p q h, agree658 p q h, agree733 p q h]
theorem nonnegative (player : Cell) (p : Pattern) : 0 ≤ bonus player p :=
  nonnegative_ite (([29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 55, 56, 76, 82, 102, 108, 128, 154, 180, 206, 232, 258, 284, 310, 336] : List Cell).contains player) (nonnegative75 p) (nonnegative_ite (([105, 106, 131, 157] : List Cell).contains player) (nonnegative161 p) (nonnegative_ite (([115, 116, 117, 142, 143, 169] : List Cell).contains player) (nonnegative195 p) (nonnegative_ite (([132] : List Cell).contains player) (nonnegative201 p) (nonnegative_ite (([133] : List Cell).contains player) (nonnegative219 p) (nonnegative_ite (([134] : List Cell).contains player) (nonnegative74 p) (nonnegative_ite (([135, 161] : List Cell).contains player) (nonnegative236 p) (nonnegative_ite (([140, 163, 164, 166, 167, 184, 185, 189, 190, 191, 194, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 236, 237, 238, 239, 241, 242, 244, 245, 246, 262, 263, 264, 265, 270, 272, 288, 289, 290, 291, 292, 293, 294, 296, 297, 317, 318, 319, 320, 322, 345, 348, 370, 371, 372, 373, 374, 396, 397, 399, 400] : List Cell).contains player) (nonnegative258 p) (nonnegative_ite (([141] : List Cell).contains player) (nonnegative309 p) (nonnegative_ite (([158] : List Cell).contains player) (nonnegative319 p) (nonnegative_ite (([159] : List Cell).contains player) (nonnegative356 p) (nonnegative_ite (([160] : List Cell).contains player) (nonnegative374 p) (nonnegative_ite (([168] : List Cell).contains player) (nonnegative430 p) (nonnegative_ite (([186] : List Cell).contains player) (nonnegative485 p) (nonnegative_ite (([187] : List Cell).contains player) (nonnegative524 p) (nonnegative_ite (([192] : List Cell).contains player) (nonnegative586 p) (nonnegative_ite (([193] : List Cell).contains player) (nonnegative658 p) (nonnegative_ite (([271] : List Cell).contains player) (nonnegative733 p) (nonnegative0 p))))))))))))))))))
end NetHack.Sokoban12CostPartition
