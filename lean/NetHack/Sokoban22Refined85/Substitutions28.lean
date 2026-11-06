/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions27
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3360 (p : Pattern) : d83 (change p 116 none) = d83 p := by
  change (if p 163 then d12 (change p 116 none) else d78 (change p 116 none)) = d83 p
  rw [sub3283, sub3355]
  rfl
theorem sub3361 (p : Pattern) : d84 (change p 116 none) = d84 p := by
  change (if p 162 then d12 (change p 116 none) else d83 (change p 116 none)) = d84 p
  rw [sub3283, sub3360]
  rfl
theorem sub3362 (p : Pattern) : d85 (change p 116 none) = d85 p := by
  change (if p 161 then d12 (change p 116 none) else d84 (change p 116 none)) = d85 p
  rw [sub3283, sub3361]
  rfl
theorem sub3363 (p : Pattern) : d86 (change p 116 none) = d86 p := by
  change (if p 160 then d85 (change p 116 none) else d65 (change p 116 none)) = d86 p
  rw [sub3362, sub3342]
  rfl
theorem sub3364 (p : Pattern) : d87 (change p 116 none) = d87 p := by
  change (if p 141 then d86 (change p 116 none) else d82 (change p 116 none)) = d87 p
  rw [sub3363, sub3359]
  rfl
theorem sub3365 (p : Pattern) : d88 (change p 116 none) = d88 p := by
  change (if p 138 then d87 (change p 116 none) else d77 (change p 116 none)) = d88 p
  rw [sub3364, sub3354]
  rfl
theorem sub3366 (p : Pattern) : d499 (change p 116 none) = d88 p := by
  change d88 (change p 116 none) = d88 p
  exact sub3365 p
theorem sub3367 (p : Pattern) : d500 (change p 116 none) = d88 p := by
  change d88 (change p 116 none) = d88 p
  exact sub3365 p
theorem sub3368 (p : Pattern) : d501 (change p 116 none) = d88 p := by
  change (if p 115 then d500 (change p 116 none) else d499 (change p 116 none)) = d88 p
  rw [sub3367, sub3366]
  simp only [ite_self]
theorem sub3369 (p : Pattern) : d502 (change p 116 none) = d88 p := by
  change d88 (change p 116 none) = d88 p
  exact sub3365 p
theorem sub3370 (p : Pattern) : d503 (change p 116 none) = d88 p := by
  change d88 (change p 116 none) = d88 p
  exact sub3365 p
theorem sub3371 (p : Pattern) : d504 (change p 116 none) = d88 p := by
  change (if p 115 then d503 (change p 116 none) else d502 (change p 116 none)) = d88 p
  rw [sub3370, sub3369]
  simp only [ite_self]
theorem sub3372 (p : Pattern) : d505 (change p 116 none) = d88 p := by
  change (if p 71 then d504 (change p 116 none) else d501 (change p 116 none)) = d88 p
  rw [sub3371, sub3368]
  simp only [ite_self]
theorem sub3373 (p : Pattern) : d1 (change p 116 none) = d1 p := by
  rfl
theorem sub3374 (p : Pattern) : d102 (change p 116 none) = d102 p := by
  change (if p 247 then d12 (change p 116 none) else d1 (change p 116 none)) = d102 p
  rw [sub3283, sub3373]
  rfl
theorem sub3375 (p : Pattern) : d103 (change p 116 none) = d103 p := by
  change (if p 246 then d102 (change p 116 none) else d1 (change p 116 none)) = d103 p
  rw [sub3374, sub3373]
  rfl
theorem sub3376 (p : Pattern) : d104 (change p 116 none) = d104 p := by
  change (if p 204 then d12 (change p 116 none) else d103 (change p 116 none)) = d104 p
  rw [sub3283, sub3375]
  rfl
theorem sub3377 (p : Pattern) : d105 (change p 116 none) = d105 p := by
  change (if p 182 then d104 (change p 116 none) else d103 (change p 116 none)) = d105 p
  rw [sub3376, sub3375]
  rfl
theorem sub3378 (p : Pattern) : d5 (change p 116 none) = d5 p := by
  rfl
theorem sub3379 (p : Pattern) : d106 (change p 116 none) = d106 p := by
  change (if p 247 then d12 (change p 116 none) else d5 (change p 116 none)) = d106 p
  rw [sub3283, sub3378]
  rfl
theorem sub3380 (p : Pattern) : d107 (change p 116 none) = d107 p := by
  change (if p 246 then d106 (change p 116 none) else d5 (change p 116 none)) = d107 p
  rw [sub3379, sub3378]
  rfl
theorem sub3381 (p : Pattern) : d108 (change p 116 none) = d108 p := by
  change (if p 204 then d12 (change p 116 none) else d107 (change p 116 none)) = d108 p
  rw [sub3283, sub3380]
  rfl
theorem sub3382 (p : Pattern) : d109 (change p 116 none) = d109 p := by
  change (if p 182 then d108 (change p 116 none) else d107 (change p 116 none)) = d109 p
  rw [sub3381, sub3380]
  rfl
theorem sub3383 (p : Pattern) : d110 (change p 116 none) = d110 p := by
  change (if p 163 then d109 (change p 116 none) else d105 (change p 116 none)) = d110 p
  rw [sub3382, sub3377]
  rfl
theorem sub3384 (p : Pattern) : d111 (change p 116 none) = d111 p := by
  change (if p 162 then d110 (change p 116 none) else d105 (change p 116 none)) = d111 p
  rw [sub3383, sub3377]
  rfl
theorem sub3385 (p : Pattern) : d112 (change p 116 none) = d112 p := by
  change (if p 163 then d12 (change p 116 none) else d60 (change p 116 none)) = d112 p
  rw [sub3283, sub3337]
  rfl
theorem sub3386 (p : Pattern) : d113 (change p 116 none) = d113 p := by
  change (if p 162 then d112 (change p 116 none) else d110 (change p 116 none)) = d113 p
  rw [sub3385, sub3383]
  rfl
theorem sub3387 (p : Pattern) : d114 (change p 116 none) = d114 p := by
  change (if p 161 then d113 (change p 116 none) else d111 (change p 116 none)) = d114 p
  rw [sub3386, sub3384]
  rfl
theorem sub3388 (p : Pattern) : d3 (change p 116 none) = d3 p := by
  rfl
theorem sub3389 (p : Pattern) : d115 (change p 116 none) = d115 p := by
  change (if p 247 then d12 (change p 116 none) else d3 (change p 116 none)) = d115 p
  rw [sub3283, sub3388]
  rfl
theorem sub3390 (p : Pattern) : d116 (change p 116 none) = d116 p := by
  change (if p 246 then d115 (change p 116 none) else d3 (change p 116 none)) = d116 p
  rw [sub3389, sub3388]
  rfl
theorem sub3391 (p : Pattern) : d117 (change p 116 none) = d117 p := by
  change (if p 204 then d12 (change p 116 none) else d116 (change p 116 none)) = d117 p
  rw [sub3283, sub3390]
  rfl
theorem sub3392 (p : Pattern) : d118 (change p 116 none) = d118 p := by
  change (if p 182 then d117 (change p 116 none) else d103 (change p 116 none)) = d118 p
  rw [sub3391, sub3375]
  rfl
theorem sub3393 (p : Pattern) : d7 (change p 116 none) = d7 p := by
  rfl
theorem sub3394 (p : Pattern) : d119 (change p 116 none) = d119 p := by
  change (if p 247 then d12 (change p 116 none) else d7 (change p 116 none)) = d119 p
  rw [sub3283, sub3393]
  rfl
theorem sub3395 (p : Pattern) : d120 (change p 116 none) = d120 p := by
  change (if p 246 then d119 (change p 116 none) else d7 (change p 116 none)) = d120 p
  rw [sub3394, sub3393]
  rfl
theorem sub3396 (p : Pattern) : d121 (change p 116 none) = d121 p := by
  change (if p 204 then d12 (change p 116 none) else d120 (change p 116 none)) = d121 p
  rw [sub3283, sub3395]
  rfl
theorem sub3397 (p : Pattern) : d122 (change p 116 none) = d122 p := by
  change (if p 182 then d121 (change p 116 none) else d103 (change p 116 none)) = d122 p
  rw [sub3396, sub3375]
  rfl
theorem sub3398 (p : Pattern) : d123 (change p 116 none) = d123 p := by
  change (if p 163 then d122 (change p 116 none) else d118 (change p 116 none)) = d123 p
  rw [sub3397, sub3392]
  rfl
theorem sub3399 (p : Pattern) : d124 (change p 116 none) = d124 p := by
  change (if p 182 then d12 (change p 116 none) else d103 (change p 116 none)) = d124 p
  rw [sub3283, sub3375]
  rfl
theorem sub3400 (p : Pattern) : d125 (change p 116 none) = d125 p := by
  change (if p 182 then d12 (change p 116 none) else d107 (change p 116 none)) = d125 p
  rw [sub3283, sub3380]
  rfl
theorem sub3401 (p : Pattern) : d126 (change p 116 none) = d126 p := by
  change (if p 163 then d125 (change p 116 none) else d124 (change p 116 none)) = d126 p
  rw [sub3400, sub3399]
  rfl
theorem sub3402 (p : Pattern) : d127 (change p 116 none) = d127 p := by
  change (if p 162 then d126 (change p 116 none) else d123 (change p 116 none)) = d127 p
  rw [sub3401, sub3398]
  rfl
theorem sub3403 (p : Pattern) : d128 (change p 116 none) = d128 p := by
  change (if p 163 then d12 (change p 116 none) else d70 (change p 116 none)) = d128 p
  rw [sub3283, sub3347]
  rfl
theorem sub3404 (p : Pattern) : d129 (change p 116 none) = d129 p := by
  change (if p 162 then d128 (change p 116 none) else d126 (change p 116 none)) = d129 p
  rw [sub3403, sub3401]
  rfl
theorem sub3405 (p : Pattern) : d130 (change p 116 none) = d130 p := by
  change (if p 161 then d129 (change p 116 none) else d127 (change p 116 none)) = d130 p
  rw [sub3404, sub3402]
  rfl
theorem sub3406 (p : Pattern) : d131 (change p 116 none) = d131 p := by
  change (if p 160 then d130 (change p 116 none) else d114 (change p 116 none)) = d131 p
  rw [sub3405, sub3387]
  rfl
theorem sub3407 (p : Pattern) : d132 (change p 116 none) = d132 p := by
  change (if p 182 then d117 (change p 116 none) else d116 (change p 116 none)) = d132 p
  rw [sub3391, sub3390]
  rfl
theorem sub3408 (p : Pattern) : d133 (change p 116 none) = d133 p := by
  change (if p 163 then d132 (change p 116 none) else d105 (change p 116 none)) = d133 p
  rw [sub3407, sub3377]
  rfl
theorem sub3409 (p : Pattern) : d134 (change p 116 none) = d134 p := by
  change (if p 163 then d60 (change p 116 none) else d109 (change p 116 none)) = d134 p
  rw [sub3337, sub3382]
  rfl
theorem sub3410 (p : Pattern) : d135 (change p 116 none) = d135 p := by
  change (if p 162 then d134 (change p 116 none) else d133 (change p 116 none)) = d135 p
  rw [sub3409, sub3408]
  rfl
theorem sub3411 (p : Pattern) : d136 (change p 116 none) = d136 p := by
  change (if p 163 then d62 (change p 116 none) else d109 (change p 116 none)) = d136 p
  rw [sub3339, sub3382]
  rfl
theorem sub3412 (p : Pattern) : d137 (change p 116 none) = d137 p := by
  change (if p 162 then d12 (change p 116 none) else d136 (change p 116 none)) = d137 p
  rw [sub3283, sub3411]
  rfl
theorem sub3413 (p : Pattern) : d138 (change p 116 none) = d138 p := by
  change (if p 161 then d137 (change p 116 none) else d135 (change p 116 none)) = d138 p
  rw [sub3412, sub3410]
  rfl
theorem sub3414 (p : Pattern) : d139 (change p 116 none) = d139 p := by
  change (if p 182 then d12 (change p 116 none) else d116 (change p 116 none)) = d139 p
  rw [sub3283, sub3390]
  rfl
theorem sub3415 (p : Pattern) : d140 (change p 116 none) = d140 p := by
  change (if p 163 then d139 (change p 116 none) else d122 (change p 116 none)) = d140 p
  rw [sub3414, sub3397]
  rfl
theorem sub3416 (p : Pattern) : d141 (change p 116 none) = d141 p := by
  change (if p 163 then d70 (change p 116 none) else d125 (change p 116 none)) = d141 p
  rw [sub3347, sub3400]
  rfl
theorem sub3417 (p : Pattern) : d142 (change p 116 none) = d142 p := by
  change (if p 162 then d141 (change p 116 none) else d140 (change p 116 none)) = d142 p
  rw [sub3416, sub3415]
  rfl
theorem sub3418 (p : Pattern) : d143 (change p 116 none) = d143 p := by
  change (if p 163 then d72 (change p 116 none) else d125 (change p 116 none)) = d143 p
  rw [sub3349, sub3400]
  rfl
theorem sub3419 (p : Pattern) : d144 (change p 116 none) = d144 p := by
  change (if p 162 then d12 (change p 116 none) else d143 (change p 116 none)) = d144 p
  rw [sub3283, sub3418]
  rfl
theorem sub3420 (p : Pattern) : d145 (change p 116 none) = d145 p := by
  change (if p 161 then d144 (change p 116 none) else d142 (change p 116 none)) = d145 p
  rw [sub3419, sub3417]
  rfl
theorem sub3421 (p : Pattern) : d146 (change p 116 none) = d146 p := by
  change (if p 160 then d145 (change p 116 none) else d138 (change p 116 none)) = d146 p
  rw [sub3420, sub3413]
  rfl
theorem sub3422 (p : Pattern) : d147 (change p 116 none) = d147 p := by
  change (if p 141 then d146 (change p 116 none) else d131 (change p 116 none)) = d147 p
  rw [sub3421, sub3406]
  rfl
theorem sub3423 (p : Pattern) : d148 (change p 116 none) = d148 p := by
  change (if p 182 then d121 (change p 116 none) else d120 (change p 116 none)) = d148 p
  rw [sub3396, sub3395]
  rfl
theorem sub3424 (p : Pattern) : d149 (change p 116 none) = d149 p := by
  change (if p 163 then d148 (change p 116 none) else d132 (change p 116 none)) = d149 p
  rw [sub3423, sub3407]
  rfl
theorem sub3425 (p : Pattern) : d150 (change p 116 none) = d150 p := by
  change (if p 162 then d12 (change p 116 none) else d149 (change p 116 none)) = d150 p
  rw [sub3283, sub3424]
  rfl
theorem sub3426 (p : Pattern) : d151 (change p 116 none) = d151 p := by
  change (if p 161 then d12 (change p 116 none) else d150 (change p 116 none)) = d151 p
  rw [sub3283, sub3425]
  rfl
theorem sub3427 (p : Pattern) : d152 (change p 116 none) = d152 p := by
  change (if p 160 then d151 (change p 116 none) else d114 (change p 116 none)) = d152 p
  rw [sub3426, sub3387]
  rfl
theorem sub3428 (p : Pattern) : d153 (change p 116 none) = d153 p := by
  change (if p 163 then d12 (change p 116 none) else d148 (change p 116 none)) = d153 p
  rw [sub3283, sub3423]
  rfl
theorem sub3429 (p : Pattern) : d154 (change p 116 none) = d154 p := by
  change (if p 162 then d12 (change p 116 none) else d153 (change p 116 none)) = d154 p
  rw [sub3283, sub3428]
  rfl
theorem sub3430 (p : Pattern) : d155 (change p 116 none) = d155 p := by
  change (if p 161 then d12 (change p 116 none) else d154 (change p 116 none)) = d155 p
  rw [sub3283, sub3429]
  rfl
theorem sub3431 (p : Pattern) : d156 (change p 116 none) = d156 p := by
  change (if p 160 then d155 (change p 116 none) else d138 (change p 116 none)) = d156 p
  rw [sub3430, sub3413]
  rfl
theorem sub3432 (p : Pattern) : d157 (change p 116 none) = d157 p := by
  change (if p 141 then d156 (change p 116 none) else d152 (change p 116 none)) = d157 p
  rw [sub3431, sub3427]
  rfl
theorem sub3433 (p : Pattern) : d158 (change p 116 none) = d158 p := by
  change (if p 138 then d157 (change p 116 none) else d147 (change p 116 none)) = d158 p
  rw [sub3432, sub3422]
  rfl
theorem sub3434 (p : Pattern) : d506 (change p 116 none) = d158 p := by
  change d158 (change p 116 none) = d158 p
  exact sub3433 p
theorem sub3435 (p : Pattern) : d507 (change p 116 none) = d158 p := by
  change d158 (change p 116 none) = d158 p
  exact sub3433 p
theorem sub3436 (p : Pattern) : d508 (change p 116 none) = d158 p := by
  change (if p 115 then d507 (change p 116 none) else d506 (change p 116 none)) = d158 p
  rw [sub3435, sub3434]
  simp only [ite_self]
theorem sub3437 (p : Pattern) : d509 (change p 116 none) = d4197 p := by
  change (if p 71 then d508 (change p 116 none) else d501 (change p 116 none)) = d4197 p
  rw [sub3436, sub3368]
  rfl
theorem sub3438 (p : Pattern) : d510 (change p 116 none) = d4198 p := by
  change (if p 49 then d509 (change p 116 none) else d505 (change p 116 none)) = d4198 p
  rw [sub3437, sub3372]
  rfl
theorem sub3439 (p : Pattern) : d211 (change p 116 none) = d211 p := by
  change (if p 163 then d12 (change p 116 none) else d109 (change p 116 none)) = d211 p
  rw [sub3283, sub3382]
  rfl
theorem sub3440 (p : Pattern) : d212 (change p 116 none) = d212 p := by
  change (if p 162 then d211 (change p 116 none) else d133 (change p 116 none)) = d212 p
  rw [sub3439, sub3408]
  rfl
theorem sub3441 (p : Pattern) : d213 (change p 116 none) = d213 p := by
  change (if p 162 then d12 (change p 116 none) else d211 (change p 116 none)) = d213 p
  rw [sub3283, sub3439]
  rfl
theorem sub3442 (p : Pattern) : d214 (change p 116 none) = d214 p := by
  change (if p 161 then d213 (change p 116 none) else d212 (change p 116 none)) = d214 p
  rw [sub3441, sub3440]
  rfl
theorem sub3443 (p : Pattern) : d215 (change p 116 none) = d215 p := by
  change (if p 163 then d12 (change p 116 none) else d125 (change p 116 none)) = d215 p
  rw [sub3283, sub3400]
  rfl
theorem sub3444 (p : Pattern) : d216 (change p 116 none) = d216 p := by
  change (if p 162 then d215 (change p 116 none) else d140 (change p 116 none)) = d216 p
  rw [sub3443, sub3415]
  rfl
theorem sub3445 (p : Pattern) : d217 (change p 116 none) = d217 p := by
  change (if p 162 then d12 (change p 116 none) else d215 (change p 116 none)) = d217 p
  rw [sub3283, sub3443]
  rfl
theorem sub3446 (p : Pattern) : d218 (change p 116 none) = d218 p := by
  change (if p 161 then d217 (change p 116 none) else d216 (change p 116 none)) = d218 p
  rw [sub3445, sub3444]
  rfl
theorem sub3447 (p : Pattern) : d219 (change p 116 none) = d219 p := by
  change (if p 160 then d218 (change p 116 none) else d214 (change p 116 none)) = d219 p
  rw [sub3446, sub3442]
  rfl
theorem sub3448 (p : Pattern) : d220 (change p 116 none) = d220 p := by
  change (if p 141 then d219 (change p 116 none) else d131 (change p 116 none)) = d220 p
  rw [sub3447, sub3406]
  rfl
theorem sub3449 (p : Pattern) : d221 (change p 116 none) = d221 p := by
  change (if p 160 then d155 (change p 116 none) else d214 (change p 116 none)) = d221 p
  rw [sub3430, sub3442]
  rfl
theorem sub3450 (p : Pattern) : d222 (change p 116 none) = d222 p := by
  change (if p 141 then d221 (change p 116 none) else d152 (change p 116 none)) = d222 p
  rw [sub3449, sub3427]
  rfl
theorem sub3451 (p : Pattern) : d223 (change p 116 none) = d223 p := by
  change (if p 138 then d222 (change p 116 none) else d220 (change p 116 none)) = d223 p
  rw [sub3450, sub3448]
  rfl
theorem sub3452 (p : Pattern) : d511 (change p 116 none) = d223 p := by
  change d223 (change p 116 none) = d223 p
  exact sub3451 p
theorem sub3453 (p : Pattern) : d268 (change p 116 none) = d268 p := by
  change (if p 204 then d116 (change p 116 none) else d103 (change p 116 none)) = d268 p
  rw [sub3390, sub3375]
  rfl
theorem sub3454 (p : Pattern) : d269 (change p 116 none) = d269 p := by
  change (if p 182 then d117 (change p 116 none) else d268 (change p 116 none)) = d269 p
  rw [sub3391, sub3453]
  rfl
theorem sub3455 (p : Pattern) : d270 (change p 116 none) = d270 p := by
  change (if p 182 then d121 (change p 116 none) else d268 (change p 116 none)) = d270 p
  rw [sub3396, sub3453]
  rfl
theorem sub3456 (p : Pattern) : d271 (change p 116 none) = d271 p := by
  change (if p 163 then d270 (change p 116 none) else d269 (change p 116 none)) = d271 p
  rw [sub3455, sub3454]
  rfl
theorem sub3457 (p : Pattern) : d272 (change p 116 none) = d272 p := by
  change (if p 182 then d12 (change p 116 none) else d268 (change p 116 none)) = d272 p
  rw [sub3283, sub3453]
  rfl
theorem sub3458 (p : Pattern) : d273 (change p 116 none) = d273 p := by
  change (if p 204 then d120 (change p 116 none) else d107 (change p 116 none)) = d273 p
  rw [sub3395, sub3380]
  rfl
theorem sub3459 (p : Pattern) : d274 (change p 116 none) = d274 p := by
  change (if p 182 then d12 (change p 116 none) else d273 (change p 116 none)) = d274 p
  rw [sub3283, sub3458]
  rfl
theorem sub3460 (p : Pattern) : d275 (change p 116 none) = d275 p := by
  change (if p 163 then d274 (change p 116 none) else d272 (change p 116 none)) = d275 p
  rw [sub3459, sub3457]
  rfl
theorem sub3461 (p : Pattern) : d276 (change p 116 none) = d276 p := by
  change (if p 162 then d275 (change p 116 none) else d271 (change p 116 none)) = d276 p
  rw [sub3460, sub3456]
  rfl
theorem sub3462 (p : Pattern) : d277 (change p 116 none) = d277 p := by
  change (if p 182 then d12 (change p 116 none) else d59 (change p 116 none)) = d277 p
  rw [sub3283, sub3336]
  rfl
theorem sub3463 (p : Pattern) : d278 (change p 116 none) = d278 p := by
  change (if p 163 then d12 (change p 116 none) else d277 (change p 116 none)) = d278 p
  rw [sub3283, sub3462]
  rfl
theorem sub3464 (p : Pattern) : d279 (change p 116 none) = d279 p := by
  change (if p 162 then d278 (change p 116 none) else d275 (change p 116 none)) = d279 p
  rw [sub3463, sub3460]
  rfl
theorem sub3465 (p : Pattern) : d280 (change p 116 none) = d280 p := by
  change (if p 161 then d279 (change p 116 none) else d276 (change p 116 none)) = d280 p
  rw [sub3464, sub3461]
  rfl
theorem sub3466 (p : Pattern) : d281 (change p 116 none) = d281 p := by
  change (if p 160 then d280 (change p 116 none) else d114 (change p 116 none)) = d281 p
  rw [sub3465, sub3387]
  rfl
theorem sub3467 (p : Pattern) : d282 (change p 116 none) = d282 p := by
  change (if p 204 then d107 (change p 116 none) else d116 (change p 116 none)) = d282 p
  rw [sub3380, sub3390]
  rfl
theorem sub3468 (p : Pattern) : d283 (change p 116 none) = d283 p := by
  change (if p 182 then d12 (change p 116 none) else d282 (change p 116 none)) = d283 p
  rw [sub3283, sub3467]
  rfl
theorem sub3469 (p : Pattern) : d284 (change p 116 none) = d284 p := by
  change (if p 163 then d283 (change p 116 none) else d270 (change p 116 none)) = d284 p
  rw [sub3468, sub3455]
  rfl
theorem sub3470 (p : Pattern) : d285 (change p 116 none) = d285 p := by
  change (if p 163 then d12 (change p 116 none) else d274 (change p 116 none)) = d285 p
  rw [sub3283, sub3459]
  rfl
theorem sub3471 (p : Pattern) : d286 (change p 116 none) = d286 p := by
  change (if p 162 then d285 (change p 116 none) else d284 (change p 116 none)) = d286 p
  rw [sub3470, sub3469]
  rfl
theorem sub3472 (p : Pattern) : d287 (change p 116 none) = d287 p := by
  change (if p 162 then d12 (change p 116 none) else d285 (change p 116 none)) = d287 p
  rw [sub3283, sub3470]
  rfl
theorem sub3473 (p : Pattern) : d288 (change p 116 none) = d288 p := by
  change (if p 161 then d287 (change p 116 none) else d286 (change p 116 none)) = d288 p
  rw [sub3472, sub3471]
  rfl
theorem sub3474 (p : Pattern) : d289 (change p 116 none) = d289 p := by
  change (if p 160 then d288 (change p 116 none) else d214 (change p 116 none)) = d289 p
  rw [sub3473, sub3442]
  rfl
theorem sub3475 (p : Pattern) : d290 (change p 116 none) = d290 p := by
  change (if p 141 then d289 (change p 116 none) else d281 (change p 116 none)) = d290 p
  rw [sub3474, sub3466]
  rfl
theorem sub3476 (p : Pattern) : d291 (change p 116 none) = d291 p := by
  change (if p 163 then d269 (change p 116 none) else d105 (change p 116 none)) = d291 p
  rw [sub3454, sub3377]
  rfl
theorem sub3477 (p : Pattern) : d292 (change p 116 none) = d292 p := by
  change (if p 182 then d121 (change p 116 none) else d273 (change p 116 none)) = d292 p
  rw [sub3396, sub3458]
  rfl
theorem sub3478 (p : Pattern) : d293 (change p 116 none) = d293 p := by
  change (if p 163 then d292 (change p 116 none) else d269 (change p 116 none)) = d293 p
  rw [sub3477, sub3454]
  rfl
theorem sub3479 (p : Pattern) : d294 (change p 116 none) = d294 p := by
  change (if p 162 then d293 (change p 116 none) else d291 (change p 116 none)) = d294 p
  rw [sub3478, sub3476]
  rfl
end NetHack.Sokoban22Refined85
