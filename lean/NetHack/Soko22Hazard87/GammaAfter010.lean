import NetHack.Soko22Hazard87.GammaAfter009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem gammaAfter1000 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252)) = d47417 p := by
  change bonus 252 _ = _
  rw [at252]
  rfl
theorem gammaAfter1001 (p : Pattern) : bonus (HazardPattern.nextHero (.push 252 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253))) = d379469 p := by
  change bonus 252 _ = _
  rw [at252]
  change d47417 (u305 p) = d379469 p
  exact allUpdate33985 p
theorem gammaAfter1002 (p : Pattern) : bonus (HazardPattern.nextHero (.push 252 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253))) = d0 p := by
  change bonus 252 _ = _
  rw [at252]
  change d47417 (u307 p) = d0 p
  exact allUpdate33997 p
theorem gammaAfter1003 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 250)) (HazardPattern.afterPattern 10000 p (.walk 250)) = d47326 p := by
  change bonus 250 _ = _
  rw [at250]
  rfl
theorem gammaAfter1004 (p : Pattern) : bonus (HazardPattern.nextHero (.push 250 (.stay 245))) (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245))) = d0 p := by
  change bonus 250 _ = _
  rw [at250]
  change d47326 (u298 p) = d0 p
  exact allUpdate33036 p
theorem gammaAfter1005 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253)) = d47464 p := by
  change bonus 253 _ = _
  rw [at253]
  rfl
theorem gammaAfter1006 (p : Pattern) : bonus (HazardPattern.nextHero (.push 253 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254))) = d379779 p := by
  change bonus 253 _ = _
  rw [at253]
  change d47464 (u309 p) = d379779 p
  exact allUpdate34237 p
theorem gammaAfter1007 (p : Pattern) : bonus (HazardPattern.nextHero (.push 253 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254))) = d0 p := by
  change bonus 253 _ = _
  rw [at253]
  change d47464 (u311 p) = d0 p
  exact allUpdate34250 p
theorem gammaAfter1008 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 251)) (HazardPattern.afterPattern 10000 p (.walk 251)) = d47371 p := by
  change bonus 251 _ = _
  rw [at251]
  rfl
theorem gammaAfter1009 (p : Pattern) : bonus (HazardPattern.nextHero (.push 251 (.fill 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250))) = d379924 p := by
  change bonus 251 _ = _
  rw [at251]
  change d47371 (u300 p) = d379924 p
  exact allUpdate33366 p
theorem gammaAfter1010 (p : Pattern) : bonus (HazardPattern.nextHero (.push 251 (.stay 250))) (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250))) = d0 p := by
  change bonus 251 _ = _
  rw [at251]
  change d47371 (u302 p) = d0 p
  exact allUpdate33600 p
theorem gammaAfter1011 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254)) = d47512 p := by
  change bonus 254 _ = _
  rw [at254]
  rfl
theorem gammaAfter1012 (p : Pattern) : bonus (HazardPattern.nextHero (.push 254 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255))) = d380214 p := by
  change bonus 254 _ = _
  rw [at254]
  change d47512 (u313 p) = d380214 p
  exact allUpdate34392 p
theorem gammaAfter1013 (p : Pattern) : bonus (HazardPattern.nextHero (.push 254 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255))) = d0 p := by
  change bonus 254 _ = _
  rw [at254]
  change d47512 (u315 p) = d0 p
  exact allUpdate34405 p
theorem gammaAfter1014 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 252)) (HazardPattern.afterPattern 10000 p (.walk 252)) = d47417 p := by
  change bonus 252 _ = _
  rw [at252]
  rfl
theorem gammaAfter1015 (p : Pattern) : bonus (HazardPattern.nextHero (.push 252 (.fill 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251))) = d380362 p := by
  change bonus 252 _ = _
  rw [at252]
  change d47417 (u304 p) = d380362 p
  exact allUpdate33834 p
theorem gammaAfter1016 (p : Pattern) : bonus (HazardPattern.nextHero (.push 252 (.stay 251))) (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251))) = d0 p := by
  change bonus 252 _ = _
  rw [at252]
  change d47417 (u306 p) = d0 p
  exact allUpdate33991 p
theorem gammaAfter1017 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255)) = d47561 p := by
  change bonus 255 _ = _
  rw [at255]
  rfl
theorem gammaAfter1018 (p : Pattern) : bonus (HazardPattern.nextHero (.push 255 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256))) = d380658 p := by
  change bonus 255 _ = _
  rw [at255]
  change d47561 (u317 p) = d380658 p
  exact allUpdate34481 p
theorem gammaAfter1019 (p : Pattern) : bonus (HazardPattern.nextHero (.push 255 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256))) = d0 p := by
  change bonus 255 _ = _
  rw [at255]
  change d47561 (u319 p) = d0 p
  exact allUpdate34495 p
theorem gammaAfter1020 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 253)) (HazardPattern.afterPattern 10000 p (.walk 253)) = d47464 p := by
  change bonus 253 _ = _
  rw [at253]
  rfl
theorem gammaAfter1021 (p : Pattern) : bonus (HazardPattern.nextHero (.push 253 (.fill 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252))) = d380761 p := by
  change bonus 253 _ = _
  rw [at253]
  change d47464 (u308 p) = d380761 p
  exact allUpdate34148 p
theorem gammaAfter1022 (p : Pattern) : bonus (HazardPattern.nextHero (.push 253 (.stay 252))) (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252))) = d0 p := by
  change bonus 253 _ = _
  rw [at253]
  change d47464 (u310 p) = d0 p
  exact allUpdate34243 p
theorem gammaAfter1023 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256)) = d47611 p := by
  change bonus 256 _ = _
  rw [at256]
  rfl
theorem gammaAfter1024 (p : Pattern) : bonus (HazardPattern.nextHero (.push 256 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257))) = d0 p := by
  change bonus 256 _ = _
  rw [at256]
  change d47611 (u321 p) = d0 p
  exact allUpdate34527 p
theorem gammaAfter1025 (p : Pattern) : bonus (HazardPattern.nextHero (.push 256 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257))) = d0 p := by
  change bonus 256 _ = _
  rw [at256]
  change d47611 (u323 p) = d0 p
  exact allUpdate34541 p
theorem gammaAfter1026 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 254)) (HazardPattern.afterPattern 10000 p (.walk 254)) = d47512 p := by
  change bonus 254 _ = _
  rw [at254]
  rfl
theorem gammaAfter1027 (p : Pattern) : bonus (HazardPattern.nextHero (.push 254 (.fill 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253))) = d380970 p := by
  change bonus 254 _ = _
  rw [at254]
  change d47512 (u312 p) = d380970 p
  exact allUpdate34339 p
theorem gammaAfter1028 (p : Pattern) : bonus (HazardPattern.nextHero (.push 254 (.stay 253))) (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253))) = d0 p := by
  change bonus 254 _ = _
  rw [at254]
  change d47512 (u314 p) = d0 p
  exact allUpdate34398 p
theorem gammaAfter1029 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257)) = d0 p := by
  change bonus 257 _ = _
  rw [at257]
  rfl
theorem gammaAfter1030 (p : Pattern) : bonus (HazardPattern.nextHero (.push 257 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258))) = d0 p := by
  change bonus 257 _ = _
  rw [at257]
  change d0 (u325 p) = d0 p
  exact allUpdate167 p
theorem gammaAfter1031 (p : Pattern) : bonus (HazardPattern.nextHero (.push 257 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258))) = d0 p := by
  change bonus 257 _ = _
  rw [at257]
  change d0 (u327 p) = d0 p
  exact allUpdate169 p
theorem gammaAfter1032 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 255)) (HazardPattern.afterPattern 10000 p (.walk 255)) = d47561 p := by
  change bonus 255 _ = _
  rw [at255]
  rfl
theorem gammaAfter1033 (p : Pattern) : bonus (HazardPattern.nextHero (.push 255 (.fill 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254))) = d381132 p := by
  change bonus 255 _ = _
  rw [at255]
  change d47561 (u316 p) = d381132 p
  exact allUpdate34458 p
theorem gammaAfter1034 (p : Pattern) : bonus (HazardPattern.nextHero (.push 255 (.stay 254))) (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254))) = d0 p := by
  change bonus 255 _ = _
  rw [at255]
  change d47561 (u318 p) = d0 p
  exact allUpdate34488 p
theorem gammaAfter1035 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258)) = d0 p := by
  change bonus 258 _ = _
  rw [at258]
  rfl
theorem gammaAfter1036 (p : Pattern) : bonus (HazardPattern.nextHero (.push 258 (.fill 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259))) = d0 p := by
  change bonus 258 _ = _
  rw [at258]
  change d0 (u329 p) = d0 p
  exact allUpdate171 p
theorem gammaAfter1037 (p : Pattern) : bonus (HazardPattern.nextHero (.push 258 (.stay 259))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259))) = d0 p := by
  change bonus 258 _ = _
  rw [at258]
  change d0 (u331 p) = d0 p
  exact allUpdate173 p
theorem gammaAfter1038 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 256)) (HazardPattern.afterPattern 10000 p (.walk 256)) = d47611 p := by
  change bonus 256 _ = _
  rw [at256]
  rfl
theorem gammaAfter1039 (p : Pattern) : bonus (HazardPattern.nextHero (.push 256 (.fill 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255))) = d381297 p := by
  change bonus 256 _ = _
  rw [at256]
  change d47611 (u320 p) = d381297 p
  exact allUpdate34518 p
theorem gammaAfter1040 (p : Pattern) : bonus (HazardPattern.nextHero (.push 256 (.stay 255))) (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255))) = d0 p := by
  change bonus 256 _ = _
  rw [at256]
  change d47611 (u322 p) = d0 p
  exact allUpdate34534 p
theorem gammaAfter1041 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259)) = d0 p := by
  change bonus 259 _ = _
  rw [at259]
  rfl
theorem gammaAfter1042 (p : Pattern) : bonus (HazardPattern.nextHero (.push 259 (.fill 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260))) = d0 p := by
  change bonus 259 _ = _
  rw [at259]
  change d0 (u333 p) = d0 p
  exact allUpdate175 p
theorem gammaAfter1043 (p : Pattern) : bonus (HazardPattern.nextHero (.push 259 (.stay 260))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260))) = d0 p := by
  change bonus 259 _ = _
  rw [at259]
  change d0 (u335 p) = d0 p
  exact allUpdate177 p
theorem gammaAfter1044 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 257)) (HazardPattern.afterPattern 10000 p (.walk 257)) = d0 p := by
  change bonus 257 _ = _
  rw [at257]
  rfl
theorem gammaAfter1045 (p : Pattern) : bonus (HazardPattern.nextHero (.push 257 (.fill 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256))) = d0 p := by
  change bonus 257 _ = _
  rw [at257]
  change d0 (u324 p) = d0 p
  exact allUpdate166 p
theorem gammaAfter1046 (p : Pattern) : bonus (HazardPattern.nextHero (.push 257 (.stay 256))) (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256))) = d0 p := by
  change bonus 257 _ = _
  rw [at257]
  change d0 (u326 p) = d0 p
  exact allUpdate168 p
theorem gammaAfter1047 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 260)) (HazardPattern.afterPattern 10000 p (.walk 260)) = d0 p := by
  change bonus 260 _ = _
  rw [at260]
  rfl
theorem gammaAfter1048 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 258)) (HazardPattern.afterPattern 10000 p (.walk 258)) = d0 p := by
  change bonus 258 _ = _
  rw [at258]
  rfl
theorem gammaAfter1049 (p : Pattern) : bonus (HazardPattern.nextHero (.push 258 (.fill 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257))) = d0 p := by
  change bonus 258 _ = _
  rw [at258]
  change d0 (u328 p) = d0 p
  exact allUpdate170 p
theorem gammaAfter1050 (p : Pattern) : bonus (HazardPattern.nextHero (.push 258 (.stay 257))) (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257))) = d0 p := by
  change bonus 258 _ = _
  rw [at258]
  change d0 (u330 p) = d0 p
  exact allUpdate172 p
theorem gammaAfter1051 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 259)) (HazardPattern.afterPattern 10000 p (.walk 259)) = d0 p := by
  change bonus 259 _ = _
  rw [at259]
  rfl
theorem gammaAfter1052 (p : Pattern) : bonus (HazardPattern.nextHero (.push 259 (.fill 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258))) = d0 p := by
  change bonus 259 _ = _
  rw [at259]
  change d0 (u332 p) = d0 p
  exact allUpdate174 p
theorem gammaAfter1053 (p : Pattern) : bonus (HazardPattern.nextHero (.push 259 (.stay 258))) (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258))) = d0 p := by
  change bonus 259 _ = _
  rw [at259]
  change d0 (u334 p) = d0 p
  exact allUpdate176 p
theorem gammaAfter1054 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 240)) (HazardPattern.afterPattern 10000 p (.walk 240)) = d0 p := by
  change bonus 240 _ = _
  rw [at240]
  rfl
theorem gammaAfter1055 (p : Pattern) : bonus (HazardPattern.nextHero (.push 240 (.stay 218))) (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218))) = d0 p := by
  change bonus 240 _ = _
  rw [at240]
  change d0 (u276 p) = d0 p
  exact allUpdate164 p
end NetHack.Soko22Hazard87
