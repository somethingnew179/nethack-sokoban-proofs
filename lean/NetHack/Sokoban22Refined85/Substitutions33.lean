/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions32
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3960 (p : Pattern) : d1356 (change p 163 none) = d4367 p := by
  change (if p 115 then d1355 (change p 163 none) else d1259 (change p 163 none)) = d4367 p
  rw [sub3959, sub3833]
  rfl
theorem sub3961 (p : Pattern) : d1357 (change p 163 none) = d4368 p := by
  change (if p 71 then d1356 (change p 163 none) else d1236 (change p 163 none)) = d4368 p
  rw [sub3960, sub3810]
  rfl
theorem sub3962 (p : Pattern) : d1358 (change p 163 none) = d4339 p := by
  change (if p 162 then d1289 (change p 163 none) else d1283 (change p 163 none)) = d4339 p
  rw [sub3883, sub3876]
  rfl
theorem sub3963 (p : Pattern) : d1359 (change p 163 none) = d4340 p := by
  change (if p 161 then d1300 (change p 163 none) else d1358 (change p 163 none)) = d4340 p
  rw [sub3895, sub3962]
  rfl
theorem sub3964 (p : Pattern) : d1360 (change p 163 none) = d4344 p := by
  change (if p 160 then d1293 (change p 163 none) else d1359 (change p 163 none)) = d4344 p
  rw [sub3888, sub3963]
  rfl
theorem sub3965 (p : Pattern) : d1361 (change p 163 none) = d4345 p := by
  change (if p 141 then d1360 (change p 163 none) else d1282 (change p 163 none)) = d4345 p
  rw [sub3964, sub3875]
  rfl
theorem sub3966 (p : Pattern) : d1362 (change p 163 none) = d4348 p := by
  change (if p 141 then d1334 (change p 163 none) else d1302 (change p 163 none)) = d4348 p
  rw [sub3933, sub3897]
  rfl
theorem sub3967 (p : Pattern) : d1363 (change p 163 none) = d4349 p := by
  change (if p 138 then d1362 (change p 163 none) else d1361 (change p 163 none)) = d4349 p
  rw [sub3966, sub3965]
  rfl
theorem sub3968 (p : Pattern) : d1364 (change p 163 none) = d4348 p := by
  change (if p 141 then d1334 (change p 163 none) else d1311 (change p 163 none)) = d4348 p
  rw [sub3933, sub3906]
  rfl
theorem sub3969 (p : Pattern) : d1365 (change p 163 none) = d4354 p := by
  change (if p 138 then d162 (change p 163 none) else d1364 (change p 163 none)) = d4354 p
  rw [sub3915, sub3968]
  rfl
theorem sub3970 (p : Pattern) : d1366 (change p 163 none) = d4355 p := by
  change (if p 116 then d1365 (change p 163 none) else d1363 (change p 163 none)) = d4355 p
  rw [sub3969, sub3967]
  rfl
theorem sub3971 (p : Pattern) : d1367 (change p 163 none) = d105 p := by
  change (if p 162 then d1296 (change p 163 none) else d1319 (change p 163 none)) = d105 p
  rw [sub3891, sub3918]
  simp only [ite_self]
theorem sub3972 (p : Pattern) : d1368 (change p 163 none) = d4334 p := by
  change (if p 161 then d1298 (change p 163 none) else d1367 (change p 163 none)) = d4334 p
  rw [sub3893, sub3971]
  rfl
theorem sub3973 (p : Pattern) : d268 (change p 163 none) = d268 p := by
  change (if p 204 then d116 (change p 163 none) else d103 (change p 163 none)) = d268 p
  rw [sub3864, sub3847]
  rfl
theorem sub3974 (p : Pattern) : d269 (change p 163 none) = d269 p := by
  change (if p 182 then d117 (change p 163 none) else d268 (change p 163 none)) = d269 p
  rw [sub3865, sub3973]
  rfl
theorem sub3975 (p : Pattern) : d1369 (change p 163 none) = d269 p := by
  change d269 (change p 163 none) = d269 p
  exact sub3974 p
theorem sub3976 (p : Pattern) : d272 (change p 163 none) = d272 p := by
  change (if p 182 then d12 (change p 163 none) else d268 (change p 163 none)) = d272 p
  rw [sub3692, sub3973]
  rfl
theorem sub3977 (p : Pattern) : d1370 (change p 163 none) = d272 p := by
  change d272 (change p 163 none) = d272 p
  exact sub3976 p
theorem sub3978 (p : Pattern) : d1371 (change p 163 none) = d4369 p := by
  change (if p 162 then d1370 (change p 163 none) else d1369 (change p 163 none)) = d4369 p
  rw [sub3977, sub3975]
  rfl
theorem sub3979 (p : Pattern) : d277 (change p 163 none) = d277 p := by
  change (if p 182 then d12 (change p 163 none) else d59 (change p 163 none)) = d277 p
  rw [sub3692, sub3857]
  rfl
theorem sub3980 (p : Pattern) : d278 (change p 163 none) = d277 p := by
  change d277 (change p 163 none) = d277 p
  exact sub3979 p
theorem sub3981 (p : Pattern) : d1372 (change p 163 none) = d4370 p := by
  change (if p 162 then d278 (change p 163 none) else d1370 (change p 163 none)) = d4370 p
  rw [sub3980, sub3977]
  rfl
theorem sub3982 (p : Pattern) : d1373 (change p 163 none) = d4371 p := by
  change (if p 161 then d1372 (change p 163 none) else d1371 (change p 163 none)) = d4371 p
  rw [sub3981, sub3978]
  rfl
theorem sub3983 (p : Pattern) : d1374 (change p 163 none) = d4372 p := by
  change (if p 160 then d1373 (change p 163 none) else d1368 (change p 163 none)) = d4372 p
  rw [sub3982, sub3972]
  rfl
theorem sub3984 (p : Pattern) : d5 (change p 163 none) = d5 p := by
  rfl
theorem sub3985 (p : Pattern) : d106 (change p 163 none) = d106 p := by
  change (if p 247 then d12 (change p 163 none) else d5 (change p 163 none)) = d106 p
  rw [sub3692, sub3984]
  rfl
theorem sub3986 (p : Pattern) : d107 (change p 163 none) = d107 p := by
  change (if p 246 then d106 (change p 163 none) else d5 (change p 163 none)) = d107 p
  rw [sub3985, sub3984]
  rfl
theorem sub3987 (p : Pattern) : d282 (change p 163 none) = d282 p := by
  change (if p 204 then d107 (change p 163 none) else d116 (change p 163 none)) = d282 p
  rw [sub3986, sub3864]
  rfl
theorem sub3988 (p : Pattern) : d283 (change p 163 none) = d283 p := by
  change (if p 182 then d12 (change p 163 none) else d282 (change p 163 none)) = d283 p
  rw [sub3692, sub3987]
  rfl
theorem sub3989 (p : Pattern) : d1375 (change p 163 none) = d283 p := by
  change d283 (change p 163 none) = d283 p
  exact sub3988 p
theorem sub3990 (p : Pattern) : d1376 (change p 163 none) = d4373 p := by
  change (if p 162 then d1375 (change p 163 none) else d1289 (change p 163 none)) = d4373 p
  rw [sub3989, sub3883]
  rfl
theorem sub3991 (p : Pattern) : d1377 (change p 163 none) = d4374 p := by
  change (if p 162 then d12 (change p 163 none) else d1375 (change p 163 none)) = d4374 p
  rw [sub3692, sub3989]
  rfl
theorem sub3992 (p : Pattern) : d1378 (change p 163 none) = d4375 p := by
  change (if p 161 then d1377 (change p 163 none) else d1376 (change p 163 none)) = d4375 p
  rw [sub3991, sub3990]
  rfl
theorem sub3993 (p : Pattern) : d1379 (change p 163 none) = d4376 p := by
  change (if p 160 then d1378 (change p 163 none) else d1333 (change p 163 none)) = d4376 p
  rw [sub3992, sub3932]
  rfl
theorem sub3994 (p : Pattern) : d1380 (change p 163 none) = d4377 p := by
  change (if p 141 then d1379 (change p 163 none) else d1374 (change p 163 none)) = d4377 p
  rw [sub3993, sub3983]
  rfl
theorem sub3995 (p : Pattern) : d1381 (change p 163 none) = d4378 p := by
  change (if p 162 then d1369 (change p 163 none) else d1296 (change p 163 none)) = d4378 p
  rw [sub3975, sub3891]
  rfl
theorem sub3996 (p : Pattern) : d1382 (change p 163 none) = d4379 p := by
  change (if p 162 then d278 (change p 163 none) else d1369 (change p 163 none)) = d4379 p
  rw [sub3980, sub3975]
  rfl
theorem sub3997 (p : Pattern) : d1383 (change p 163 none) = d4380 p := by
  change (if p 161 then d1382 (change p 163 none) else d1381 (change p 163 none)) = d4380 p
  rw [sub3996, sub3995]
  rfl
theorem sub3998 (p : Pattern) : d1384 (change p 163 none) = d4381 p := by
  change (if p 160 then d1301 (change p 163 none) else d1383 (change p 163 none)) = d4381 p
  rw [sub3896, sub3997]
  rfl
theorem sub3999 (p : Pattern) : d108 (change p 163 none) = d108 p := by
  change (if p 204 then d12 (change p 163 none) else d107 (change p 163 none)) = d108 p
  rw [sub3692, sub3986]
  rfl
theorem sub4000 (p : Pattern) : d298 (change p 163 none) = d298 p := by
  change (if p 182 then d108 (change p 163 none) else d282 (change p 163 none)) = d298 p
  rw [sub3999, sub3987]
  rfl
theorem sub4001 (p : Pattern) : d1385 (change p 163 none) = d298 p := by
  change d298 (change p 163 none) = d298 p
  exact sub4000 p
theorem sub4002 (p : Pattern) : d1386 (change p 163 none) = d4382 p := by
  change (if p 162 then d1385 (change p 163 none) else d1289 (change p 163 none)) = d4382 p
  rw [sub4001, sub3883]
  rfl
theorem sub4003 (p : Pattern) : d1387 (change p 163 none) = d4383 p := by
  change (if p 162 then d12 (change p 163 none) else d1385 (change p 163 none)) = d4383 p
  rw [sub3692, sub4001]
  rfl
theorem sub4004 (p : Pattern) : d1388 (change p 163 none) = d4384 p := by
  change (if p 161 then d1387 (change p 163 none) else d1386 (change p 163 none)) = d4384 p
  rw [sub4003, sub4002]
  rfl
theorem sub4005 (p : Pattern) : d109 (change p 163 none) = d109 p := by
  change (if p 182 then d108 (change p 163 none) else d107 (change p 163 none)) = d109 p
  rw [sub3999, sub3986]
  rfl
theorem sub4006 (p : Pattern) : d211 (change p 163 none) = d109 p := by
  change d109 (change p 163 none) = d109 p
  exact sub4005 p
theorem sub4007 (p : Pattern) : d213 (change p 163 none) = d1140 p := by
  change (if p 162 then d12 (change p 163 none) else d211 (change p 163 none)) = d1140 p
  rw [sub3692, sub4006]
  rfl
theorem sub4008 (p : Pattern) : d1389 (change p 163 none) = d1141 p := by
  change (if p 161 then d12 (change p 163 none) else d213 (change p 163 none)) = d1141 p
  rw [sub3692, sub4007]
  rfl
theorem sub4009 (p : Pattern) : d1390 (change p 163 none) = d4385 p := by
  change (if p 160 then d1389 (change p 163 none) else d1388 (change p 163 none)) = d4385 p
  rw [sub4008, sub4004]
  rfl
theorem sub4010 (p : Pattern) : d1391 (change p 163 none) = d4386 p := by
  change (if p 141 then d1390 (change p 163 none) else d1384 (change p 163 none)) = d4386 p
  rw [sub4009, sub3998]
  rfl
theorem sub4011 (p : Pattern) : d1392 (change p 163 none) = d4387 p := by
  change (if p 138 then d1391 (change p 163 none) else d1380 (change p 163 none)) = d4387 p
  rw [sub4010, sub3994]
  rfl
theorem sub4012 (p : Pattern) : d1393 (change p 163 none) = d4388 p := by
  change (if p 138 then d12 (change p 163 none) else d1391 (change p 163 none)) = d4388 p
  rw [sub3692, sub4010]
  rfl
theorem sub4013 (p : Pattern) : d1394 (change p 163 none) = d4389 p := by
  change (if p 116 then d1393 (change p 163 none) else d1392 (change p 163 none)) = d4389 p
  rw [sub4012, sub4011]
  rfl
theorem sub4014 (p : Pattern) : d1395 (change p 163 none) = d4390 p := by
  change (if p 115 then d1394 (change p 163 none) else d1366 (change p 163 none)) = d4390 p
  rw [sub4013, sub3970]
  rfl
theorem sub4015 (p : Pattern) : d1396 (change p 163 none) = d4391 p := by
  change (if p 71 then d1395 (change p 163 none) else d1236 (change p 163 none)) = d4391 p
  rw [sub4014, sub3810]
  rfl
theorem sub4016 (p : Pattern) : d1397 (change p 163 none) = d4392 p := by
  change (if p 49 then d1396 (change p 163 none) else d1357 (change p 163 none)) = d4392 p
  rw [sub4015, sub3961]
  rfl
theorem sub4017 (p : Pattern) : d1398 (change p 163 none) = d4393 p := by
  change (if p 48 then d1397 (change p 163 none) else d1345 (change p 163 none)) = d4393 p
  rw [sub4016, sub3944]
  rfl
theorem sub4018 (p : Pattern) : d0 (change p 10000 (some 160)) = d0 p := by
  rfl
theorem sub4019 (p : Pattern) : d12 (change p 10000 (some 160)) = d12 p := by
  rfl
theorem sub4020 (p : Pattern) : d13 (change p 10000 (some 160)) = d13 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d0 (change p 10000 (some 160))) = d13 p
  rw [sub4019, sub4018]
  rfl
theorem sub4021 (p : Pattern) : d14 (change p 10000 (some 160)) = d14 p := by
  change (if p 246 then d13 (change p 10000 (some 160)) else d0 (change p 10000 (some 160))) = d14 p
  rw [sub4020, sub4018]
  rfl
theorem sub4022 (p : Pattern) : d2 (change p 10000 (some 160)) = d2 p := by
  rfl
theorem sub4023 (p : Pattern) : d30 (change p 10000 (some 160)) = d30 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d2 (change p 10000 (some 160))) = d30 p
  rw [sub4019, sub4022]
  rfl
theorem sub4024 (p : Pattern) : d31 (change p 10000 (some 160)) = d31 p := by
  change (if p 246 then d30 (change p 10000 (some 160)) else d2 (change p 10000 (some 160))) = d31 p
  rw [sub4023, sub4022]
  rfl
theorem sub4025 (p : Pattern) : d32 (change p 10000 (some 160)) = d32 p := by
  change (if p 204 then d12 (change p 10000 (some 160)) else d31 (change p 10000 (some 160))) = d32 p
  rw [sub4019, sub4024]
  rfl
theorem sub4026 (p : Pattern) : d33 (change p 10000 (some 160)) = d33 p := by
  change (if p 182 then d32 (change p 10000 (some 160)) else d14 (change p 10000 (some 160))) = d33 p
  rw [sub4025, sub4021]
  rfl
theorem sub4027 (p : Pattern) : d6 (change p 10000 (some 160)) = d6 p := by
  rfl
theorem sub4028 (p : Pattern) : d34 (change p 10000 (some 160)) = d34 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d6 (change p 10000 (some 160))) = d34 p
  rw [sub4019, sub4027]
  rfl
theorem sub4029 (p : Pattern) : d35 (change p 10000 (some 160)) = d35 p := by
  change (if p 246 then d34 (change p 10000 (some 160)) else d6 (change p 10000 (some 160))) = d35 p
  rw [sub4028, sub4027]
  rfl
theorem sub4030 (p : Pattern) : d36 (change p 10000 (some 160)) = d36 p := by
  change (if p 204 then d12 (change p 10000 (some 160)) else d35 (change p 10000 (some 160))) = d36 p
  rw [sub4019, sub4029]
  rfl
theorem sub4031 (p : Pattern) : d37 (change p 10000 (some 160)) = d37 p := by
  change (if p 182 then d36 (change p 10000 (some 160)) else d14 (change p 10000 (some 160))) = d37 p
  rw [sub4030, sub4021]
  rfl
theorem sub4032 (p : Pattern) : d38 (change p 10000 (some 160)) = d38 p := by
  change (if p 163 then d37 (change p 10000 (some 160)) else d33 (change p 10000 (some 160))) = d38 p
  rw [sub4031, sub4026]
  rfl
theorem sub4033 (p : Pattern) : d11 (change p 10000 (some 160)) = d11 p := by
  rfl
theorem sub4034 (p : Pattern) : d39 (change p 10000 (some 160)) = d39 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d11 (change p 10000 (some 160))) = d39 p
  rw [sub4019, sub4033]
  rfl
theorem sub4035 (p : Pattern) : d40 (change p 10000 (some 160)) = d40 p := by
  change (if p 246 then d39 (change p 10000 (some 160)) else d11 (change p 10000 (some 160))) = d40 p
  rw [sub4034, sub4033]
  rfl
theorem sub4036 (p : Pattern) : d41 (change p 10000 (some 160)) = d41 p := by
  change (if p 204 then d12 (change p 10000 (some 160)) else d40 (change p 10000 (some 160))) = d41 p
  rw [sub4019, sub4035]
  rfl
theorem sub4037 (p : Pattern) : d42 (change p 10000 (some 160)) = d42 p := by
  change (if p 182 then d41 (change p 10000 (some 160)) else d14 (change p 10000 (some 160))) = d42 p
  rw [sub4036, sub4021]
  rfl
theorem sub4038 (p : Pattern) : d4 (change p 10000 (some 160)) = d4 p := by
  rfl
theorem sub4039 (p : Pattern) : d17 (change p 10000 (some 160)) = d17 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d4 (change p 10000 (some 160))) = d17 p
  rw [sub4019, sub4038]
  rfl
theorem sub4040 (p : Pattern) : d18 (change p 10000 (some 160)) = d18 p := by
  change (if p 246 then d17 (change p 10000 (some 160)) else d4 (change p 10000 (some 160))) = d18 p
  rw [sub4039, sub4038]
  rfl
theorem sub4041 (p : Pattern) : d43 (change p 10000 (some 160)) = d43 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d18 (change p 10000 (some 160))) = d43 p
  rw [sub4019, sub4040]
  rfl
theorem sub4042 (p : Pattern) : d44 (change p 10000 (some 160)) = d44 p := by
  change (if p 163 then d43 (change p 10000 (some 160)) else d42 (change p 10000 (some 160))) = d44 p
  rw [sub4041, sub4037]
  rfl
theorem sub4043 (p : Pattern) : d45 (change p 10000 (some 160)) = d45 p := by
  change (if p 162 then d44 (change p 10000 (some 160)) else d38 (change p 10000 (some 160))) = d45 p
  rw [sub4042, sub4032]
  rfl
theorem sub4044 (p : Pattern) : d46 (change p 10000 (some 160)) = d46 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d14 (change p 10000 (some 160))) = d46 p
  rw [sub4019, sub4021]
  rfl
theorem sub4045 (p : Pattern) : d47 (change p 10000 (some 160)) = d47 p := by
  change (if p 163 then d43 (change p 10000 (some 160)) else d46 (change p 10000 (some 160))) = d47 p
  rw [sub4041, sub4044]
  rfl
theorem sub4046 (p : Pattern) : d9 (change p 10000 (some 160)) = d9 p := by
  rfl
theorem sub4047 (p : Pattern) : d23 (change p 10000 (some 160)) = d23 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d9 (change p 10000 (some 160))) = d23 p
  rw [sub4019, sub4046]
  rfl
theorem sub4048 (p : Pattern) : d24 (change p 10000 (some 160)) = d24 p := by
  change (if p 246 then d23 (change p 10000 (some 160)) else d9 (change p 10000 (some 160))) = d24 p
  rw [sub4047, sub4046]
  rfl
theorem sub4049 (p : Pattern) : d48 (change p 10000 (some 160)) = d48 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d24 (change p 10000 (some 160))) = d48 p
  rw [sub4019, sub4048]
  rfl
theorem sub4050 (p : Pattern) : d49 (change p 10000 (some 160)) = d49 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d48 (change p 10000 (some 160))) = d49 p
  rw [sub4019, sub4049]
  rfl
theorem sub4051 (p : Pattern) : d50 (change p 10000 (some 160)) = d50 p := by
  change (if p 162 then d49 (change p 10000 (some 160)) else d47 (change p 10000 (some 160))) = d50 p
  rw [sub4050, sub4045]
  rfl
theorem sub4052 (p : Pattern) : d51 (change p 10000 (some 160)) = d51 p := by
  change (if p 161 then d50 (change p 10000 (some 160)) else d45 (change p 10000 (some 160))) = d51 p
  rw [sub4051, sub4043]
  rfl
theorem sub4053 (p : Pattern) : d52 (change p 10000 (some 160)) = d51 p := by
  change d51 (change p 10000 (some 160)) = d51 p
  exact sub4052 p
theorem sub4054 (p : Pattern) : d66 (change p 10000 (some 160)) = d66 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d31 (change p 10000 (some 160))) = d66 p
  rw [sub4019, sub4024]
  rfl
theorem sub4055 (p : Pattern) : d67 (change p 10000 (some 160)) = d67 p := by
  change (if p 163 then d66 (change p 10000 (some 160)) else d37 (change p 10000 (some 160))) = d67 p
  rw [sub4054, sub4031]
  rfl
theorem sub4056 (p : Pattern) : d68 (change p 10000 (some 160)) = d68 p := by
  change (if p 163 then d48 (change p 10000 (some 160)) else d43 (change p 10000 (some 160))) = d68 p
  rw [sub4049, sub4041]
  rfl
theorem sub4057 (p : Pattern) : d69 (change p 10000 (some 160)) = d69 p := by
  change (if p 162 then d68 (change p 10000 (some 160)) else d67 (change p 10000 (some 160))) = d69 p
  rw [sub4056, sub4055]
  rfl
theorem sub4058 (p : Pattern) : d10 (change p 10000 (some 160)) = d10 p := by
  rfl
theorem sub4059 (p : Pattern) : d57 (change p 10000 (some 160)) = d57 p := by
  change (if p 247 then d12 (change p 10000 (some 160)) else d10 (change p 10000 (some 160))) = d57 p
  rw [sub4019, sub4058]
  rfl
theorem sub4060 (p : Pattern) : d58 (change p 10000 (some 160)) = d58 p := by
  change (if p 246 then d57 (change p 10000 (some 160)) else d10 (change p 10000 (some 160))) = d58 p
  rw [sub4059, sub4058]
  rfl
theorem sub4061 (p : Pattern) : d70 (change p 10000 (some 160)) = d70 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d58 (change p 10000 (some 160))) = d70 p
  rw [sub4019, sub4060]
  rfl
theorem sub4062 (p : Pattern) : d71 (change p 10000 (some 160)) = d71 p := by
  change (if p 163 then d70 (change p 10000 (some 160)) else d43 (change p 10000 (some 160))) = d71 p
  rw [sub4061, sub4041]
  rfl
theorem sub4063 (p : Pattern) : d72 (change p 10000 (some 160)) = d72 p := by
  change (if p 182 then d12 (change p 10000 (some 160)) else d40 (change p 10000 (some 160))) = d72 p
  rw [sub4019, sub4035]
  rfl
theorem sub4064 (p : Pattern) : d73 (change p 10000 (some 160)) = d73 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d72 (change p 10000 (some 160))) = d73 p
  rw [sub4019, sub4063]
  rfl
theorem sub4065 (p : Pattern) : d74 (change p 10000 (some 160)) = d74 p := by
  change (if p 162 then d73 (change p 10000 (some 160)) else d71 (change p 10000 (some 160))) = d74 p
  rw [sub4064, sub4062]
  rfl
theorem sub4066 (p : Pattern) : d75 (change p 10000 (some 160)) = d75 p := by
  change (if p 161 then d74 (change p 10000 (some 160)) else d69 (change p 10000 (some 160))) = d75 p
  rw [sub4065, sub4057]
  rfl
theorem sub4067 (p : Pattern) : d76 (change p 10000 (some 160)) = d75 p := by
  change d75 (change p 10000 (some 160)) = d75 p
  exact sub4066 p
theorem sub4068 (p : Pattern) : d77 (change p 10000 (some 160)) = d4120 p := by
  change (if p 141 then d76 (change p 10000 (some 160)) else d52 (change p 10000 (some 160))) = d4120 p
  rw [sub4067, sub4053]
  rfl
theorem sub4069 (p : Pattern) : d53 (change p 10000 (some 160)) = d53 p := by
  change (if p 182 then d32 (change p 10000 (some 160)) else d31 (change p 10000 (some 160))) = d53 p
  rw [sub4025, sub4024]
  rfl
theorem sub4070 (p : Pattern) : d78 (change p 10000 (some 160)) = d78 p := by
  change (if p 182 then d36 (change p 10000 (some 160)) else d35 (change p 10000 (some 160))) = d78 p
  rw [sub4030, sub4029]
  rfl
theorem sub4071 (p : Pattern) : d79 (change p 10000 (some 160)) = d79 p := by
  change (if p 163 then d78 (change p 10000 (some 160)) else d53 (change p 10000 (some 160))) = d79 p
  rw [sub4070, sub4069]
  rfl
theorem sub4072 (p : Pattern) : d62 (change p 10000 (some 160)) = d62 p := by
  change (if p 182 then d41 (change p 10000 (some 160)) else d40 (change p 10000 (some 160))) = d62 p
  rw [sub4036, sub4035]
  rfl
theorem sub4073 (p : Pattern) : d63 (change p 10000 (some 160)) = d63 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d62 (change p 10000 (some 160))) = d63 p
  rw [sub4019, sub4072]
  rfl
theorem sub4074 (p : Pattern) : d80 (change p 10000 (some 160)) = d80 p := by
  change (if p 162 then d63 (change p 10000 (some 160)) else d79 (change p 10000 (some 160))) = d80 p
  rw [sub4073, sub4071]
  rfl
theorem sub4075 (p : Pattern) : d81 (change p 10000 (some 160)) = d81 p := by
  change (if p 161 then d12 (change p 10000 (some 160)) else d80 (change p 10000 (some 160))) = d81 p
  rw [sub4019, sub4074]
  rfl
theorem sub4076 (p : Pattern) : d82 (change p 10000 (some 160)) = d81 p := by
  change d81 (change p 10000 (some 160)) = d81 p
  exact sub4075 p
theorem sub4077 (p : Pattern) : d83 (change p 10000 (some 160)) = d83 p := by
  change (if p 163 then d12 (change p 10000 (some 160)) else d78 (change p 10000 (some 160))) = d83 p
  rw [sub4019, sub4070]
  rfl
theorem sub4078 (p : Pattern) : d84 (change p 10000 (some 160)) = d84 p := by
  change (if p 162 then d12 (change p 10000 (some 160)) else d83 (change p 10000 (some 160))) = d84 p
  rw [sub4019, sub4077]
  rfl
theorem sub4079 (p : Pattern) : d85 (change p 10000 (some 160)) = d85 p := by
  change (if p 161 then d12 (change p 10000 (some 160)) else d84 (change p 10000 (some 160))) = d85 p
  rw [sub4019, sub4078]
  rfl
end NetHack.Sokoban22Refined85
