/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions31
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3840 (p : Pattern) : d1266 (change p 163 none) = d4323 p := by
  change (if p 138 then d1265 (change p 163 none) else d1262 (change p 163 none)) = d4323 p
  rw [sub3839, sub3836]
  rfl
theorem sub3841 (p : Pattern) : d1267 (change p 163 none) = d4330 p := by
  change (if p 138 then d12 (change p 163 none) else d1228 (change p 163 none)) = d4330 p
  rw [sub3692, sub3802]
  rfl
theorem sub3842 (p : Pattern) : d1268 (change p 163 none) = d4331 p := by
  change (if p 116 then d1267 (change p 163 none) else d1266 (change p 163 none)) = d4331 p
  rw [sub3841, sub3840]
  rfl
theorem sub3843 (p : Pattern) : d1269 (change p 163 none) = d4332 p := by
  change (if p 115 then d1268 (change p 163 none) else d1259 (change p 163 none)) = d4332 p
  rw [sub3842, sub3833]
  rfl
theorem sub3844 (p : Pattern) : d1270 (change p 163 none) = d4332 p := by
  change (if p 71 then d1269 (change p 163 none) else d1236 (change p 163 none)) = d4332 p
  rw [sub3843, sub3810]
  simp only [ite_self]
theorem sub3845 (p : Pattern) : d1 (change p 163 none) = d1 p := by
  rfl
theorem sub3846 (p : Pattern) : d102 (change p 163 none) = d102 p := by
  change (if p 247 then d12 (change p 163 none) else d1 (change p 163 none)) = d102 p
  rw [sub3692, sub3845]
  rfl
theorem sub3847 (p : Pattern) : d103 (change p 163 none) = d103 p := by
  change (if p 246 then d102 (change p 163 none) else d1 (change p 163 none)) = d103 p
  rw [sub3846, sub3845]
  rfl
theorem sub3848 (p : Pattern) : d104 (change p 163 none) = d104 p := by
  change (if p 204 then d12 (change p 163 none) else d103 (change p 163 none)) = d104 p
  rw [sub3692, sub3847]
  rfl
theorem sub3849 (p : Pattern) : d105 (change p 163 none) = d105 p := by
  change (if p 182 then d104 (change p 163 none) else d103 (change p 163 none)) = d105 p
  rw [sub3848, sub3847]
  rfl
theorem sub3850 (p : Pattern) : d1271 (change p 163 none) = d105 p := by
  change d105 (change p 163 none) = d105 p
  exact sub3849 p
theorem sub3851 (p : Pattern) : d1272 (change p 163 none) = d105 p := by
  change d105 (change p 163 none) = d105 p
  exact sub3849 p
theorem sub3852 (p : Pattern) : d1273 (change p 163 none) = d105 p := by
  change (if p 162 then d1272 (change p 163 none) else d1271 (change p 163 none)) = d105 p
  rw [sub3851, sub3850]
  simp only [ite_self]
theorem sub3853 (p : Pattern) : d1274 (change p 163 none) = d105 p := by
  change d105 (change p 163 none) = d105 p
  exact sub3849 p
theorem sub3854 (p : Pattern) : d10 (change p 163 none) = d10 p := by
  rfl
theorem sub3855 (p : Pattern) : d57 (change p 163 none) = d57 p := by
  change (if p 247 then d12 (change p 163 none) else d10 (change p 163 none)) = d57 p
  rw [sub3692, sub3854]
  rfl
theorem sub3856 (p : Pattern) : d58 (change p 163 none) = d58 p := by
  change (if p 246 then d57 (change p 163 none) else d10 (change p 163 none)) = d58 p
  rw [sub3855, sub3854]
  rfl
theorem sub3857 (p : Pattern) : d59 (change p 163 none) = d59 p := by
  change (if p 204 then d12 (change p 163 none) else d58 (change p 163 none)) = d59 p
  rw [sub3692, sub3856]
  rfl
theorem sub3858 (p : Pattern) : d60 (change p 163 none) = d60 p := by
  change (if p 182 then d59 (change p 163 none) else d58 (change p 163 none)) = d60 p
  rw [sub3857, sub3856]
  rfl
theorem sub3859 (p : Pattern) : d112 (change p 163 none) = d60 p := by
  change d60 (change p 163 none) = d60 p
  exact sub3858 p
theorem sub3860 (p : Pattern) : d1275 (change p 163 none) = d4333 p := by
  change (if p 162 then d112 (change p 163 none) else d1274 (change p 163 none)) = d4333 p
  rw [sub3859, sub3853]
  rfl
theorem sub3861 (p : Pattern) : d1276 (change p 163 none) = d4334 p := by
  change (if p 161 then d1275 (change p 163 none) else d1273 (change p 163 none)) = d4334 p
  rw [sub3860, sub3852]
  rfl
theorem sub3862 (p : Pattern) : d3 (change p 163 none) = d3 p := by
  rfl
theorem sub3863 (p : Pattern) : d115 (change p 163 none) = d115 p := by
  change (if p 247 then d12 (change p 163 none) else d3 (change p 163 none)) = d115 p
  rw [sub3692, sub3862]
  rfl
theorem sub3864 (p : Pattern) : d116 (change p 163 none) = d116 p := by
  change (if p 246 then d115 (change p 163 none) else d3 (change p 163 none)) = d116 p
  rw [sub3863, sub3862]
  rfl
theorem sub3865 (p : Pattern) : d117 (change p 163 none) = d117 p := by
  change (if p 204 then d12 (change p 163 none) else d116 (change p 163 none)) = d117 p
  rw [sub3692, sub3864]
  rfl
theorem sub3866 (p : Pattern) : d118 (change p 163 none) = d118 p := by
  change (if p 182 then d117 (change p 163 none) else d103 (change p 163 none)) = d118 p
  rw [sub3865, sub3847]
  rfl
theorem sub3867 (p : Pattern) : d1277 (change p 163 none) = d118 p := by
  change d118 (change p 163 none) = d118 p
  exact sub3866 p
theorem sub3868 (p : Pattern) : d124 (change p 163 none) = d124 p := by
  change (if p 182 then d12 (change p 163 none) else d103 (change p 163 none)) = d124 p
  rw [sub3692, sub3847]
  rfl
theorem sub3869 (p : Pattern) : d1278 (change p 163 none) = d124 p := by
  change d124 (change p 163 none) = d124 p
  exact sub3868 p
theorem sub3870 (p : Pattern) : d1279 (change p 163 none) = d4335 p := by
  change (if p 162 then d1278 (change p 163 none) else d1277 (change p 163 none)) = d4335 p
  rw [sub3869, sub3867]
  rfl
theorem sub3871 (p : Pattern) : d70 (change p 163 none) = d70 p := by
  change (if p 182 then d12 (change p 163 none) else d58 (change p 163 none)) = d70 p
  rw [sub3692, sub3856]
  rfl
theorem sub3872 (p : Pattern) : d128 (change p 163 none) = d70 p := by
  change d70 (change p 163 none) = d70 p
  exact sub3871 p
theorem sub3873 (p : Pattern) : d1280 (change p 163 none) = d4336 p := by
  change (if p 162 then d128 (change p 163 none) else d1278 (change p 163 none)) = d4336 p
  rw [sub3872, sub3869]
  rfl
theorem sub3874 (p : Pattern) : d1281 (change p 163 none) = d4337 p := by
  change (if p 161 then d1280 (change p 163 none) else d1279 (change p 163 none)) = d4337 p
  rw [sub3873, sub3870]
  rfl
theorem sub3875 (p : Pattern) : d1282 (change p 163 none) = d4338 p := by
  change (if p 160 then d1281 (change p 163 none) else d1276 (change p 163 none)) = d4338 p
  rw [sub3874, sub3861]
  rfl
theorem sub3876 (p : Pattern) : d1283 (change p 163 none) = d105 p := by
  change d105 (change p 163 none) = d105 p
  exact sub3849 p
theorem sub3877 (p : Pattern) : d132 (change p 163 none) = d132 p := by
  change (if p 182 then d117 (change p 163 none) else d116 (change p 163 none)) = d132 p
  rw [sub3865, sub3864]
  rfl
theorem sub3878 (p : Pattern) : d1284 (change p 163 none) = d132 p := by
  change d132 (change p 163 none) = d132 p
  exact sub3877 p
theorem sub3879 (p : Pattern) : d1285 (change p 163 none) = d4339 p := by
  change (if p 162 then d1284 (change p 163 none) else d1283 (change p 163 none)) = d4339 p
  rw [sub3878, sub3876]
  rfl
theorem sub3880 (p : Pattern) : d1286 (change p 163 none) = d132 p := by
  change d132 (change p 163 none) = d132 p
  exact sub3877 p
theorem sub3881 (p : Pattern) : d1287 (change p 163 none) = d1061 p := by
  change (if p 162 then d12 (change p 163 none) else d1286 (change p 163 none)) = d1061 p
  rw [sub3692, sub3880]
  rfl
theorem sub3882 (p : Pattern) : d1288 (change p 163 none) = d4340 p := by
  change (if p 161 then d1287 (change p 163 none) else d1285 (change p 163 none)) = d4340 p
  rw [sub3881, sub3879]
  rfl
theorem sub3883 (p : Pattern) : d1289 (change p 163 none) = d132 p := by
  change d132 (change p 163 none) = d132 p
  exact sub3877 p
theorem sub3884 (p : Pattern) : d139 (change p 163 none) = d139 p := by
  change (if p 182 then d12 (change p 163 none) else d116 (change p 163 none)) = d139 p
  rw [sub3692, sub3864]
  rfl
theorem sub3885 (p : Pattern) : d1290 (change p 163 none) = d139 p := by
  change d139 (change p 163 none) = d139 p
  exact sub3884 p
theorem sub3886 (p : Pattern) : d1291 (change p 163 none) = d4341 p := by
  change (if p 162 then d1290 (change p 163 none) else d1289 (change p 163 none)) = d4341 p
  rw [sub3885, sub3883]
  rfl
theorem sub3887 (p : Pattern) : d1292 (change p 163 none) = d4342 p := by
  change (if p 162 then d12 (change p 163 none) else d1290 (change p 163 none)) = d4342 p
  rw [sub3692, sub3885]
  rfl
theorem sub3888 (p : Pattern) : d1293 (change p 163 none) = d4343 p := by
  change (if p 161 then d1292 (change p 163 none) else d1291 (change p 163 none)) = d4343 p
  rw [sub3887, sub3886]
  rfl
theorem sub3889 (p : Pattern) : d1294 (change p 163 none) = d4344 p := by
  change (if p 160 then d1293 (change p 163 none) else d1288 (change p 163 none)) = d4344 p
  rw [sub3888, sub3882]
  rfl
theorem sub3890 (p : Pattern) : d1295 (change p 163 none) = d4345 p := by
  change (if p 141 then d1294 (change p 163 none) else d1282 (change p 163 none)) = d4345 p
  rw [sub3889, sub3875]
  rfl
theorem sub3891 (p : Pattern) : d1296 (change p 163 none) = d105 p := by
  change d105 (change p 163 none) = d105 p
  exact sub3849 p
theorem sub3892 (p : Pattern) : d1297 (change p 163 none) = d105 p := by
  change (if p 162 then d1296 (change p 163 none) else d1274 (change p 163 none)) = d105 p
  rw [sub3891, sub3853]
  simp only [ite_self]
theorem sub3893 (p : Pattern) : d1298 (change p 163 none) = d4333 p := by
  change (if p 162 then d112 (change p 163 none) else d1296 (change p 163 none)) = d4333 p
  rw [sub3859, sub3891]
  rfl
theorem sub3894 (p : Pattern) : d1299 (change p 163 none) = d4334 p := by
  change (if p 161 then d1298 (change p 163 none) else d1297 (change p 163 none)) = d4334 p
  rw [sub3893, sub3892]
  rfl
theorem sub3895 (p : Pattern) : d1300 (change p 163 none) = d1061 p := by
  change (if p 162 then d12 (change p 163 none) else d1289 (change p 163 none)) = d1061 p
  rw [sub3692, sub3883]
  rfl
theorem sub3896 (p : Pattern) : d1301 (change p 163 none) = d1062 p := by
  change (if p 161 then d12 (change p 163 none) else d1300 (change p 163 none)) = d1062 p
  rw [sub3692, sub3895]
  rfl
theorem sub3897 (p : Pattern) : d1302 (change p 163 none) = d4346 p := by
  change (if p 160 then d1301 (change p 163 none) else d1299 (change p 163 none)) = d4346 p
  rw [sub3896, sub3894]
  rfl
theorem sub3898 (p : Pattern) : d1303 (change p 163 none) = d105 p := by
  change d105 (change p 163 none) = d105 p
  exact sub3849 p
theorem sub3899 (p : Pattern) : d1304 (change p 163 none) = d4339 p := by
  change (if p 162 then d1289 (change p 163 none) else d1303 (change p 163 none)) = d4339 p
  rw [sub3883, sub3898]
  rfl
theorem sub3900 (p : Pattern) : d1305 (change p 163 none) = d4340 p := by
  change (if p 161 then d1300 (change p 163 none) else d1304 (change p 163 none)) = d4340 p
  rw [sub3895, sub3899]
  rfl
theorem sub3901 (p : Pattern) : d1306 (change p 163 none) = d4347 p := by
  change (if p 160 then d1301 (change p 163 none) else d1305 (change p 163 none)) = d4347 p
  rw [sub3896, sub3900]
  rfl
theorem sub3902 (p : Pattern) : d1307 (change p 163 none) = d4348 p := by
  change (if p 141 then d1306 (change p 163 none) else d1302 (change p 163 none)) = d4348 p
  rw [sub3901, sub3897]
  rfl
theorem sub3903 (p : Pattern) : d1308 (change p 163 none) = d4349 p := by
  change (if p 138 then d1307 (change p 163 none) else d1295 (change p 163 none)) = d4349 p
  rw [sub3902, sub3890]
  rfl
theorem sub3904 (p : Pattern) : d1309 (change p 163 none) = d105 p := by
  change (if p 162 then d1296 (change p 163 none) else d1272 (change p 163 none)) = d105 p
  rw [sub3891, sub3851]
  simp only [ite_self]
theorem sub3905 (p : Pattern) : d1310 (change p 163 none) = d4334 p := by
  change (if p 161 then d1298 (change p 163 none) else d1309 (change p 163 none)) = d4334 p
  rw [sub3893, sub3904]
  rfl
theorem sub3906 (p : Pattern) : d1311 (change p 163 none) = d4346 p := by
  change (if p 160 then d1301 (change p 163 none) else d1310 (change p 163 none)) = d4346 p
  rw [sub3896, sub3905]
  rfl
theorem sub3907 (p : Pattern) : d1312 (change p 163 none) = d105 p := by
  change d105 (change p 163 none) = d105 p
  exact sub3849 p
theorem sub3908 (p : Pattern) : d1313 (change p 163 none) = d4339 p := by
  change (if p 162 then d1289 (change p 163 none) else d1312 (change p 163 none)) = d4339 p
  rw [sub3883, sub3907]
  rfl
theorem sub3909 (p : Pattern) : d1314 (change p 163 none) = d4340 p := by
  change (if p 161 then d1300 (change p 163 none) else d1313 (change p 163 none)) = d4340 p
  rw [sub3895, sub3908]
  rfl
theorem sub3910 (p : Pattern) : d1315 (change p 163 none) = d4347 p := by
  change (if p 160 then d1301 (change p 163 none) else d1314 (change p 163 none)) = d4347 p
  rw [sub3896, sub3909]
  rfl
theorem sub3911 (p : Pattern) : d1316 (change p 163 none) = d4348 p := by
  change (if p 141 then d1315 (change p 163 none) else d1311 (change p 163 none)) = d4348 p
  rw [sub3910, sub3906]
  rfl
theorem sub3912 (p : Pattern) : d159 (change p 163 none) = d4350 p := by
  change (if p 162 then d12 (change p 163 none) else d112 (change p 163 none)) = d4350 p
  rw [sub3692, sub3859]
  rfl
theorem sub3913 (p : Pattern) : d160 (change p 163 none) = d4351 p := by
  change (if p 161 then d12 (change p 163 none) else d159 (change p 163 none)) = d4351 p
  rw [sub3692, sub3912]
  rfl
theorem sub3914 (p : Pattern) : d161 (change p 163 none) = d4352 p := by
  change (if p 160 then d12 (change p 163 none) else d160 (change p 163 none)) = d4352 p
  rw [sub3692, sub3913]
  rfl
theorem sub3915 (p : Pattern) : d162 (change p 163 none) = d4353 p := by
  change (if p 141 then d12 (change p 163 none) else d161 (change p 163 none)) = d4353 p
  rw [sub3692, sub3914]
  rfl
theorem sub3916 (p : Pattern) : d1317 (change p 163 none) = d4354 p := by
  change (if p 138 then d162 (change p 163 none) else d1316 (change p 163 none)) = d4354 p
  rw [sub3915, sub3911]
  rfl
theorem sub3917 (p : Pattern) : d1318 (change p 163 none) = d4355 p := by
  change (if p 116 then d1317 (change p 163 none) else d1308 (change p 163 none)) = d4355 p
  rw [sub3916, sub3903]
  rfl
theorem sub3918 (p : Pattern) : d1319 (change p 163 none) = d105 p := by
  change d105 (change p 163 none) = d105 p
  exact sub3849 p
theorem sub3919 (p : Pattern) : d1320 (change p 163 none) = d105 p := by
  change (if p 162 then d1303 (change p 163 none) else d1319 (change p 163 none)) = d105 p
  rw [sub3898, sub3918]
  simp only [ite_self]
theorem sub3920 (p : Pattern) : d1321 (change p 163 none) = d4334 p := by
  change (if p 161 then d1298 (change p 163 none) else d1320 (change p 163 none)) = d4334 p
  rw [sub3893, sub3919]
  rfl
theorem sub3921 (p : Pattern) : d1322 (change p 163 none) = d118 p := by
  change d118 (change p 163 none) = d118 p
  exact sub3866 p
theorem sub3922 (p : Pattern) : d1323 (change p 163 none) = d4335 p := by
  change (if p 162 then d1278 (change p 163 none) else d1322 (change p 163 none)) = d4335 p
  rw [sub3869, sub3921]
  rfl
theorem sub3923 (p : Pattern) : d1324 (change p 163 none) = d4337 p := by
  change (if p 161 then d1280 (change p 163 none) else d1323 (change p 163 none)) = d4337 p
  rw [sub3873, sub3922]
  rfl
theorem sub3924 (p : Pattern) : d1325 (change p 163 none) = d4338 p := by
  change (if p 160 then d1324 (change p 163 none) else d1321 (change p 163 none)) = d4338 p
  rw [sub3923, sub3920]
  rfl
theorem sub3925 (p : Pattern) : d1326 (change p 163 none) = d4339 p := by
  change (if p 162 then d1289 (change p 163 none) else d1274 (change p 163 none)) = d4339 p
  rw [sub3883, sub3853]
  rfl
theorem sub3926 (p : Pattern) : d1327 (change p 163 none) = d4340 p := by
  change (if p 161 then d1300 (change p 163 none) else d1326 (change p 163 none)) = d4340 p
  rw [sub3895, sub3925]
  rfl
theorem sub3927 (p : Pattern) : d1328 (change p 163 none) = d4344 p := by
  change (if p 160 then d1293 (change p 163 none) else d1327 (change p 163 none)) = d4344 p
  rw [sub3888, sub3926]
  rfl
theorem sub3928 (p : Pattern) : d1329 (change p 163 none) = d4345 p := by
  change (if p 141 then d1328 (change p 163 none) else d1325 (change p 163 none)) = d4345 p
  rw [sub3927, sub3924]
  rfl
theorem sub3929 (p : Pattern) : d1330 (change p 163 none) = d4334 p := by
  change (if p 161 then d1298 (change p 163 none) else d1296 (change p 163 none)) = d4334 p
  rw [sub3893, sub3891]
  rfl
theorem sub3930 (p : Pattern) : d1331 (change p 163 none) = d4346 p := by
  change (if p 160 then d1301 (change p 163 none) else d1330 (change p 163 none)) = d4346 p
  rw [sub3896, sub3929]
  rfl
theorem sub3931 (p : Pattern) : d1332 (change p 163 none) = d4339 p := by
  change (if p 162 then d1289 (change p 163 none) else d1296 (change p 163 none)) = d4339 p
  rw [sub3883, sub3891]
  rfl
theorem sub3932 (p : Pattern) : d1333 (change p 163 none) = d4340 p := by
  change (if p 161 then d1300 (change p 163 none) else d1332 (change p 163 none)) = d4340 p
  rw [sub3895, sub3931]
  rfl
theorem sub3933 (p : Pattern) : d1334 (change p 163 none) = d4347 p := by
  change (if p 160 then d1301 (change p 163 none) else d1333 (change p 163 none)) = d4347 p
  rw [sub3896, sub3932]
  rfl
theorem sub3934 (p : Pattern) : d1335 (change p 163 none) = d4348 p := by
  change (if p 141 then d1334 (change p 163 none) else d1331 (change p 163 none)) = d4348 p
  rw [sub3933, sub3930]
  rfl
theorem sub3935 (p : Pattern) : d1336 (change p 163 none) = d4349 p := by
  change (if p 138 then d1335 (change p 163 none) else d1329 (change p 163 none)) = d4349 p
  rw [sub3934, sub3928]
  rfl
theorem sub3936 (p : Pattern) : d1337 (change p 163 none) = d105 p := by
  change (if p 162 then d1296 (change p 163 none) else d1303 (change p 163 none)) = d105 p
  rw [sub3891, sub3898]
  simp only [ite_self]
theorem sub3937 (p : Pattern) : d1338 (change p 163 none) = d4334 p := by
  change (if p 161 then d1298 (change p 163 none) else d1337 (change p 163 none)) = d4334 p
  rw [sub3893, sub3936]
  rfl
theorem sub3938 (p : Pattern) : d1339 (change p 163 none) = d4346 p := by
  change (if p 160 then d1301 (change p 163 none) else d1338 (change p 163 none)) = d4346 p
  rw [sub3896, sub3937]
  rfl
theorem sub3939 (p : Pattern) : d1340 (change p 163 none) = d4348 p := by
  change (if p 141 then d1334 (change p 163 none) else d1339 (change p 163 none)) = d4348 p
  rw [sub3933, sub3938]
  rfl
theorem sub3940 (p : Pattern) : d1341 (change p 163 none) = d4356 p := by
  change (if p 138 then d12 (change p 163 none) else d1340 (change p 163 none)) = d4356 p
  rw [sub3692, sub3939]
  rfl
theorem sub3941 (p : Pattern) : d1342 (change p 163 none) = d4357 p := by
  change (if p 116 then d1341 (change p 163 none) else d1336 (change p 163 none)) = d4357 p
  rw [sub3940, sub3935]
  rfl
theorem sub3942 (p : Pattern) : d1343 (change p 163 none) = d4358 p := by
  change (if p 115 then d1342 (change p 163 none) else d1318 (change p 163 none)) = d4358 p
  rw [sub3941, sub3917]
  rfl
theorem sub3943 (p : Pattern) : d1344 (change p 163 none) = d4359 p := by
  change (if p 71 then d1343 (change p 163 none) else d1236 (change p 163 none)) = d4359 p
  rw [sub3942, sub3810]
  rfl
theorem sub3944 (p : Pattern) : d1345 (change p 163 none) = d4360 p := by
  change (if p 49 then d1344 (change p 163 none) else d1270 (change p 163 none)) = d4360 p
  rw [sub3943, sub3844]
  rfl
theorem sub3945 (p : Pattern) : d1346 (change p 163 none) = d4361 p := by
  change (if p 161 then d1182 (change p 163 none) else d1181 (change p 163 none)) = d4361 p
  rw [sub3753, sub3752]
  rfl
theorem sub3946 (p : Pattern) : d4 (change p 163 none) = d4 p := by
  rfl
theorem sub3947 (p : Pattern) : d17 (change p 163 none) = d17 p := by
  change (if p 247 then d12 (change p 163 none) else d4 (change p 163 none)) = d17 p
  rw [sub3692, sub3946]
  rfl
theorem sub3948 (p : Pattern) : d18 (change p 163 none) = d18 p := by
  change (if p 246 then d17 (change p 163 none) else d4 (change p 163 none)) = d18 p
  rw [sub3947, sub3946]
  rfl
theorem sub3949 (p : Pattern) : d19 (change p 163 none) = d19 p := by
  change (if p 204 then d12 (change p 163 none) else d18 (change p 163 none)) = d19 p
  rw [sub3692, sub3948]
  rfl
theorem sub3950 (p : Pattern) : d20 (change p 163 none) = d20 p := by
  change (if p 182 then d19 (change p 163 none) else d18 (change p 163 none)) = d20 p
  rw [sub3949, sub3948]
  rfl
theorem sub3951 (p : Pattern) : d1347 (change p 163 none) = d20 p := by
  change d20 (change p 163 none) = d20 p
  exact sub3950 p
theorem sub3952 (p : Pattern) : d1348 (change p 163 none) = d1100 p := by
  change (if p 162 then d12 (change p 163 none) else d1347 (change p 163 none)) = d1100 p
  rw [sub3692, sub3951]
  rfl
theorem sub3953 (p : Pattern) : d1349 (change p 163 none) = d1101 p := by
  change (if p 161 then d12 (change p 163 none) else d1348 (change p 163 none)) = d1101 p
  rw [sub3692, sub3952]
  rfl
theorem sub3954 (p : Pattern) : d1350 (change p 163 none) = d4362 p := by
  change (if p 160 then d1349 (change p 163 none) else d1346 (change p 163 none)) = d4362 p
  rw [sub3953, sub3945]
  rfl
theorem sub3955 (p : Pattern) : d1351 (change p 163 none) = d4363 p := by
  change (if p 141 then d1350 (change p 163 none) else d1264 (change p 163 none)) = d4363 p
  rw [sub3954, sub3838]
  rfl
theorem sub3956 (p : Pattern) : d1352 (change p 163 none) = d4364 p := by
  change (if p 138 then d1351 (change p 163 none) else d1262 (change p 163 none)) = d4364 p
  rw [sub3955, sub3836]
  rfl
theorem sub3957 (p : Pattern) : d1353 (change p 163 none) = d4363 p := by
  change (if p 141 then d1350 (change p 163 none) else d1224 (change p 163 none)) = d4363 p
  rw [sub3954, sub3798]
  rfl
theorem sub3958 (p : Pattern) : d1354 (change p 163 none) = d4365 p := by
  change (if p 138 then d12 (change p 163 none) else d1353 (change p 163 none)) = d4365 p
  rw [sub3692, sub3957]
  rfl
theorem sub3959 (p : Pattern) : d1355 (change p 163 none) = d4366 p := by
  change (if p 116 then d1354 (change p 163 none) else d1352 (change p 163 none)) = d4366 p
  rw [sub3958, sub3956]
  rfl
end NetHack.Sokoban22Refined85
