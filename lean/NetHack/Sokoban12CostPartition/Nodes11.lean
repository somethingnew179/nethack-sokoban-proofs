/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Nodes10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1320 (p : Pattern) : Int := if p 186 then d0 p else d1317 p
theorem agree1320 (p q : Pattern) (h : Agree support p q) : d1320 p = d1320 q := by
  simp only [d1320, h 186 (by decide), agree0 p q h, agree1317 p q h]
theorem nonnegative1320 (p : Pattern) : 0 ≤ d1320 p :=
  nonnegative_ite (p 186) (nonnegative0 p) (nonnegative1317 p)
def d1321 (p : Pattern) : Int := if p 168 then d1320 p else d1318 p
theorem agree1321 (p q : Pattern) (h : Agree support p q) : d1321 p = d1321 q := by
  simp only [d1321, h 168 (by decide), agree1320 p q h, agree1318 p q h]
theorem nonnegative1321 (p : Pattern) : 0 ≤ d1321 p :=
  nonnegative_ite (p 168) (nonnegative1320 p) (nonnegative1318 p)
def d1322 (p : Pattern) : Int := if p 160 then d1321 p else d1319 p
theorem agree1322 (p q : Pattern) (h : Agree support p q) : d1322 p = d1322 q := by
  simp only [d1322, h 160 (by decide), agree1321 p q h, agree1319 p q h]
theorem nonnegative1322 (p : Pattern) : 0 ≤ d1322 p :=
  nonnegative_ite (p 160) (nonnegative1321 p) (nonnegative1319 p)
def d1323 (p : Pattern) : Int := if p 168 then d0 p else d1320 p
theorem agree1323 (p q : Pattern) (h : Agree support p q) : d1323 p = d1323 q := by
  simp only [d1323, h 168 (by decide), agree0 p q h, agree1320 p q h]
theorem nonnegative1323 (p : Pattern) : 0 ≤ d1323 p :=
  nonnegative_ite (p 168) (nonnegative0 p) (nonnegative1320 p)
def d1324 (p : Pattern) : Int := if p 160 then d1323 p else d1321 p
theorem agree1324 (p q : Pattern) (h : Agree support p q) : d1324 p = d1324 q := by
  simp only [d1324, h 160 (by decide), agree1323 p q h, agree1321 p q h]
theorem nonnegative1324 (p : Pattern) : 0 ≤ d1324 p :=
  nonnegative_ite (p 160) (nonnegative1323 p) (nonnegative1321 p)
def d1325 (p : Pattern) : Int := if p 159 then d1324 p else d1322 p
theorem agree1325 (p q : Pattern) (h : Agree support p q) : d1325 p = d1325 q := by
  simp only [d1325, h 159 (by decide), agree1324 p q h, agree1322 p q h]
theorem nonnegative1325 (p : Pattern) : 0 ≤ d1325 p :=
  nonnegative_ite (p 159) (nonnegative1324 p) (nonnegative1322 p)
def d1326 (p : Pattern) : Int := if p 160 then d0 p else d1323 p
theorem agree1326 (p q : Pattern) (h : Agree support p q) : d1326 p = d1326 q := by
  simp only [d1326, h 160 (by decide), agree0 p q h, agree1323 p q h]
theorem nonnegative1326 (p : Pattern) : 0 ≤ d1326 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative1323 p)
def d1327 (p : Pattern) : Int := if p 159 then d1326 p else d1324 p
theorem agree1327 (p q : Pattern) (h : Agree support p q) : d1327 p = d1327 q := by
  simp only [d1327, h 159 (by decide), agree1326 p q h, agree1324 p q h]
theorem nonnegative1327 (p : Pattern) : 0 ≤ d1327 p :=
  nonnegative_ite (p 159) (nonnegative1326 p) (nonnegative1324 p)
def d1328 (p : Pattern) : Int := if p 158 then d1327 p else d1325 p
theorem agree1328 (p q : Pattern) (h : Agree support p q) : d1328 p = d1328 q := by
  simp only [d1328, h 158 (by decide), agree1327 p q h, agree1325 p q h]
theorem nonnegative1328 (p : Pattern) : 0 ≤ d1328 p :=
  nonnegative_ite (p 158) (nonnegative1327 p) (nonnegative1325 p)
def d1329 (p : Pattern) : Int := if p 159 then d0 p else d1326 p
theorem agree1329 (p q : Pattern) (h : Agree support p q) : d1329 p = d1329 q := by
  simp only [d1329, h 159 (by decide), agree0 p q h, agree1326 p q h]
theorem nonnegative1329 (p : Pattern) : 0 ≤ d1329 p :=
  nonnegative_ite (p 159) (nonnegative0 p) (nonnegative1326 p)
def d1330 (p : Pattern) : Int := if p 158 then d1329 p else d1327 p
theorem agree1330 (p q : Pattern) (h : Agree support p q) : d1330 p = d1330 q := by
  simp only [d1330, h 158 (by decide), agree1329 p q h, agree1327 p q h]
theorem nonnegative1330 (p : Pattern) : 0 ≤ d1330 p :=
  nonnegative_ite (p 158) (nonnegative1329 p) (nonnegative1327 p)
def d1331 (p : Pattern) : Int := if p 141 then d1330 p else d1328 p
theorem agree1331 (p q : Pattern) (h : Agree support p q) : d1331 p = d1331 q := by
  simp only [d1331, h 141 (by decide), agree1330 p q h, agree1328 p q h]
theorem nonnegative1331 (p : Pattern) : 0 ≤ d1331 p :=
  nonnegative_ite (p 141) (nonnegative1330 p) (nonnegative1328 p)
def d1332 (p : Pattern) : Int := if p 158 then d0 p else d1329 p
theorem agree1332 (p q : Pattern) (h : Agree support p q) : d1332 p = d1332 q := by
  simp only [d1332, h 158 (by decide), agree0 p q h, agree1329 p q h]
theorem nonnegative1332 (p : Pattern) : 0 ≤ d1332 p :=
  nonnegative_ite (p 158) (nonnegative0 p) (nonnegative1329 p)
def d1333 (p : Pattern) : Int := if p 141 then d1332 p else d1330 p
theorem agree1333 (p q : Pattern) (h : Agree support p q) : d1333 p = d1333 q := by
  simp only [d1333, h 141 (by decide), agree1332 p q h, agree1330 p q h]
theorem nonnegative1333 (p : Pattern) : 0 ≤ d1333 p :=
  nonnegative_ite (p 141) (nonnegative1332 p) (nonnegative1330 p)
def d1334 (p : Pattern) : Int := if p 134 then d1333 p else d1331 p
theorem agree1334 (p q : Pattern) (h : Agree support p q) : d1334 p = d1334 q := by
  simp only [d1334, h 134 (by decide), agree1333 p q h, agree1331 p q h]
theorem nonnegative1334 (p : Pattern) : 0 ≤ d1334 p :=
  nonnegative_ite (p 134) (nonnegative1333 p) (nonnegative1331 p)
def d1335 (p : Pattern) : Int := if p 141 then d0 p else d1332 p
theorem agree1335 (p q : Pattern) (h : Agree support p q) : d1335 p = d1335 q := by
  simp only [d1335, h 141 (by decide), agree0 p q h, agree1332 p q h]
theorem nonnegative1335 (p : Pattern) : 0 ≤ d1335 p :=
  nonnegative_ite (p 141) (nonnegative0 p) (nonnegative1332 p)
def d1336 (p : Pattern) : Int := if p 134 then d1335 p else d1333 p
theorem agree1336 (p q : Pattern) (h : Agree support p q) : d1336 p = d1336 q := by
  simp only [d1336, h 134 (by decide), agree1335 p q h, agree1333 p q h]
theorem nonnegative1336 (p : Pattern) : 0 ≤ d1336 p :=
  nonnegative_ite (p 134) (nonnegative1335 p) (nonnegative1333 p)
def d1337 (p : Pattern) : Int := if p 133 then d1336 p else d1334 p
theorem agree1337 (p q : Pattern) (h : Agree support p q) : d1337 p = d1337 q := by
  simp only [d1337, h 133 (by decide), agree1336 p q h, agree1334 p q h]
theorem nonnegative1337 (p : Pattern) : 0 ≤ d1337 p :=
  nonnegative_ite (p 133) (nonnegative1336 p) (nonnegative1334 p)
def d1338 (p : Pattern) : Int := if p 134 then d0 p else d1335 p
theorem agree1338 (p q : Pattern) (h : Agree support p q) : d1338 p = d1338 q := by
  simp only [d1338, h 134 (by decide), agree0 p q h, agree1335 p q h]
theorem nonnegative1338 (p : Pattern) : 0 ≤ d1338 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative1335 p)
def d1339 (p : Pattern) : Int := if p 133 then d1338 p else d1336 p
theorem agree1339 (p q : Pattern) (h : Agree support p q) : d1339 p = d1339 q := by
  simp only [d1339, h 133 (by decide), agree1338 p q h, agree1336 p q h]
theorem nonnegative1339 (p : Pattern) : 0 ≤ d1339 p :=
  nonnegative_ite (p 133) (nonnegative1338 p) (nonnegative1336 p)
def d1340 (p : Pattern) : Int := if p 132 then d1339 p else d1337 p
theorem agree1340 (p q : Pattern) (h : Agree support p q) : d1340 p = d1340 q := by
  simp only [d1340, h 132 (by decide), agree1339 p q h, agree1337 p q h]
theorem nonnegative1340 (p : Pattern) : 0 ≤ d1340 p :=
  nonnegative_ite (p 132) (nonnegative1339 p) (nonnegative1337 p)
def d1341 (p : Pattern) : Int := if p 133 then d0 p else d1338 p
theorem agree1341 (p q : Pattern) (h : Agree support p q) : d1341 p = d1341 q := by
  simp only [d1341, h 133 (by decide), agree0 p q h, agree1338 p q h]
theorem nonnegative1341 (p : Pattern) : 0 ≤ d1341 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative1338 p)
def d1342 (p : Pattern) : Int := if p 132 then d1341 p else d1339 p
theorem agree1342 (p q : Pattern) (h : Agree support p q) : d1342 p = d1342 q := by
  simp only [d1342, h 132 (by decide), agree1341 p q h, agree1339 p q h]
theorem nonnegative1342 (p : Pattern) : 0 ≤ d1342 p :=
  nonnegative_ite (p 132) (nonnegative1341 p) (nonnegative1339 p)
def d1343 (p : Pattern) : Int := if p 108 then d1342 p else d1340 p
theorem agree1343 (p q : Pattern) (h : Agree support p q) : d1343 p = d1343 q := by
  simp only [d1343, h 108 (by decide), agree1342 p q h, agree1340 p q h]
theorem nonnegative1343 (p : Pattern) : 0 ≤ d1343 p :=
  nonnegative_ite (p 108) (nonnegative1342 p) (nonnegative1340 p)
def d1344 (p : Pattern) : Int := if p 192 then d1237 p else d6 p
theorem agree1344 (p q : Pattern) (h : Agree support p q) : d1344 p = d1344 q := by
  simp only [d1344, h 192 (by decide), agree1237 p q h, agree6 p q h]
theorem nonnegative1344 (p : Pattern) : 0 ≤ d1344 p :=
  nonnegative_ite (p 192) (nonnegative1237 p) (nonnegative6 p)
def d1345 (p : Pattern) : Int := if p 187 then d5 p else d1344 p
theorem agree1345 (p q : Pattern) (h : Agree support p q) : d1345 p = d1345 q := by
  simp only [d1345, h 187 (by decide), agree5 p q h, agree1344 p q h]
theorem nonnegative1345 (p : Pattern) : 0 ≤ d1345 p :=
  nonnegative_ite (p 187) (nonnegative5 p) (nonnegative1344 p)
def d1346 (p : Pattern) : Int := if p 186 then d5 p else d1345 p
theorem agree1346 (p q : Pattern) (h : Agree support p q) : d1346 p = d1346 q := by
  simp only [d1346, h 186 (by decide), agree5 p q h, agree1345 p q h]
theorem nonnegative1346 (p : Pattern) : 0 ≤ d1346 p :=
  nonnegative_ite (p 186) (nonnegative5 p) (nonnegative1345 p)
def d1347 (p : Pattern) : Int := if p 160 then d5 p else d1346 p
theorem agree1347 (p q : Pattern) (h : Agree support p q) : d1347 p = d1347 q := by
  simp only [d1347, h 160 (by decide), agree5 p q h, agree1346 p q h]
theorem nonnegative1347 (p : Pattern) : 0 ≤ d1347 p :=
  nonnegative_ite (p 160) (nonnegative5 p) (nonnegative1346 p)
def d1348 (p : Pattern) : Int := if p 159 then d5 p else d1347 p
theorem agree1348 (p q : Pattern) (h : Agree support p q) : d1348 p = d1348 q := by
  simp only [d1348, h 159 (by decide), agree5 p q h, agree1347 p q h]
theorem nonnegative1348 (p : Pattern) : 0 ≤ d1348 p :=
  nonnegative_ite (p 159) (nonnegative5 p) (nonnegative1347 p)
def d1349 (p : Pattern) : Int := if p 158 then d5 p else d1348 p
theorem agree1349 (p q : Pattern) (h : Agree support p q) : d1349 p = d1349 q := by
  simp only [d1349, h 158 (by decide), agree5 p q h, agree1348 p q h]
theorem nonnegative1349 (p : Pattern) : 0 ≤ d1349 p :=
  nonnegative_ite (p 158) (nonnegative5 p) (nonnegative1348 p)
def d1350 (p : Pattern) : Int := if p 134 then d5 p else d1349 p
theorem agree1350 (p q : Pattern) (h : Agree support p q) : d1350 p = d1350 q := by
  simp only [d1350, h 134 (by decide), agree5 p q h, agree1349 p q h]
theorem nonnegative1350 (p : Pattern) : 0 ≤ d1350 p :=
  nonnegative_ite (p 134) (nonnegative5 p) (nonnegative1349 p)
def d1351 (p : Pattern) : Int := if p 133 then d5 p else d1350 p
theorem agree1351 (p q : Pattern) (h : Agree support p q) : d1351 p = d1351 q := by
  simp only [d1351, h 133 (by decide), agree5 p q h, agree1350 p q h]
theorem nonnegative1351 (p : Pattern) : 0 ≤ d1351 p :=
  nonnegative_ite (p 133) (nonnegative5 p) (nonnegative1350 p)
def d1352 (p : Pattern) : Int := if p 132 then d5 p else d1351 p
theorem agree1352 (p q : Pattern) (h : Agree support p q) : d1352 p = d1352 q := by
  simp only [d1352, h 132 (by decide), agree5 p q h, agree1351 p q h]
theorem nonnegative1352 (p : Pattern) : 0 ≤ d1352 p :=
  nonnegative_ite (p 132) (nonnegative5 p) (nonnegative1351 p)
def d1353 (p : Pattern) : Int := if p 108 then d5 p else d1352 p
theorem agree1353 (p q : Pattern) (h : Agree support p q) : d1353 p = d1353 q := by
  simp only [d1353, h 108 (by decide), agree5 p q h, agree1352 p q h]
theorem nonnegative1353 (p : Pattern) : 0 ≤ d1353 p :=
  nonnegative_ite (p 108) (nonnegative5 p) (nonnegative1352 p)
end NetHack.Sokoban12CostPartition
