/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1440 (p : Pattern) : Int := if p 161 then d1439 p else d111 p
theorem agree1440 (p q : Pattern) (h : Agree support p q) : d1440 p = d1440 q := by
  simp only [d1440, h 161 (by decide), agree1439 p q h, agree111 p q h]
theorem nonnegative1440 (p : Pattern) : 0 ≤ d1440 p :=
  nonnegative_ite (p 161) (nonnegative1439 p) (nonnegative111 p)
def d1441 (p : Pattern) : Int := if p 162 then d126 p else d118 p
theorem agree1441 (p q : Pattern) (h : Agree support p q) : d1441 p = d1441 q := by
  simp only [d1441, h 162 (by decide), agree126 p q h, agree118 p q h]
theorem nonnegative1441 (p : Pattern) : 0 ≤ d1441 p :=
  nonnegative_ite (p 162) (nonnegative126 p) (nonnegative118 p)
def d1442 (p : Pattern) : Int := if p 161 then d129 p else d1441 p
theorem agree1442 (p q : Pattern) (h : Agree support p q) : d1442 p = d1442 q := by
  simp only [d1442, h 161 (by decide), agree129 p q h, agree1441 p q h]
theorem nonnegative1442 (p : Pattern) : 0 ≤ d1442 p :=
  nonnegative_ite (p 161) (nonnegative129 p) (nonnegative1441 p)
def d1443 (p : Pattern) : Int := if p 160 then d1442 p else d1440 p
theorem agree1443 (p q : Pattern) (h : Agree support p q) : d1443 p = d1443 q := by
  simp only [d1443, h 160 (by decide), agree1442 p q h, agree1440 p q h]
theorem nonnegative1443 (p : Pattern) : 0 ≤ d1443 p :=
  nonnegative_ite (p 160) (nonnegative1442 p) (nonnegative1440 p)
def d1444 (p : Pattern) : Int := if p 162 then d1284 p else d133 p
theorem agree1444 (p q : Pattern) (h : Agree support p q) : d1444 p = d1444 q := by
  simp only [d1444, h 162 (by decide), agree1284 p q h, agree133 p q h]
theorem nonnegative1444 (p : Pattern) : 0 ≤ d1444 p :=
  nonnegative_ite (p 162) (nonnegative1284 p) (nonnegative133 p)
def d1445 (p : Pattern) : Int := if p 161 then d1051 p else d1444 p
theorem agree1445 (p q : Pattern) (h : Agree support p q) : d1445 p = d1445 q := by
  simp only [d1445, h 161 (by decide), agree1051 p q h, agree1444 p q h]
theorem nonnegative1445 (p : Pattern) : 0 ≤ d1445 p :=
  nonnegative_ite (p 161) (nonnegative1051 p) (nonnegative1444 p)
def d1446 (p : Pattern) : Int := if p 162 then d1290 p else d862 p
theorem agree1446 (p q : Pattern) (h : Agree support p q) : d1446 p = d1446 q := by
  simp only [d1446, h 162 (by decide), agree1290 p q h, agree862 p q h]
theorem nonnegative1446 (p : Pattern) : 0 ≤ d1446 p :=
  nonnegative_ite (p 162) (nonnegative1290 p) (nonnegative862 p)
def d1447 (p : Pattern) : Int := if p 161 then d1054 p else d1446 p
theorem agree1447 (p q : Pattern) (h : Agree support p q) : d1447 p = d1447 q := by
  simp only [d1447, h 161 (by decide), agree1054 p q h, agree1446 p q h]
theorem nonnegative1447 (p : Pattern) : 0 ≤ d1447 p :=
  nonnegative_ite (p 161) (nonnegative1054 p) (nonnegative1446 p)
def d1448 (p : Pattern) : Int := if p 160 then d1447 p else d1445 p
theorem agree1448 (p q : Pattern) (h : Agree support p q) : d1448 p = d1448 q := by
  simp only [d1448, h 160 (by decide), agree1447 p q h, agree1445 p q h]
theorem nonnegative1448 (p : Pattern) : 0 ≤ d1448 p :=
  nonnegative_ite (p 160) (nonnegative1447 p) (nonnegative1445 p)
def d1449 (p : Pattern) : Int := if p 141 then d1448 p else d1443 p
theorem agree1449 (p q : Pattern) (h : Agree support p q) : d1449 p = d1449 q := by
  simp only [d1449, h 141 (by decide), agree1448 p q h, agree1443 p q h]
theorem nonnegative1449 (p : Pattern) : 0 ≤ d1449 p :=
  nonnegative_ite (p 141) (nonnegative1448 p) (nonnegative1443 p)
def d1450 (p : Pattern) : Int := if p 162 then d112 p else d133 p
theorem agree1450 (p q : Pattern) (h : Agree support p q) : d1450 p = d1450 q := by
  simp only [d1450, h 162 (by decide), agree112 p q h, agree133 p q h]
theorem nonnegative1450 (p : Pattern) : 0 ≤ d1450 p :=
  nonnegative_ite (p 162) (nonnegative112 p) (nonnegative133 p)
def d1451 (p : Pattern) : Int := if p 161 then d1450 p else d111 p
theorem agree1451 (p q : Pattern) (h : Agree support p q) : d1451 p = d1451 q := by
  simp only [d1451, h 161 (by decide), agree1450 p q h, agree111 p q h]
theorem nonnegative1451 (p : Pattern) : 0 ≤ d1451 p :=
  nonnegative_ite (p 161) (nonnegative1450 p) (nonnegative111 p)
def d1452 (p : Pattern) : Int := if p 160 then d1062 p else d1451 p
theorem agree1452 (p q : Pattern) (h : Agree support p q) : d1452 p = d1452 q := by
  simp only [d1452, h 160 (by decide), agree1062 p q h, agree1451 p q h]
theorem nonnegative1452 (p : Pattern) : 0 ≤ d1452 p :=
  nonnegative_ite (p 160) (nonnegative1062 p) (nonnegative1451 p)
def d1453 (p : Pattern) : Int := if p 162 then d1289 p else d133 p
theorem agree1453 (p q : Pattern) (h : Agree support p q) : d1453 p = d1453 q := by
  simp only [d1453, h 162 (by decide), agree1289 p q h, agree133 p q h]
theorem nonnegative1453 (p : Pattern) : 0 ≤ d1453 p :=
  nonnegative_ite (p 162) (nonnegative1289 p) (nonnegative133 p)
def d1454 (p : Pattern) : Int := if p 161 then d1064 p else d1453 p
theorem agree1454 (p q : Pattern) (h : Agree support p q) : d1454 p = d1454 q := by
  simp only [d1454, h 161 (by decide), agree1064 p q h, agree1453 p q h]
theorem nonnegative1454 (p : Pattern) : 0 ≤ d1454 p :=
  nonnegative_ite (p 161) (nonnegative1064 p) (nonnegative1453 p)
def d1455 (p : Pattern) : Int := if p 160 then d1066 p else d1454 p
theorem agree1455 (p q : Pattern) (h : Agree support p q) : d1455 p = d1455 q := by
  simp only [d1455, h 160 (by decide), agree1066 p q h, agree1454 p q h]
theorem nonnegative1455 (p : Pattern) : 0 ≤ d1455 p :=
  nonnegative_ite (p 160) (nonnegative1066 p) (nonnegative1454 p)
def d1456 (p : Pattern) : Int := if p 141 then d1455 p else d1452 p
theorem agree1456 (p q : Pattern) (h : Agree support p q) : d1456 p = d1456 q := by
  simp only [d1456, h 141 (by decide), agree1455 p q h, agree1452 p q h]
theorem nonnegative1456 (p : Pattern) : 0 ≤ d1456 p :=
  nonnegative_ite (p 141) (nonnegative1455 p) (nonnegative1452 p)
def d1457 (p : Pattern) : Int := if p 138 then d1456 p else d1449 p
theorem agree1457 (p q : Pattern) (h : Agree support p q) : d1457 p = d1457 q := by
  simp only [d1457, h 138 (by decide), agree1456 p q h, agree1449 p q h]
theorem nonnegative1457 (p : Pattern) : 0 ≤ d1457 p :=
  nonnegative_ite (p 138) (nonnegative1456 p) (nonnegative1449 p)
def d1458 (p : Pattern) : Int := if p 138 then d162 p else d1456 p
theorem agree1458 (p q : Pattern) (h : Agree support p q) : d1458 p = d1458 q := by
  simp only [d1458, h 138 (by decide), agree162 p q h, agree1456 p q h]
theorem nonnegative1458 (p : Pattern) : 0 ≤ d1458 p :=
  nonnegative_ite (p 138) (nonnegative162 p) (nonnegative1456 p)
def d1459 (p : Pattern) : Int := if p 116 then d1458 p else d1457 p
theorem agree1459 (p q : Pattern) (h : Agree support p q) : d1459 p = d1459 q := by
  simp only [d1459, h 116 (by decide), agree1458 p q h, agree1457 p q h]
theorem nonnegative1459 (p : Pattern) : 0 ≤ d1459 p :=
  nonnegative_ite (p 116) (nonnegative1458 p) (nonnegative1457 p)
def d1460 (p : Pattern) : Int := if p 161 then d1051 p else d1453 p
theorem agree1460 (p q : Pattern) (h : Agree support p q) : d1460 p = d1460 q := by
  simp only [d1460, h 161 (by decide), agree1051 p q h, agree1453 p q h]
theorem nonnegative1460 (p : Pattern) : 0 ≤ d1460 p :=
  nonnegative_ite (p 161) (nonnegative1051 p) (nonnegative1453 p)
def d1461 (p : Pattern) : Int := if p 160 then d1447 p else d1460 p
theorem agree1461 (p q : Pattern) (h : Agree support p q) : d1461 p = d1461 q := by
  simp only [d1461, h 160 (by decide), agree1447 p q h, agree1460 p q h]
theorem nonnegative1461 (p : Pattern) : 0 ≤ d1461 p :=
  nonnegative_ite (p 160) (nonnegative1447 p) (nonnegative1460 p)
def d1462 (p : Pattern) : Int := if p 141 then d1461 p else d1443 p
theorem agree1462 (p q : Pattern) (h : Agree support p q) : d1462 p = d1462 q := by
  simp only [d1462, h 141 (by decide), agree1461 p q h, agree1443 p q h]
theorem nonnegative1462 (p : Pattern) : 0 ≤ d1462 p :=
  nonnegative_ite (p 141) (nonnegative1461 p) (nonnegative1443 p)
def d1463 (p : Pattern) : Int := if p 138 then d1456 p else d1462 p
theorem agree1463 (p q : Pattern) (h : Agree support p q) : d1463 p = d1463 q := by
  simp only [d1463, h 138 (by decide), agree1456 p q h, agree1462 p q h]
theorem nonnegative1463 (p : Pattern) : 0 ≤ d1463 p :=
  nonnegative_ite (p 138) (nonnegative1456 p) (nonnegative1462 p)
def d1464 (p : Pattern) : Int := if p 138 then d12 p else d1456 p
theorem agree1464 (p q : Pattern) (h : Agree support p q) : d1464 p = d1464 q := by
  simp only [d1464, h 138 (by decide), agree12 p q h, agree1456 p q h]
theorem nonnegative1464 (p : Pattern) : 0 ≤ d1464 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1456 p)
def d1465 (p : Pattern) : Int := if p 116 then d1464 p else d1463 p
theorem agree1465 (p q : Pattern) (h : Agree support p q) : d1465 p = d1465 q := by
  simp only [d1465, h 116 (by decide), agree1464 p q h, agree1463 p q h]
theorem nonnegative1465 (p : Pattern) : 0 ≤ d1465 p :=
  nonnegative_ite (p 116) (nonnegative1464 p) (nonnegative1463 p)
def d1466 (p : Pattern) : Int := if p 115 then d1465 p else d1459 p
theorem agree1466 (p q : Pattern) (h : Agree support p q) : d1466 p = d1466 q := by
  simp only [d1466, h 115 (by decide), agree1465 p q h, agree1459 p q h]
theorem nonnegative1466 (p : Pattern) : 0 ≤ d1466 p :=
  nonnegative_ite (p 115) (nonnegative1465 p) (nonnegative1459 p)
def d1467 (p : Pattern) : Int := if p 71 then d1466 p else d1430 p
theorem agree1467 (p q : Pattern) (h : Agree support p q) : d1467 p = d1467 q := by
  simp only [d1467, h 71 (by decide), agree1466 p q h, agree1430 p q h]
theorem nonnegative1467 (p : Pattern) : 0 ≤ d1467 p :=
  nonnegative_ite (p 71) (nonnegative1466 p) (nonnegative1430 p)
def d1468 (p : Pattern) : Int := if p 49 then d1467 p else d1438 p
theorem agree1468 (p q : Pattern) (h : Agree support p q) : d1468 p = d1468 q := by
  simp only [d1468, h 49 (by decide), agree1467 p q h, agree1438 p q h]
theorem nonnegative1468 (p : Pattern) : 0 ≤ d1468 p :=
  nonnegative_ite (p 49) (nonnegative1467 p) (nonnegative1438 p)
def d1469 (p : Pattern) : Int := if p 162 then d1181 p else d53 p
theorem agree1469 (p q : Pattern) (h : Agree support p q) : d1469 p = d1469 q := by
  simp only [d1469, h 162 (by decide), agree1181 p q h, agree53 p q h]
theorem nonnegative1469 (p : Pattern) : 0 ≤ d1469 p :=
  nonnegative_ite (p 162) (nonnegative1181 p) (nonnegative53 p)
def d1470 (p : Pattern) : Int := if p 161 then d1417 p else d1469 p
theorem agree1470 (p q : Pattern) (h : Agree support p q) : d1470 p = d1470 q := by
  simp only [d1470, h 161 (by decide), agree1417 p q h, agree1469 p q h]
theorem nonnegative1470 (p : Pattern) : 0 ≤ d1470 p :=
  nonnegative_ite (p 161) (nonnegative1417 p) (nonnegative1469 p)
def d1471 (p : Pattern) : Int := if p 160 then d1101 p else d1470 p
theorem agree1471 (p q : Pattern) (h : Agree support p q) : d1471 p = d1471 q := by
  simp only [d1471, h 160 (by decide), agree1101 p q h, agree1470 p q h]
theorem nonnegative1471 (p : Pattern) : 0 ≤ d1471 p :=
  nonnegative_ite (p 160) (nonnegative1101 p) (nonnegative1470 p)
def d1472 (p : Pattern) : Int := if p 141 then d1471 p else d1415 p
theorem agree1472 (p q : Pattern) (h : Agree support p q) : d1472 p = d1472 q := by
  simp only [d1472, h 141 (by decide), agree1471 p q h, agree1415 p q h]
theorem nonnegative1472 (p : Pattern) : 0 ≤ d1472 p :=
  nonnegative_ite (p 141) (nonnegative1471 p) (nonnegative1415 p)
def d1473 (p : Pattern) : Int := if p 138 then d1472 p else d1426 p
theorem agree1473 (p q : Pattern) (h : Agree support p q) : d1473 p = d1473 q := by
  simp only [d1473, h 138 (by decide), agree1472 p q h, agree1426 p q h]
theorem nonnegative1473 (p : Pattern) : 0 ≤ d1473 p :=
  nonnegative_ite (p 138) (nonnegative1472 p) (nonnegative1426 p)
def d1474 (p : Pattern) : Int := if p 138 then d12 p else d1472 p
theorem agree1474 (p q : Pattern) (h : Agree support p q) : d1474 p = d1474 q := by
  simp only [d1474, h 138 (by decide), agree12 p q h, agree1472 p q h]
theorem nonnegative1474 (p : Pattern) : 0 ≤ d1474 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1472 p)
def d1475 (p : Pattern) : Int := if p 116 then d1474 p else d1473 p
theorem agree1475 (p q : Pattern) (h : Agree support p q) : d1475 p = d1475 q := by
  simp only [d1475, h 116 (by decide), agree1474 p q h, agree1473 p q h]
theorem nonnegative1475 (p : Pattern) : 0 ≤ d1475 p :=
  nonnegative_ite (p 116) (nonnegative1474 p) (nonnegative1473 p)
def d1476 (p : Pattern) : Int := if p 115 then d1475 p else d1436 p
theorem agree1476 (p q : Pattern) (h : Agree support p q) : d1476 p = d1476 q := by
  simp only [d1476, h 115 (by decide), agree1475 p q h, agree1436 p q h]
theorem nonnegative1476 (p : Pattern) : 0 ≤ d1476 p :=
  nonnegative_ite (p 115) (nonnegative1475 p) (nonnegative1436 p)
def d1477 (p : Pattern) : Int := if p 71 then d1476 p else d1430 p
theorem agree1477 (p q : Pattern) (h : Agree support p q) : d1477 p = d1477 q := by
  simp only [d1477, h 71 (by decide), agree1476 p q h, agree1430 p q h]
theorem nonnegative1477 (p : Pattern) : 0 ≤ d1477 p :=
  nonnegative_ite (p 71) (nonnegative1476 p) (nonnegative1430 p)
def d1478 (p : Pattern) : Int := if p 116 then d1458 p else d1463 p
theorem agree1478 (p q : Pattern) (h : Agree support p q) : d1478 p = d1478 q := by
  simp only [d1478, h 116 (by decide), agree1458 p q h, agree1463 p q h]
theorem nonnegative1478 (p : Pattern) : 0 ≤ d1478 p :=
  nonnegative_ite (p 116) (nonnegative1458 p) (nonnegative1463 p)
def d1479 (p : Pattern) : Int := if p 162 then d112 p else d291 p
theorem agree1479 (p q : Pattern) (h : Agree support p q) : d1479 p = d1479 q := by
  simp only [d1479, h 162 (by decide), agree112 p q h, agree291 p q h]
theorem nonnegative1479 (p : Pattern) : 0 ≤ d1479 p :=
  nonnegative_ite (p 162) (nonnegative112 p) (nonnegative291 p)
def d1480 (p : Pattern) : Int := if p 161 then d1479 p else d111 p
theorem agree1480 (p q : Pattern) (h : Agree support p q) : d1480 p = d1480 q := by
  simp only [d1480, h 161 (by decide), agree1479 p q h, agree111 p q h]
theorem nonnegative1480 (p : Pattern) : 0 ≤ d1480 p :=
  nonnegative_ite (p 161) (nonnegative1479 p) (nonnegative111 p)
def d1481 (p : Pattern) : Int := if p 162 then d275 p else d269 p
theorem agree1481 (p q : Pattern) (h : Agree support p q) : d1481 p = d1481 q := by
  simp only [d1481, h 162 (by decide), agree275 p q h, agree269 p q h]
theorem nonnegative1481 (p : Pattern) : 0 ≤ d1481 p :=
  nonnegative_ite (p 162) (nonnegative275 p) (nonnegative269 p)
def d1482 (p : Pattern) : Int := if p 161 then d279 p else d1481 p
theorem agree1482 (p q : Pattern) (h : Agree support p q) : d1482 p = d1482 q := by
  simp only [d1482, h 161 (by decide), agree279 p q h, agree1481 p q h]
theorem nonnegative1482 (p : Pattern) : 0 ≤ d1482 p :=
  nonnegative_ite (p 161) (nonnegative279 p) (nonnegative1481 p)
def d1483 (p : Pattern) : Int := if p 160 then d1482 p else d1480 p
theorem agree1483 (p q : Pattern) (h : Agree support p q) : d1483 p = d1483 q := by
  simp only [d1483, h 160 (by decide), agree1482 p q h, agree1480 p q h]
theorem nonnegative1483 (p : Pattern) : 0 ≤ d1483 p :=
  nonnegative_ite (p 160) (nonnegative1482 p) (nonnegative1480 p)
def d1484 (p : Pattern) : Int := if p 161 then d1124 p else d1453 p
theorem agree1484 (p q : Pattern) (h : Agree support p q) : d1484 p = d1484 q := by
  simp only [d1484, h 161 (by decide), agree1124 p q h, agree1453 p q h]
theorem nonnegative1484 (p : Pattern) : 0 ≤ d1484 p :=
  nonnegative_ite (p 161) (nonnegative1124 p) (nonnegative1453 p)
def d1485 (p : Pattern) : Int := if p 162 then d1375 p else d925 p
theorem agree1485 (p q : Pattern) (h : Agree support p q) : d1485 p = d1485 q := by
  simp only [d1485, h 162 (by decide), agree1375 p q h, agree925 p q h]
theorem nonnegative1485 (p : Pattern) : 0 ≤ d1485 p :=
  nonnegative_ite (p 162) (nonnegative1375 p) (nonnegative925 p)
def d1486 (p : Pattern) : Int := if p 161 then d1129 p else d1485 p
theorem agree1486 (p q : Pattern) (h : Agree support p q) : d1486 p = d1486 q := by
  simp only [d1486, h 161 (by decide), agree1129 p q h, agree1485 p q h]
theorem nonnegative1486 (p : Pattern) : 0 ≤ d1486 p :=
  nonnegative_ite (p 161) (nonnegative1129 p) (nonnegative1485 p)
def d1487 (p : Pattern) : Int := if p 160 then d1486 p else d1484 p
theorem agree1487 (p q : Pattern) (h : Agree support p q) : d1487 p = d1487 q := by
  simp only [d1487, h 160 (by decide), agree1486 p q h, agree1484 p q h]
theorem nonnegative1487 (p : Pattern) : 0 ≤ d1487 p :=
  nonnegative_ite (p 160) (nonnegative1486 p) (nonnegative1484 p)
def d1488 (p : Pattern) : Int := if p 141 then d1487 p else d1483 p
theorem agree1488 (p q : Pattern) (h : Agree support p q) : d1488 p = d1488 q := by
  simp only [d1488, h 141 (by decide), agree1487 p q h, agree1483 p q h]
theorem nonnegative1488 (p : Pattern) : 0 ≤ d1488 p :=
  nonnegative_ite (p 141) (nonnegative1487 p) (nonnegative1483 p)
def d1489 (p : Pattern) : Int := if p 162 then d293 p else d105 p
theorem agree1489 (p q : Pattern) (h : Agree support p q) : d1489 p = d1489 q := by
  simp only [d1489, h 162 (by decide), agree293 p q h, agree105 p q h]
theorem nonnegative1489 (p : Pattern) : 0 ≤ d1489 p :=
  nonnegative_ite (p 162) (nonnegative293 p) (nonnegative105 p)
def d1490 (p : Pattern) : Int := if p 162 then d278 p else d1133 p
theorem agree1490 (p q : Pattern) (h : Agree support p q) : d1490 p = d1490 q := by
  simp only [d1490, h 162 (by decide), agree278 p q h, agree1133 p q h]
theorem nonnegative1490 (p : Pattern) : 0 ≤ d1490 p :=
  nonnegative_ite (p 162) (nonnegative278 p) (nonnegative1133 p)
def d1491 (p : Pattern) : Int := if p 161 then d1490 p else d1489 p
theorem agree1491 (p q : Pattern) (h : Agree support p q) : d1491 p = d1491 q := by
  simp only [d1491, h 161 (by decide), agree1490 p q h, agree1489 p q h]
theorem nonnegative1491 (p : Pattern) : 0 ≤ d1491 p :=
  nonnegative_ite (p 161) (nonnegative1490 p) (nonnegative1489 p)
def d1492 (p : Pattern) : Int := if p 160 then d1062 p else d1491 p
theorem agree1492 (p q : Pattern) (h : Agree support p q) : d1492 p = d1492 q := by
  simp only [d1492, h 160 (by decide), agree1062 p q h, agree1491 p q h]
theorem nonnegative1492 (p : Pattern) : 0 ≤ d1492 p :=
  nonnegative_ite (p 160) (nonnegative1062 p) (nonnegative1491 p)
def d1493 (p : Pattern) : Int := if p 162 then d1385 p else d132 p
theorem agree1493 (p q : Pattern) (h : Agree support p q) : d1493 p = d1493 q := by
  simp only [d1493, h 162 (by decide), agree1385 p q h, agree132 p q h]
theorem nonnegative1493 (p : Pattern) : 0 ≤ d1493 p :=
  nonnegative_ite (p 162) (nonnegative1385 p) (nonnegative132 p)
def d1494 (p : Pattern) : Int := if p 161 then d1138 p else d1493 p
theorem agree1494 (p q : Pattern) (h : Agree support p q) : d1494 p = d1494 q := by
  simp only [d1494, h 161 (by decide), agree1138 p q h, agree1493 p q h]
theorem nonnegative1494 (p : Pattern) : 0 ≤ d1494 p :=
  nonnegative_ite (p 161) (nonnegative1138 p) (nonnegative1493 p)
def d1495 (p : Pattern) : Int := if p 160 then d1141 p else d1494 p
theorem agree1495 (p q : Pattern) (h : Agree support p q) : d1495 p = d1495 q := by
  simp only [d1495, h 160 (by decide), agree1141 p q h, agree1494 p q h]
theorem nonnegative1495 (p : Pattern) : 0 ≤ d1495 p :=
  nonnegative_ite (p 160) (nonnegative1141 p) (nonnegative1494 p)
def d1496 (p : Pattern) : Int := if p 141 then d1495 p else d1492 p
theorem agree1496 (p q : Pattern) (h : Agree support p q) : d1496 p = d1496 q := by
  simp only [d1496, h 141 (by decide), agree1495 p q h, agree1492 p q h]
theorem nonnegative1496 (p : Pattern) : 0 ≤ d1496 p :=
  nonnegative_ite (p 141) (nonnegative1495 p) (nonnegative1492 p)
def d1497 (p : Pattern) : Int := if p 138 then d1496 p else d1488 p
theorem agree1497 (p q : Pattern) (h : Agree support p q) : d1497 p = d1497 q := by
  simp only [d1497, h 138 (by decide), agree1496 p q h, agree1488 p q h]
theorem nonnegative1497 (p : Pattern) : 0 ≤ d1497 p :=
  nonnegative_ite (p 138) (nonnegative1496 p) (nonnegative1488 p)
def d1498 (p : Pattern) : Int := if p 138 then d12 p else d1496 p
theorem agree1498 (p q : Pattern) (h : Agree support p q) : d1498 p = d1498 q := by
  simp only [d1498, h 138 (by decide), agree12 p q h, agree1496 p q h]
theorem nonnegative1498 (p : Pattern) : 0 ≤ d1498 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1496 p)
def d1499 (p : Pattern) : Int := if p 116 then d1498 p else d1497 p
theorem agree1499 (p q : Pattern) (h : Agree support p q) : d1499 p = d1499 q := by
  simp only [d1499, h 116 (by decide), agree1498 p q h, agree1497 p q h]
theorem nonnegative1499 (p : Pattern) : 0 ≤ d1499 p :=
  nonnegative_ite (p 116) (nonnegative1498 p) (nonnegative1497 p)
def d1500 (p : Pattern) : Int := if p 115 then d1499 p else d1478 p
theorem agree1500 (p q : Pattern) (h : Agree support p q) : d1500 p = d1500 q := by
  simp only [d1500, h 115 (by decide), agree1499 p q h, agree1478 p q h]
theorem nonnegative1500 (p : Pattern) : 0 ≤ d1500 p :=
  nonnegative_ite (p 115) (nonnegative1499 p) (nonnegative1478 p)
def d1501 (p : Pattern) : Int := if p 71 then d1500 p else d1430 p
theorem agree1501 (p q : Pattern) (h : Agree support p q) : d1501 p = d1501 q := by
  simp only [d1501, h 71 (by decide), agree1500 p q h, agree1430 p q h]
theorem nonnegative1501 (p : Pattern) : 0 ≤ d1501 p :=
  nonnegative_ite (p 71) (nonnegative1500 p) (nonnegative1430 p)
def d1502 (p : Pattern) : Int := if p 49 then d1501 p else d1477 p
theorem agree1502 (p q : Pattern) (h : Agree support p q) : d1502 p = d1502 q := by
  simp only [d1502, h 49 (by decide), agree1501 p q h, agree1477 p q h]
theorem nonnegative1502 (p : Pattern) : 0 ≤ d1502 p :=
  nonnegative_ite (p 49) (nonnegative1501 p) (nonnegative1477 p)
def d1503 (p : Pattern) : Int := if p 48 then d1502 p else d1468 p
theorem agree1503 (p q : Pattern) (h : Agree support p q) : d1503 p = d1503 q := by
  simp only [d1503, h 48 (by decide), agree1502 p q h, agree1468 p q h]
theorem nonnegative1503 (p : Pattern) : 0 ≤ d1503 p :=
  nonnegative_ite (p 48) (nonnegative1502 p) (nonnegative1468 p)
def d1504 (p : Pattern) : Int := if p 182 then d324 p else d14 p
theorem agree1504 (p q : Pattern) (h : Agree support p q) : d1504 p = d1504 q := by
  simp only [d1504, h 182 (by decide), agree324 p q h, agree14 p q h]
theorem nonnegative1504 (p : Pattern) : 0 ≤ d1504 p :=
  nonnegative_ite (p 182) (nonnegative324 p) (nonnegative14 p)
def d1505 (p : Pattern) : Int := if p 182 then d336 p else d14 p
theorem agree1505 (p q : Pattern) (h : Agree support p q) : d1505 p = d1505 q := by
  simp only [d1505, h 182 (by decide), agree336 p q h, agree14 p q h]
theorem nonnegative1505 (p : Pattern) : 0 ≤ d1505 p :=
  nonnegative_ite (p 182) (nonnegative336 p) (nonnegative14 p)
def d1506 (p : Pattern) : Int := if p 163 then d1505 p else d1504 p
theorem agree1506 (p q : Pattern) (h : Agree support p q) : d1506 p = d1506 q := by
  simp only [d1506, h 163 (by decide), agree1505 p q h, agree1504 p q h]
theorem nonnegative1506 (p : Pattern) : 0 ≤ d1506 p :=
  nonnegative_ite (p 163) (nonnegative1505 p) (nonnegative1504 p)
def d1507 (p : Pattern) : Int := if p 182 then d343 p else d14 p
theorem agree1507 (p q : Pattern) (h : Agree support p q) : d1507 p = d1507 q := by
  simp only [d1507, h 182 (by decide), agree343 p q h, agree14 p q h]
theorem nonnegative1507 (p : Pattern) : 0 ≤ d1507 p :=
  nonnegative_ite (p 182) (nonnegative343 p) (nonnegative14 p)
def d1508 (p : Pattern) : Int := if p 163 then d43 p else d1507 p
theorem agree1508 (p q : Pattern) (h : Agree support p q) : d1508 p = d1508 q := by
  simp only [d1508, h 163 (by decide), agree43 p q h, agree1507 p q h]
theorem nonnegative1508 (p : Pattern) : 0 ≤ d1508 p :=
  nonnegative_ite (p 163) (nonnegative43 p) (nonnegative1507 p)
def d1509 (p : Pattern) : Int := if p 162 then d1508 p else d1506 p
theorem agree1509 (p q : Pattern) (h : Agree support p q) : d1509 p = d1509 q := by
  simp only [d1509, h 162 (by decide), agree1508 p q h, agree1506 p q h]
theorem nonnegative1509 (p : Pattern) : 0 ≤ d1509 p :=
  nonnegative_ite (p 162) (nonnegative1508 p) (nonnegative1506 p)
def d1510 (p : Pattern) : Int := if p 161 then d50 p else d1509 p
theorem agree1510 (p q : Pattern) (h : Agree support p q) : d1510 p = d1510 q := by
  simp only [d1510, h 161 (by decide), agree50 p q h, agree1509 p q h]
theorem nonnegative1510 (p : Pattern) : 0 ≤ d1510 p :=
  nonnegative_ite (p 161) (nonnegative50 p) (nonnegative1509 p)
def d1511 (p : Pattern) : Int := if p 162 then d47 p else d46 p
theorem agree1511 (p q : Pattern) (h : Agree support p q) : d1511 p = d1511 q := by
  simp only [d1511, h 162 (by decide), agree47 p q h, agree46 p q h]
theorem nonnegative1511 (p : Pattern) : 0 ≤ d1511 p :=
  nonnegative_ite (p 162) (nonnegative47 p) (nonnegative46 p)
def d1512 (p : Pattern) : Int := if p 161 then d50 p else d1511 p
theorem agree1512 (p q : Pattern) (h : Agree support p q) : d1512 p = d1512 q := by
  simp only [d1512, h 161 (by decide), agree50 p q h, agree1511 p q h]
theorem nonnegative1512 (p : Pattern) : 0 ≤ d1512 p :=
  nonnegative_ite (p 161) (nonnegative50 p) (nonnegative1511 p)
def d1513 (p : Pattern) : Int := if p 160 then d1512 p else d1510 p
theorem agree1513 (p q : Pattern) (h : Agree support p q) : d1513 p = d1513 q := by
  simp only [d1513, h 160 (by decide), agree1512 p q h, agree1510 p q h]
theorem nonnegative1513 (p : Pattern) : 0 ≤ d1513 p :=
  nonnegative_ite (p 160) (nonnegative1512 p) (nonnegative1510 p)
def d1514 (p : Pattern) : Int := if p 182 then d359 p else d14 p
theorem agree1514 (p q : Pattern) (h : Agree support p q) : d1514 p = d1514 q := by
  simp only [d1514, h 182 (by decide), agree359 p q h, agree14 p q h]
theorem nonnegative1514 (p : Pattern) : 0 ≤ d1514 p :=
  nonnegative_ite (p 182) (nonnegative359 p) (nonnegative14 p)
def d1515 (p : Pattern) : Int := if p 163 then d66 p else d1514 p
theorem agree1515 (p q : Pattern) (h : Agree support p q) : d1515 p = d1515 q := by
  simp only [d1515, h 163 (by decide), agree66 p q h, agree1514 p q h]
theorem nonnegative1515 (p : Pattern) : 0 ≤ d1515 p :=
  nonnegative_ite (p 163) (nonnegative66 p) (nonnegative1514 p)
def d1516 (p : Pattern) : Int := if p 162 then d68 p else d1515 p
theorem agree1516 (p q : Pattern) (h : Agree support p q) : d1516 p = d1516 q := by
  simp only [d1516, h 162 (by decide), agree68 p q h, agree1515 p q h]
theorem nonnegative1516 (p : Pattern) : 0 ≤ d1516 p :=
  nonnegative_ite (p 162) (nonnegative68 p) (nonnegative1515 p)
def d1517 (p : Pattern) : Int := if p 161 then d74 p else d1516 p
theorem agree1517 (p q : Pattern) (h : Agree support p q) : d1517 p = d1517 q := by
  simp only [d1517, h 161 (by decide), agree74 p q h, agree1516 p q h]
theorem nonnegative1517 (p : Pattern) : 0 ≤ d1517 p :=
  nonnegative_ite (p 161) (nonnegative74 p) (nonnegative1516 p)
def d1518 (p : Pattern) : Int := if p 163 then d66 p else d46 p
theorem agree1518 (p q : Pattern) (h : Agree support p q) : d1518 p = d1518 q := by
  simp only [d1518, h 163 (by decide), agree66 p q h, agree46 p q h]
theorem nonnegative1518 (p : Pattern) : 0 ≤ d1518 p :=
  nonnegative_ite (p 163) (nonnegative66 p) (nonnegative46 p)
def d1519 (p : Pattern) : Int := if p 162 then d68 p else d1518 p
theorem agree1519 (p q : Pattern) (h : Agree support p q) : d1519 p = d1519 q := by
  simp only [d1519, h 162 (by decide), agree68 p q h, agree1518 p q h]
theorem nonnegative1519 (p : Pattern) : 0 ≤ d1519 p :=
  nonnegative_ite (p 162) (nonnegative68 p) (nonnegative1518 p)
def d1520 (p : Pattern) : Int := if p 161 then d74 p else d1519 p
theorem agree1520 (p q : Pattern) (h : Agree support p q) : d1520 p = d1520 q := by
  simp only [d1520, h 161 (by decide), agree74 p q h, agree1519 p q h]
theorem nonnegative1520 (p : Pattern) : 0 ≤ d1520 p :=
  nonnegative_ite (p 161) (nonnegative74 p) (nonnegative1519 p)
def d1521 (p : Pattern) : Int := if p 160 then d1520 p else d1517 p
theorem agree1521 (p q : Pattern) (h : Agree support p q) : d1521 p = d1521 q := by
  simp only [d1521, h 160 (by decide), agree1520 p q h, agree1517 p q h]
theorem nonnegative1521 (p : Pattern) : 0 ≤ d1521 p :=
  nonnegative_ite (p 160) (nonnegative1520 p) (nonnegative1517 p)
def d1522 (p : Pattern) : Int := if p 141 then d1521 p else d1513 p
theorem agree1522 (p q : Pattern) (h : Agree support p q) : d1522 p = d1522 q := by
  simp only [d1522, h 141 (by decide), agree1521 p q h, agree1513 p q h]
theorem nonnegative1522 (p : Pattern) : 0 ≤ d1522 p :=
  nonnegative_ite (p 141) (nonnegative1521 p) (nonnegative1513 p)
def d1523 (p : Pattern) : Int := if p 161 then d12 p else d177 p
theorem agree1523 (p q : Pattern) (h : Agree support p q) : d1523 p = d1523 q := by
  simp only [d1523, h 161 (by decide), agree12 p q h, agree177 p q h]
theorem nonnegative1523 (p : Pattern) : 0 ≤ d1523 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative177 p)
def d1524 (p : Pattern) : Int := if p 160 then d1523 p else d1512 p
theorem agree1524 (p q : Pattern) (h : Agree support p q) : d1524 p = d1524 q := by
  simp only [d1524, h 160 (by decide), agree1523 p q h, agree1512 p q h]
theorem nonnegative1524 (p : Pattern) : 0 ≤ d1524 p :=
  nonnegative_ite (p 160) (nonnegative1523 p) (nonnegative1512 p)
def d1525 (p : Pattern) : Int := if p 161 then d12 p else d184 p
theorem agree1525 (p q : Pattern) (h : Agree support p q) : d1525 p = d1525 q := by
  simp only [d1525, h 161 (by decide), agree12 p q h, agree184 p q h]
theorem nonnegative1525 (p : Pattern) : 0 ≤ d1525 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative184 p)
def d1526 (p : Pattern) : Int := if p 160 then d1525 p else d1520 p
theorem agree1526 (p q : Pattern) (h : Agree support p q) : d1526 p = d1526 q := by
  simp only [d1526, h 160 (by decide), agree1525 p q h, agree1520 p q h]
theorem nonnegative1526 (p : Pattern) : 0 ≤ d1526 p :=
  nonnegative_ite (p 160) (nonnegative1525 p) (nonnegative1520 p)
def d1527 (p : Pattern) : Int := if p 141 then d1526 p else d1524 p
theorem agree1527 (p q : Pattern) (h : Agree support p q) : d1527 p = d1527 q := by
  simp only [d1527, h 141 (by decide), agree1526 p q h, agree1524 p q h]
theorem nonnegative1527 (p : Pattern) : 0 ≤ d1527 p :=
  nonnegative_ite (p 141) (nonnegative1526 p) (nonnegative1524 p)
def d1528 (p : Pattern) : Int := if p 138 then d1527 p else d1522 p
theorem agree1528 (p q : Pattern) (h : Agree support p q) : d1528 p = d1528 q := by
  simp only [d1528, h 138 (by decide), agree1527 p q h, agree1522 p q h]
theorem nonnegative1528 (p : Pattern) : 0 ≤ d1528 p :=
  nonnegative_ite (p 138) (nonnegative1527 p) (nonnegative1522 p)
def d1529 (p : Pattern) : Int := if p 163 then d46 p else d1507 p
theorem agree1529 (p q : Pattern) (h : Agree support p q) : d1529 p = d1529 q := by
  simp only [d1529, h 163 (by decide), agree46 p q h, agree1507 p q h]
theorem nonnegative1529 (p : Pattern) : 0 ≤ d1529 p :=
  nonnegative_ite (p 163) (nonnegative46 p) (nonnegative1507 p)
def d1530 (p : Pattern) : Int := if p 162 then d47 p else d1529 p
theorem agree1530 (p q : Pattern) (h : Agree support p q) : d1530 p = d1530 q := by
  simp only [d1530, h 162 (by decide), agree47 p q h, agree1529 p q h]
theorem nonnegative1530 (p : Pattern) : 0 ≤ d1530 p :=
  nonnegative_ite (p 162) (nonnegative47 p) (nonnegative1529 p)
def d1531 (p : Pattern) : Int := if p 161 then d50 p else d1530 p
theorem agree1531 (p q : Pattern) (h : Agree support p q) : d1531 p = d1531 q := by
  simp only [d1531, h 161 (by decide), agree50 p q h, agree1530 p q h]
theorem nonnegative1531 (p : Pattern) : 0 ≤ d1531 p :=
  nonnegative_ite (p 161) (nonnegative50 p) (nonnegative1530 p)
def d1532 (p : Pattern) : Int := if p 160 then d1523 p else d1531 p
theorem agree1532 (p q : Pattern) (h : Agree support p q) : d1532 p = d1532 q := by
  simp only [d1532, h 160 (by decide), agree1523 p q h, agree1531 p q h]
theorem nonnegative1532 (p : Pattern) : 0 ≤ d1532 p :=
  nonnegative_ite (p 160) (nonnegative1523 p) (nonnegative1531 p)
def d1533 (p : Pattern) : Int := if p 141 then d1526 p else d1532 p
theorem agree1533 (p q : Pattern) (h : Agree support p q) : d1533 p = d1533 q := by
  simp only [d1533, h 141 (by decide), agree1526 p q h, agree1532 p q h]
theorem nonnegative1533 (p : Pattern) : 0 ≤ d1533 p :=
  nonnegative_ite (p 141) (nonnegative1526 p) (nonnegative1532 p)
def d1534 (p : Pattern) : Int := if p 163 then d72 p else d48 p
theorem agree1534 (p q : Pattern) (h : Agree support p q) : d1534 p = d1534 q := by
  simp only [d1534, h 163 (by decide), agree72 p q h, agree48 p q h]
theorem nonnegative1534 (p : Pattern) : 0 ≤ d1534 p :=
  nonnegative_ite (p 163) (nonnegative72 p) (nonnegative48 p)
def d1535 (p : Pattern) : Int := if p 162 then d73 p else d1534 p
theorem agree1535 (p q : Pattern) (h : Agree support p q) : d1535 p = d1535 q := by
  simp only [d1535, h 162 (by decide), agree73 p q h, agree1534 p q h]
theorem nonnegative1535 (p : Pattern) : 0 ≤ d1535 p :=
  nonnegative_ite (p 162) (nonnegative73 p) (nonnegative1534 p)
def d1536 (p : Pattern) : Int := if p 162 then d12 p else d73 p
theorem agree1536 (p q : Pattern) (h : Agree support p q) : d1536 p = d1536 q := by
  simp only [d1536, h 162 (by decide), agree12 p q h, agree73 p q h]
theorem nonnegative1536 (p : Pattern) : 0 ≤ d1536 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative73 p)
def d1537 (p : Pattern) : Int := if p 161 then d1536 p else d1535 p
theorem agree1537 (p q : Pattern) (h : Agree support p q) : d1537 p = d1537 q := by
  simp only [d1537, h 161 (by decide), agree1536 p q h, agree1535 p q h]
theorem nonnegative1537 (p : Pattern) : 0 ≤ d1537 p :=
  nonnegative_ite (p 161) (nonnegative1536 p) (nonnegative1535 p)
def d1538 (p : Pattern) : Int := if p 161 then d12 p else d1536 p
theorem agree1538 (p q : Pattern) (h : Agree support p q) : d1538 p = d1538 q := by
  simp only [d1538, h 161 (by decide), agree12 p q h, agree1536 p q h]
theorem nonnegative1538 (p : Pattern) : 0 ≤ d1538 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1536 p)
def d1539 (p : Pattern) : Int := if p 160 then d1538 p else d1537 p
theorem agree1539 (p q : Pattern) (h : Agree support p q) : d1539 p = d1539 q := by
  simp only [d1539, h 160 (by decide), agree1538 p q h, agree1537 p q h]
theorem nonnegative1539 (p : Pattern) : 0 ≤ d1539 p :=
  nonnegative_ite (p 160) (nonnegative1538 p) (nonnegative1537 p)
def d1540 (p : Pattern) : Int := if p 160 then d12 p else d1538 p
theorem agree1540 (p q : Pattern) (h : Agree support p q) : d1540 p = d1540 q := by
  simp only [d1540, h 160 (by decide), agree12 p q h, agree1538 p q h]
theorem nonnegative1540 (p : Pattern) : 0 ≤ d1540 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative1538 p)
def d1541 (p : Pattern) : Int := if p 141 then d1540 p else d1539 p
theorem agree1541 (p q : Pattern) (h : Agree support p q) : d1541 p = d1541 q := by
  simp only [d1541, h 141 (by decide), agree1540 p q h, agree1539 p q h]
theorem nonnegative1541 (p : Pattern) : 0 ≤ d1541 p :=
  nonnegative_ite (p 141) (nonnegative1540 p) (nonnegative1539 p)
def d1542 (p : Pattern) : Int := if p 138 then d1541 p else d1533 p
theorem agree1542 (p q : Pattern) (h : Agree support p q) : d1542 p = d1542 q := by
  simp only [d1542, h 138 (by decide), agree1541 p q h, agree1533 p q h]
theorem nonnegative1542 (p : Pattern) : 0 ≤ d1542 p :=
  nonnegative_ite (p 138) (nonnegative1541 p) (nonnegative1533 p)
def d1543 (p : Pattern) : Int := if p 116 then d1542 p else d1528 p
theorem agree1543 (p q : Pattern) (h : Agree support p q) : d1543 p = d1543 q := by
  simp only [d1543, h 116 (by decide), agree1542 p q h, agree1528 p q h]
theorem nonnegative1543 (p : Pattern) : 0 ≤ d1543 p :=
  nonnegative_ite (p 116) (nonnegative1542 p) (nonnegative1528 p)
def d1544 (p : Pattern) : Int := if p 163 then d46 p else d1505 p
theorem agree1544 (p q : Pattern) (h : Agree support p q) : d1544 p = d1544 q := by
  simp only [d1544, h 163 (by decide), agree46 p q h, agree1505 p q h]
theorem nonnegative1544 (p : Pattern) : 0 ≤ d1544 p :=
  nonnegative_ite (p 163) (nonnegative46 p) (nonnegative1505 p)
def d1545 (p : Pattern) : Int := if p 162 then d47 p else d1544 p
theorem agree1545 (p q : Pattern) (h : Agree support p q) : d1545 p = d1545 q := by
  simp only [d1545, h 162 (by decide), agree47 p q h, agree1544 p q h]
theorem nonnegative1545 (p : Pattern) : 0 ≤ d1545 p :=
  nonnegative_ite (p 162) (nonnegative47 p) (nonnegative1544 p)
def d1546 (p : Pattern) : Int := if p 161 then d50 p else d1545 p
theorem agree1546 (p q : Pattern) (h : Agree support p q) : d1546 p = d1546 q := by
  simp only [d1546, h 161 (by decide), agree50 p q h, agree1545 p q h]
theorem nonnegative1546 (p : Pattern) : 0 ≤ d1546 p :=
  nonnegative_ite (p 161) (nonnegative50 p) (nonnegative1545 p)
def d1547 (p : Pattern) : Int := if p 160 then d1512 p else d1546 p
theorem agree1547 (p q : Pattern) (h : Agree support p q) : d1547 p = d1547 q := by
  simp only [d1547, h 160 (by decide), agree1512 p q h, agree1546 p q h]
theorem nonnegative1547 (p : Pattern) : 0 ≤ d1547 p :=
  nonnegative_ite (p 160) (nonnegative1512 p) (nonnegative1546 p)
def d1548 (p : Pattern) : Int := if p 141 then d1520 p else d1547 p
theorem agree1548 (p q : Pattern) (h : Agree support p q) : d1548 p = d1548 q := by
  simp only [d1548, h 141 (by decide), agree1520 p q h, agree1547 p q h]
theorem nonnegative1548 (p : Pattern) : 0 ≤ d1548 p :=
  nonnegative_ite (p 141) (nonnegative1520 p) (nonnegative1547 p)
def d1549 (p : Pattern) : Int := if p 138 then d1527 p else d1548 p
theorem agree1549 (p q : Pattern) (h : Agree support p q) : d1549 p = d1549 q := by
  simp only [d1549, h 138 (by decide), agree1527 p q h, agree1548 p q h]
theorem nonnegative1549 (p : Pattern) : 0 ≤ d1549 p :=
  nonnegative_ite (p 138) (nonnegative1527 p) (nonnegative1548 p)
def d1550 (p : Pattern) : Int := if p 138 then d12 p else d1527 p
theorem agree1550 (p q : Pattern) (h : Agree support p q) : d1550 p = d1550 q := by
  simp only [d1550, h 138 (by decide), agree12 p q h, agree1527 p q h]
theorem nonnegative1550 (p : Pattern) : 0 ≤ d1550 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1527 p)
def d1551 (p : Pattern) : Int := if p 116 then d1550 p else d1549 p
theorem agree1551 (p q : Pattern) (h : Agree support p q) : d1551 p = d1551 q := by
  simp only [d1551, h 116 (by decide), agree1550 p q h, agree1549 p q h]
theorem nonnegative1551 (p : Pattern) : 0 ≤ d1551 p :=
  nonnegative_ite (p 116) (nonnegative1550 p) (nonnegative1549 p)
def d1552 (p : Pattern) : Int := if p 115 then d1551 p else d1543 p
theorem agree1552 (p q : Pattern) (h : Agree support p q) : d1552 p = d1552 q := by
  simp only [d1552, h 115 (by decide), agree1551 p q h, agree1543 p q h]
theorem nonnegative1552 (p : Pattern) : 0 ≤ d1552 p :=
  nonnegative_ite (p 115) (nonnegative1551 p) (nonnegative1543 p)
def d1553 (p : Pattern) : Int := if p 182 then d353 p else d14 p
theorem agree1553 (p q : Pattern) (h : Agree support p q) : d1553 p = d1553 q := by
  simp only [d1553, h 182 (by decide), agree353 p q h, agree14 p q h]
theorem nonnegative1553 (p : Pattern) : 0 ≤ d1553 p :=
  nonnegative_ite (p 182) (nonnegative353 p) (nonnegative14 p)
def d1554 (p : Pattern) : Int := if p 163 then d1507 p else d1553 p
theorem agree1554 (p q : Pattern) (h : Agree support p q) : d1554 p = d1554 q := by
  simp only [d1554, h 163 (by decide), agree1507 p q h, agree1553 p q h]
theorem nonnegative1554 (p : Pattern) : 0 ≤ d1554 p :=
  nonnegative_ite (p 163) (nonnegative1507 p) (nonnegative1553 p)
def d1555 (p : Pattern) : Int := if p 162 then d47 p else d1554 p
theorem agree1555 (p q : Pattern) (h : Agree support p q) : d1555 p = d1555 q := by
  simp only [d1555, h 162 (by decide), agree47 p q h, agree1554 p q h]
theorem nonnegative1555 (p : Pattern) : 0 ≤ d1555 p :=
  nonnegative_ite (p 162) (nonnegative47 p) (nonnegative1554 p)
def d1556 (p : Pattern) : Int := if p 161 then d50 p else d1555 p
theorem agree1556 (p q : Pattern) (h : Agree support p q) : d1556 p = d1556 q := by
  simp only [d1556, h 161 (by decide), agree50 p q h, agree1555 p q h]
theorem nonnegative1556 (p : Pattern) : 0 ≤ d1556 p :=
  nonnegative_ite (p 161) (nonnegative50 p) (nonnegative1555 p)
def d1557 (p : Pattern) : Int := if p 160 then d1512 p else d1556 p
theorem agree1557 (p q : Pattern) (h : Agree support p q) : d1557 p = d1557 q := by
  simp only [d1557, h 160 (by decide), agree1512 p q h, agree1556 p q h]
theorem nonnegative1557 (p : Pattern) : 0 ≤ d1557 p :=
  nonnegative_ite (p 160) (nonnegative1512 p) (nonnegative1556 p)
def d1558 (p : Pattern) : Int := if p 163 then d66 p else d1505 p
theorem agree1558 (p q : Pattern) (h : Agree support p q) : d1558 p = d1558 q := by
  simp only [d1558, h 163 (by decide), agree66 p q h, agree1505 p q h]
theorem nonnegative1558 (p : Pattern) : 0 ≤ d1558 p :=
  nonnegative_ite (p 163) (nonnegative66 p) (nonnegative1505 p)
def d1559 (p : Pattern) : Int := if p 162 then d68 p else d1558 p
theorem agree1559 (p q : Pattern) (h : Agree support p q) : d1559 p = d1559 q := by
  simp only [d1559, h 162 (by decide), agree68 p q h, agree1558 p q h]
theorem nonnegative1559 (p : Pattern) : 0 ≤ d1559 p :=
  nonnegative_ite (p 162) (nonnegative68 p) (nonnegative1558 p)
end NetHack.Sokoban22Refined85
