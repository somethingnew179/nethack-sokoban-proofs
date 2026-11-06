/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions65
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub7920 (p : Pattern) : d1461 (change p 10000 none) = d1461 p := by
  change (if p 160 then d1447 (change p 10000 none) else d1460 (change p 10000 none)) = d1461 p
  rw [sub7900, sub7919]
  rfl
theorem sub7921 (p : Pattern) : d1462 (change p 10000 none) = d1462 p := by
  change (if p 141 then d1461 (change p 10000 none) else d1443 (change p 10000 none)) = d1462 p
  rw [sub7920, sub7889]
  rfl
theorem sub7922 (p : Pattern) : d1463 (change p 10000 none) = d1463 p := by
  change (if p 138 then d1456 (change p 10000 none) else d1462 (change p 10000 none)) = d1463 p
  rw [sub7915, sub7921]
  rfl
theorem sub7923 (p : Pattern) : d1464 (change p 10000 none) = d1464 p := by
  change (if p 138 then d12 (change p 10000 none) else d1456 (change p 10000 none)) = d1464 p
  rw [sub1, sub7915]
  rfl
theorem sub7924 (p : Pattern) : d1465 (change p 10000 none) = d1465 p := by
  change (if p 116 then d1464 (change p 10000 none) else d1463 (change p 10000 none)) = d1465 p
  rw [sub7923, sub7922]
  rfl
theorem sub7925 (p : Pattern) : d1466 (change p 10000 none) = d1466 p := by
  change (if p 115 then d1465 (change p 10000 none) else d1459 (change p 10000 none)) = d1466 p
  rw [sub7924, sub7918]
  rfl
theorem sub7926 (p : Pattern) : d1467 (change p 10000 none) = d1467 p := by
  change (if p 71 then d1466 (change p 10000 none) else d1430 (change p 10000 none)) = d1467 p
  rw [sub7925, sub7869]
  rfl
theorem sub7927 (p : Pattern) : d1468 (change p 10000 none) = d1468 p := by
  change (if p 49 then d1467 (change p 10000 none) else d1438 (change p 10000 none)) = d1468 p
  rw [sub7926, sub7883]
  rfl
theorem sub7928 (p : Pattern) : d1469 (change p 10000 none) = d1469 p := by
  change (if p 162 then d1181 (change p 10000 none) else d53 (change p 10000 none)) = d1469 p
  rw [sub7851, sub47]
  rfl
theorem sub7929 (p : Pattern) : d1470 (change p 10000 none) = d1470 p := by
  change (if p 161 then d1417 (change p 10000 none) else d1469 (change p 10000 none)) = d1470 p
  rw [sub7854, sub7928]
  rfl
theorem sub7930 (p : Pattern) : d1100 (change p 10000 none) = d1100 p := by
  change (if p 162 then d12 (change p 10000 none) else d20 (change p 10000 none)) = d1100 p
  rw [sub1, sub10]
  rfl
theorem sub7931 (p : Pattern) : d1101 (change p 10000 none) = d1101 p := by
  change (if p 161 then d12 (change p 10000 none) else d1100 (change p 10000 none)) = d1101 p
  rw [sub1, sub7930]
  rfl
theorem sub7932 (p : Pattern) : d1471 (change p 10000 none) = d1471 p := by
  change (if p 160 then d1101 (change p 10000 none) else d1470 (change p 10000 none)) = d1471 p
  rw [sub7931, sub7929]
  rfl
theorem sub7933 (p : Pattern) : d1472 (change p 10000 none) = d1472 p := by
  change (if p 141 then d1471 (change p 10000 none) else d1415 (change p 10000 none)) = d1472 p
  rw [sub7932, sub7850]
  rfl
theorem sub7934 (p : Pattern) : d1473 (change p 10000 none) = d1473 p := by
  change (if p 138 then d1472 (change p 10000 none) else d1426 (change p 10000 none)) = d1473 p
  rw [sub7933, sub7865]
  rfl
theorem sub7935 (p : Pattern) : d1474 (change p 10000 none) = d1474 p := by
  change (if p 138 then d12 (change p 10000 none) else d1472 (change p 10000 none)) = d1474 p
  rw [sub1, sub7933]
  rfl
theorem sub7936 (p : Pattern) : d1475 (change p 10000 none) = d1475 p := by
  change (if p 116 then d1474 (change p 10000 none) else d1473 (change p 10000 none)) = d1475 p
  rw [sub7935, sub7934]
  rfl
theorem sub7937 (p : Pattern) : d1476 (change p 10000 none) = d1476 p := by
  change (if p 115 then d1475 (change p 10000 none) else d1436 (change p 10000 none)) = d1476 p
  rw [sub7936, sub7881]
  rfl
theorem sub7938 (p : Pattern) : d1477 (change p 10000 none) = d1477 p := by
  change (if p 71 then d1476 (change p 10000 none) else d1430 (change p 10000 none)) = d1477 p
  rw [sub7937, sub7869]
  rfl
theorem sub7939 (p : Pattern) : d1478 (change p 10000 none) = d1478 p := by
  change (if p 116 then d1458 (change p 10000 none) else d1463 (change p 10000 none)) = d1478 p
  rw [sub7917, sub7922]
  rfl
theorem sub7940 (p : Pattern) : d1479 (change p 10000 none) = d1479 p := by
  change (if p 162 then d112 (change p 10000 none) else d291 (change p 10000 none)) = d1479 p
  rw [sub109, sub391]
  rfl
theorem sub7941 (p : Pattern) : d1480 (change p 10000 none) = d1480 p := by
  change (if p 161 then d1479 (change p 10000 none) else d111 (change p 10000 none)) = d1480 p
  rw [sub7940, sub108]
  rfl
theorem sub7942 (p : Pattern) : d1481 (change p 10000 none) = d1481 p := by
  change (if p 162 then d275 (change p 10000 none) else d269 (change p 10000 none)) = d1481 p
  rw [sub375, sub369]
  rfl
theorem sub7943 (p : Pattern) : d1482 (change p 10000 none) = d1482 p := by
  change (if p 161 then d279 (change p 10000 none) else d1481 (change p 10000 none)) = d1482 p
  rw [sub379, sub7942]
  rfl
theorem sub7944 (p : Pattern) : d1483 (change p 10000 none) = d1483 p := by
  change (if p 160 then d1482 (change p 10000 none) else d1480 (change p 10000 none)) = d1483 p
  rw [sub7943, sub7941]
  rfl
theorem sub7945 (p : Pattern) : d925 (change p 10000 none) = d925 p := by
  change (if p 163 then d298 (change p 10000 none) else d132 (change p 10000 none)) = d925 p
  rw [sub398, sub131]
  rfl
theorem sub7946 (p : Pattern) : d1124 (change p 10000 none) = d1124 p := by
  change (if p 162 then d12 (change p 10000 none) else d925 (change p 10000 none)) = d1124 p
  rw [sub1, sub7945]
  rfl
theorem sub7947 (p : Pattern) : d1484 (change p 10000 none) = d1484 p := by
  change (if p 161 then d1124 (change p 10000 none) else d1453 (change p 10000 none)) = d1484 p
  rw [sub7946, sub7909]
  rfl
theorem sub7948 (p : Pattern) : d1375 (change p 10000 none) = d1375 p := by
  change (if p 163 then d12 (change p 10000 none) else d283 (change p 10000 none)) = d1375 p
  rw [sub1, sub383]
  rfl
theorem sub7949 (p : Pattern) : d1485 (change p 10000 none) = d1485 p := by
  change (if p 162 then d1375 (change p 10000 none) else d925 (change p 10000 none)) = d1485 p
  rw [sub7948, sub7945]
  rfl
theorem sub7950 (p : Pattern) : d1126 (change p 10000 none) = d1126 p := by
  change (if p 204 then d24 (change p 10000 none) else d120 (change p 10000 none)) = d1126 p
  rw [sub15, sub119]
  rfl
theorem sub7951 (p : Pattern) : d1127 (change p 10000 none) = d1127 p := by
  change (if p 182 then d12 (change p 10000 none) else d1126 (change p 10000 none)) = d1127 p
  rw [sub1, sub7950]
  rfl
theorem sub7952 (p : Pattern) : d1128 (change p 10000 none) = d1128 p := by
  change (if p 163 then d1127 (change p 10000 none) else d283 (change p 10000 none)) = d1128 p
  rw [sub7951, sub383]
  rfl
theorem sub7953 (p : Pattern) : d1129 (change p 10000 none) = d1129 p := by
  change (if p 162 then d12 (change p 10000 none) else d1128 (change p 10000 none)) = d1129 p
  rw [sub1, sub7952]
  rfl
theorem sub7954 (p : Pattern) : d1486 (change p 10000 none) = d1486 p := by
  change (if p 161 then d1129 (change p 10000 none) else d1485 (change p 10000 none)) = d1486 p
  rw [sub7953, sub7949]
  rfl
theorem sub7955 (p : Pattern) : d1487 (change p 10000 none) = d1487 p := by
  change (if p 160 then d1486 (change p 10000 none) else d1484 (change p 10000 none)) = d1487 p
  rw [sub7954, sub7947]
  rfl
theorem sub7956 (p : Pattern) : d1488 (change p 10000 none) = d1488 p := by
  change (if p 141 then d1487 (change p 10000 none) else d1483 (change p 10000 none)) = d1488 p
  rw [sub7955, sub7944]
  rfl
theorem sub7957 (p : Pattern) : d1489 (change p 10000 none) = d1489 p := by
  change (if p 162 then d293 (change p 10000 none) else d105 (change p 10000 none)) = d1489 p
  rw [sub393, sub101]
  rfl
theorem sub7958 (p : Pattern) : d1133 (change p 10000 none) = d1133 p := by
  change (if p 163 then d132 (change p 10000 none) else d269 (change p 10000 none)) = d1133 p
  rw [sub131, sub369]
  rfl
theorem sub7959 (p : Pattern) : d1490 (change p 10000 none) = d1490 p := by
  change (if p 162 then d278 (change p 10000 none) else d1133 (change p 10000 none)) = d1490 p
  rw [sub378, sub7958]
  rfl
theorem sub7960 (p : Pattern) : d1491 (change p 10000 none) = d1491 p := by
  change (if p 161 then d1490 (change p 10000 none) else d1489 (change p 10000 none)) = d1491 p
  rw [sub7959, sub7957]
  rfl
theorem sub7961 (p : Pattern) : d1492 (change p 10000 none) = d1492 p := by
  change (if p 160 then d1062 (change p 10000 none) else d1491 (change p 10000 none)) = d1492 p
  rw [sub7906, sub7960]
  rfl
theorem sub7962 (p : Pattern) : d1385 (change p 10000 none) = d1385 p := by
  change (if p 163 then d12 (change p 10000 none) else d298 (change p 10000 none)) = d1385 p
  rw [sub1, sub398]
  rfl
theorem sub7963 (p : Pattern) : d1493 (change p 10000 none) = d1493 p := by
  change (if p 162 then d1385 (change p 10000 none) else d132 (change p 10000 none)) = d1493 p
  rw [sub7962, sub131]
  rfl
theorem sub7964 (p : Pattern) : d1137 (change p 10000 none) = d1137 p := by
  change (if p 163 then d109 (change p 10000 none) else d298 (change p 10000 none)) = d1137 p
  rw [sub106, sub398]
  rfl
theorem sub7965 (p : Pattern) : d1138 (change p 10000 none) = d1138 p := by
  change (if p 162 then d12 (change p 10000 none) else d1137 (change p 10000 none)) = d1138 p
  rw [sub1, sub7964]
  rfl
theorem sub7966 (p : Pattern) : d1494 (change p 10000 none) = d1494 p := by
  change (if p 161 then d1138 (change p 10000 none) else d1493 (change p 10000 none)) = d1494 p
  rw [sub7965, sub7963]
  rfl
theorem sub7967 (p : Pattern) : d1140 (change p 10000 none) = d1140 p := by
  change (if p 162 then d12 (change p 10000 none) else d109 (change p 10000 none)) = d1140 p
  rw [sub1, sub106]
  rfl
theorem sub7968 (p : Pattern) : d1141 (change p 10000 none) = d1141 p := by
  change (if p 161 then d12 (change p 10000 none) else d1140 (change p 10000 none)) = d1141 p
  rw [sub1, sub7967]
  rfl
theorem sub7969 (p : Pattern) : d1495 (change p 10000 none) = d1495 p := by
  change (if p 160 then d1141 (change p 10000 none) else d1494 (change p 10000 none)) = d1495 p
  rw [sub7968, sub7966]
  rfl
theorem sub7970 (p : Pattern) : d1496 (change p 10000 none) = d1496 p := by
  change (if p 141 then d1495 (change p 10000 none) else d1492 (change p 10000 none)) = d1496 p
  rw [sub7969, sub7961]
  rfl
theorem sub7971 (p : Pattern) : d1497 (change p 10000 none) = d1497 p := by
  change (if p 138 then d1496 (change p 10000 none) else d1488 (change p 10000 none)) = d1497 p
  rw [sub7970, sub7956]
  rfl
theorem sub7972 (p : Pattern) : d1498 (change p 10000 none) = d1498 p := by
  change (if p 138 then d12 (change p 10000 none) else d1496 (change p 10000 none)) = d1498 p
  rw [sub1, sub7970]
  rfl
theorem sub7973 (p : Pattern) : d1499 (change p 10000 none) = d1499 p := by
  change (if p 116 then d1498 (change p 10000 none) else d1497 (change p 10000 none)) = d1499 p
  rw [sub7972, sub7971]
  rfl
theorem sub7974 (p : Pattern) : d1500 (change p 10000 none) = d1500 p := by
  change (if p 115 then d1499 (change p 10000 none) else d1478 (change p 10000 none)) = d1500 p
  rw [sub7973, sub7939]
  rfl
theorem sub7975 (p : Pattern) : d1501 (change p 10000 none) = d1501 p := by
  change (if p 71 then d1500 (change p 10000 none) else d1430 (change p 10000 none)) = d1501 p
  rw [sub7974, sub7869]
  rfl
theorem sub7976 (p : Pattern) : d1502 (change p 10000 none) = d1502 p := by
  change (if p 49 then d1501 (change p 10000 none) else d1477 (change p 10000 none)) = d1502 p
  rw [sub7975, sub7938]
  rfl
theorem sub7977 (p : Pattern) : d1503 (change p 10000 none) = d1503 p := by
  change (if p 48 then d1502 (change p 10000 none) else d1468 (change p 10000 none)) = d1503 p
  rw [sub7976, sub7927]
  rfl
theorem sub7978 (p : Pattern) : d0 (change p 163 (some 141)) = d0 p := by
  rfl
theorem sub7979 (p : Pattern) : d12 (change p 163 (some 141)) = d12 p := by
  rfl
theorem sub7980 (p : Pattern) : d13 (change p 163 (some 141)) = d13 p := by
  change (if p 247 then d12 (change p 163 (some 141)) else d0 (change p 163 (some 141))) = d13 p
  rw [sub7979, sub7978]
  rfl
theorem sub7981 (p : Pattern) : d14 (change p 163 (some 141)) = d14 p := by
  change (if p 246 then d13 (change p 163 (some 141)) else d0 (change p 163 (some 141))) = d14 p
  rw [sub7980, sub7978]
  rfl
theorem sub7982 (p : Pattern) : d15 (change p 163 (some 141)) = d15 p := by
  change (if p 204 then d12 (change p 163 (some 141)) else d14 (change p 163 (some 141))) = d15 p
  rw [sub7979, sub7981]
  rfl
theorem sub7983 (p : Pattern) : d16 (change p 163 (some 141)) = d16 p := by
  change (if p 182 then d15 (change p 163 (some 141)) else d14 (change p 163 (some 141))) = d16 p
  rw [sub7982, sub7981]
  rfl
theorem sub7984 (p : Pattern) : d1164 (change p 163 (some 141)) = d16 p := by
  change d16 (change p 163 (some 141)) = d16 p
  exact sub7983 p
theorem sub7985 (p : Pattern) : d2 (change p 163 (some 141)) = d2 p := by
  rfl
theorem sub7986 (p : Pattern) : d30 (change p 163 (some 141)) = d30 p := by
  change (if p 247 then d12 (change p 163 (some 141)) else d2 (change p 163 (some 141))) = d30 p
  rw [sub7979, sub7985]
  rfl
theorem sub7987 (p : Pattern) : d31 (change p 163 (some 141)) = d31 p := by
  change (if p 246 then d30 (change p 163 (some 141)) else d2 (change p 163 (some 141))) = d31 p
  rw [sub7986, sub7985]
  rfl
theorem sub7988 (p : Pattern) : d32 (change p 163 (some 141)) = d32 p := by
  change (if p 204 then d12 (change p 163 (some 141)) else d31 (change p 163 (some 141))) = d32 p
  rw [sub7979, sub7987]
  rfl
theorem sub7989 (p : Pattern) : d53 (change p 163 (some 141)) = d53 p := by
  change (if p 182 then d32 (change p 163 (some 141)) else d31 (change p 163 (some 141))) = d53 p
  rw [sub7988, sub7987]
  rfl
theorem sub7990 (p : Pattern) : d1165 (change p 163 (some 141)) = d53 p := by
  change d53 (change p 163 (some 141)) = d53 p
  exact sub7989 p
theorem sub7991 (p : Pattern) : d1166 (change p 163 (some 141)) = d4311 p := by
  change (if p 162 then d1165 (change p 163 (some 141)) else d1164 (change p 163 (some 141))) = d4311 p
  rw [sub7990, sub7984]
  rfl
theorem sub7992 (p : Pattern) : d1167 (change p 163 (some 141)) = d53 p := by
  change d53 (change p 163 (some 141)) = d53 p
  exact sub7989 p
theorem sub7993 (p : Pattern) : d11 (change p 163 (some 141)) = d11 p := by
  rfl
theorem sub7994 (p : Pattern) : d39 (change p 163 (some 141)) = d39 p := by
  change (if p 247 then d12 (change p 163 (some 141)) else d11 (change p 163 (some 141))) = d39 p
  rw [sub7979, sub7993]
  rfl
theorem sub7995 (p : Pattern) : d40 (change p 163 (some 141)) = d40 p := by
  change (if p 246 then d39 (change p 163 (some 141)) else d11 (change p 163 (some 141))) = d40 p
  rw [sub7994, sub7993]
  rfl
theorem sub7996 (p : Pattern) : d41 (change p 163 (some 141)) = d41 p := by
  change (if p 204 then d12 (change p 163 (some 141)) else d40 (change p 163 (some 141))) = d41 p
  rw [sub7979, sub7995]
  rfl
theorem sub7997 (p : Pattern) : d62 (change p 163 (some 141)) = d62 p := by
  change (if p 182 then d41 (change p 163 (some 141)) else d40 (change p 163 (some 141))) = d62 p
  rw [sub7996, sub7995]
  rfl
theorem sub7998 (p : Pattern) : d63 (change p 163 (some 141)) = d62 p := by
  change d62 (change p 163 (some 141)) = d62 p
  exact sub7997 p
theorem sub7999 (p : Pattern) : d1168 (change p 163 (some 141)) = d4312 p := by
  change (if p 162 then d63 (change p 163 (some 141)) else d1167 (change p 163 (some 141))) = d4312 p
  rw [sub7998, sub7992]
  rfl
theorem sub8000 (p : Pattern) : d1169 (change p 163 (some 141)) = d4313 p := by
  change (if p 161 then d1168 (change p 163 (some 141)) else d1166 (change p 163 (some 141))) = d4313 p
  rw [sub7999, sub7991]
  rfl
theorem sub8001 (p : Pattern) : d1170 (change p 163 (some 141)) = d53 p := by
  change d53 (change p 163 (some 141)) = d53 p
  exact sub7989 p
theorem sub8002 (p : Pattern) : d66 (change p 163 (some 141)) = d66 p := by
  change (if p 182 then d12 (change p 163 (some 141)) else d31 (change p 163 (some 141))) = d66 p
  rw [sub7979, sub7987]
  rfl
theorem sub8003 (p : Pattern) : d1171 (change p 163 (some 141)) = d66 p := by
  change d66 (change p 163 (some 141)) = d66 p
  exact sub8002 p
theorem sub8004 (p : Pattern) : d1172 (change p 163 (some 141)) = d4314 p := by
  change (if p 162 then d1171 (change p 163 (some 141)) else d1170 (change p 163 (some 141))) = d4314 p
  rw [sub8003, sub8001]
  rfl
theorem sub8005 (p : Pattern) : d72 (change p 163 (some 141)) = d72 p := by
  change (if p 182 then d12 (change p 163 (some 141)) else d40 (change p 163 (some 141))) = d72 p
  rw [sub7979, sub7995]
  rfl
theorem sub8006 (p : Pattern) : d73 (change p 163 (some 141)) = d72 p := by
  change d72 (change p 163 (some 141)) = d72 p
  exact sub8005 p
theorem sub8007 (p : Pattern) : d1173 (change p 163 (some 141)) = d4315 p := by
  change (if p 162 then d73 (change p 163 (some 141)) else d1171 (change p 163 (some 141))) = d4315 p
  rw [sub8006, sub8003]
  rfl
theorem sub8008 (p : Pattern) : d1174 (change p 163 (some 141)) = d4316 p := by
  change (if p 161 then d1173 (change p 163 (some 141)) else d1172 (change p 163 (some 141))) = d4316 p
  rw [sub8007, sub8004]
  rfl
theorem sub8009 (p : Pattern) : d1175 (change p 163 (some 141)) = d4317 p := by
  change (if p 160 then d1174 (change p 163 (some 141)) else d1169 (change p 163 (some 141))) = d4317 p
  rw [sub8008, sub8000]
  rfl
theorem sub8010 (p : Pattern) : d1176 (change p 163 (some 141)) = d4317 p := by
  change d1175 (change p 163 (some 141)) = d4317 p
  exact sub8009 p
theorem sub8011 (p : Pattern) : d1185 (change p 163 (some 141)) = d16 p := by
  change d16 (change p 163 (some 141)) = d16 p
  exact sub7983 p
theorem sub8012 (p : Pattern) : d1181 (change p 163 (some 141)) = d53 p := by
  change d53 (change p 163 (some 141)) = d53 p
  exact sub7989 p
theorem sub8013 (p : Pattern) : d1186 (change p 163 (some 141)) = d4311 p := by
  change (if p 162 then d1181 (change p 163 (some 141)) else d1185 (change p 163 (some 141))) = d4311 p
  rw [sub8012, sub8011]
  rfl
theorem sub8014 (p : Pattern) : d1182 (change p 163 (some 141)) = d4312 p := by
  change (if p 162 then d63 (change p 163 (some 141)) else d1181 (change p 163 (some 141))) = d4312 p
  rw [sub7998, sub8012]
  rfl
theorem sub8015 (p : Pattern) : d1187 (change p 163 (some 141)) = d4313 p := by
  change (if p 161 then d1182 (change p 163 (some 141)) else d1186 (change p 163 (some 141))) = d4313 p
  rw [sub8014, sub8013]
  rfl
theorem sub8016 (p : Pattern) : d1188 (change p 163 (some 141)) = d968 p := by
  change (if p 162 then d12 (change p 163 (some 141)) else d1181 (change p 163 (some 141))) = d968 p
  rw [sub7979, sub8012]
  rfl
theorem sub8017 (p : Pattern) : d1189 (change p 163 (some 141)) = d969 p := by
  change (if p 161 then d12 (change p 163 (some 141)) else d1188 (change p 163 (some 141))) = d969 p
  rw [sub7979, sub8016]
  rfl
theorem sub8018 (p : Pattern) : d1190 (change p 163 (some 141)) = d4321 p := by
  change (if p 160 then d1189 (change p 163 (some 141)) else d1187 (change p 163 (some 141))) = d4321 p
  rw [sub8017, sub8015]
  rfl
theorem sub8019 (p : Pattern) : d1191 (change p 163 (some 141)) = d4321 p := by
  change d1190 (change p 163 (some 141)) = d4321 p
  exact sub8018 p
theorem sub8020 (p : Pattern) : d1192 (change p 163 (some 141)) = d5244 p := by
  change (if p 138 then d1191 (change p 163 (some 141)) else d1176 (change p 163 (some 141))) = d5244 p
  rw [sub8019, sub8010]
  rfl
theorem sub8021 (p : Pattern) : d1197 (change p 163 (some 141)) = d16 p := by
  change d16 (change p 163 (some 141)) = d16 p
  exact sub7983 p
theorem sub8022 (p : Pattern) : d1198 (change p 163 (some 141)) = d4311 p := by
  change (if p 162 then d1181 (change p 163 (some 141)) else d1197 (change p 163 (some 141))) = d4311 p
  rw [sub8012, sub8021]
  rfl
theorem sub8023 (p : Pattern) : d1199 (change p 163 (some 141)) = d4313 p := by
  change (if p 161 then d1182 (change p 163 (some 141)) else d1198 (change p 163 (some 141))) = d4313 p
  rw [sub8014, sub8022]
  rfl
theorem sub8024 (p : Pattern) : d1200 (change p 163 (some 141)) = d4321 p := by
  change (if p 160 then d1189 (change p 163 (some 141)) else d1199 (change p 163 (some 141))) = d4321 p
  rw [sub8017, sub8023]
  rfl
theorem sub8025 (p : Pattern) : d1201 (change p 163 (some 141)) = d4321 p := by
  change d1200 (change p 163 (some 141)) = d4321 p
  exact sub8024 p
theorem sub8026 (p : Pattern) : d91 (change p 163 (some 141)) = d4160 p := by
  change (if p 162 then d12 (change p 163 (some 141)) else d63 (change p 163 (some 141))) = d4160 p
  rw [sub7979, sub7998]
  rfl
theorem sub8027 (p : Pattern) : d93 (change p 163 (some 141)) = d4161 p := by
  change (if p 161 then d12 (change p 163 (some 141)) else d91 (change p 163 (some 141))) = d4161 p
  rw [sub7979, sub8026]
  rfl
theorem sub8028 (p : Pattern) : d95 (change p 163 (some 141)) = d4162 p := by
  change (if p 160 then d12 (change p 163 (some 141)) else d93 (change p 163 (some 141))) = d4162 p
  rw [sub7979, sub8027]
  rfl
theorem sub8029 (p : Pattern) : d1205 (change p 163 (some 141)) = d4162 p := by
  change d95 (change p 163 (some 141)) = d4162 p
  exact sub8028 p
theorem sub8030 (p : Pattern) : d1206 (change p 163 (some 141)) = d5245 p := by
  change (if p 138 then d1205 (change p 163 (some 141)) else d1201 (change p 163 (some 141))) = d5245 p
  rw [sub8029, sub8025]
  rfl
theorem sub8031 (p : Pattern) : d1207 (change p 163 (some 141)) = d5246 p := by
  change (if p 116 then d1206 (change p 163 (some 141)) else d1192 (change p 163 (some 141))) = d5246 p
  rw [sub8030, sub8020]
  rfl
theorem sub8032 (p : Pattern) : d1154 (change p 163 (some 141)) = d16 p := by
  change d16 (change p 163 (some 141)) = d16 p
  exact sub7983 p
theorem sub8033 (p : Pattern) : d1216 (change p 163 (some 141)) = d4311 p := by
  change (if p 162 then d1181 (change p 163 (some 141)) else d1154 (change p 163 (some 141))) = d4311 p
  rw [sub8012, sub8032]
  rfl
theorem sub8034 (p : Pattern) : d1217 (change p 163 (some 141)) = d4313 p := by
  change (if p 161 then d1182 (change p 163 (some 141)) else d1216 (change p 163 (some 141))) = d4313 p
  rw [sub8014, sub8033]
  rfl
theorem sub8035 (p : Pattern) : d1218 (change p 163 (some 141)) = d4314 p := by
  change (if p 162 then d1171 (change p 163 (some 141)) else d1181 (change p 163 (some 141))) = d4314 p
  rw [sub8003, sub8012]
  rfl
theorem sub8036 (p : Pattern) : d1219 (change p 163 (some 141)) = d4316 p := by
  change (if p 161 then d1173 (change p 163 (some 141)) else d1218 (change p 163 (some 141))) = d4316 p
  rw [sub8007, sub8035]
  rfl
theorem sub8037 (p : Pattern) : d1220 (change p 163 (some 141)) = d4317 p := by
  change (if p 160 then d1219 (change p 163 (some 141)) else d1217 (change p 163 (some 141))) = d4317 p
  rw [sub8036, sub8034]
  rfl
theorem sub8038 (p : Pattern) : d1221 (change p 163 (some 141)) = d4317 p := by
  change d1220 (change p 163 (some 141)) = d4317 p
  exact sub8037 p
theorem sub8039 (p : Pattern) : d1177 (change p 163 (some 141)) = d16 p := by
  change d16 (change p 163 (some 141)) = d16 p
  exact sub7983 p
end NetHack.Sokoban22Refined85
