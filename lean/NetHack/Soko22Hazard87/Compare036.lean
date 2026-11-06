import NetHack.Soko22Hazard87.Compare035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9000 (p : Pattern) (guard : d1115 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8080 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9001 (p : Pattern) (guard : d1116 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9000 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9002 (p : Pattern) (guard : d1117 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9001 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8082 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9003 (p : Pattern) (guard : d1118 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9002 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8083 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9004 (p : Pattern) (guard : d1119 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9003 p hg
    simpa only [d1119, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1119, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9005 (p : Pattern) (guard : d1120 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8984 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9004 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9006 (p : Pattern) (guard : d1121 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9005 p hg
    simpa only [d1121, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1121, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9007 (p : Pattern) (guard : d1122 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9006 p hg
    simpa only [d1122, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1122, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9008 (p : Pattern) (guard : d1393 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1392 p = 1 := by simpa only [d1393, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8999 p hg
    simpa only [d1393, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1393, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9007 p hg
    simpa only [d1393, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9009 (p : Pattern) (guard : d1394 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1393 p = 1 := by simpa only [d1394, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9008 p hg
    simpa only [d1394, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1394, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d1394, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9010 (p : Pattern) (guard : d1395 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1388 p = 1 := by simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8989 p hg
    simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1394 p = 1 := by simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9009 p hg
    simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9011 (p : Pattern) (guard : d1396 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1389 p = 1 := by simpa only [d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8990 p hg
    simpa only [d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1395 p = 1 := by simpa only [d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9010 p hg
    simpa only [d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9012 (p : Pattern) (guard : d1400 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1394 p = 1 := by simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9009 p hg
    simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9013 (p : Pattern) (guard : d1401 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1395 p = 1 := by simpa only [d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9010 p hg
    simpa only [d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1400 p = 1 := by simpa only [d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9012 p hg
    simpa only [d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9014 (p : Pattern) (guard : d1402 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1396 p = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9011 p hg
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1401 p = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9013 p hg
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9015 (p : Pattern) (guard : d1403 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1403, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d1403, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1402 p = 1 := by simpa only [d1403, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9014 p hg
    simpa only [d1403, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9016 (p : Pattern) (guard : d1404 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1404, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d1404, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1403 p = 1 := by simpa only [d1404, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9015 p hg
    simpa only [d1404, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9017 (p : Pattern) (guard : d1132 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8992 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9018 (p : Pattern) (guard : d1133 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9017 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9019 (p : Pattern) (guard : d1134 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9018 p hg
    simpa only [d1134, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1134, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9020 (p : Pattern) (guard : d1135 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9019 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8069 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9021 (p : Pattern) (guard : d1406 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1406, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d1406, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1135 p = 1 := by simpa only [d1406, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9020 p hg
    simpa only [d1406, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9022 (p : Pattern) (guard : d1136 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8763 p hg
    simpa only [d1136, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1136, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9023 (p : Pattern) (guard : d1407 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1406 p = 1 := by simpa only [d1407, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9021 p hg
    simpa only [d1407, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1136 p = 1 := by simpa only [d1407, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9022 p hg
    simpa only [d1407, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9024 (p : Pattern) (guard : d1132 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9001 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9025 (p : Pattern) (guard : d1133 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9024 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9026 (p : Pattern) (guard : d1134 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9025 p hg
    simpa only [d1134, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1134, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9027 (p : Pattern) (guard : d1135 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9026 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9028 (p : Pattern) (guard : d1136 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9027 p hg
    simpa only [d1136, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1136, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9029 (p : Pattern) (guard : d1137 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1136 p = 1 := by simpa only [d1137, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9028 p hg
    simpa only [d1137, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1137, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1137, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9030 (p : Pattern) (guard : d1408 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1407 p = 1 := by simpa only [d1408, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9023 p hg
    simpa only [d1408, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1137 p = 1 := by simpa only [d1408, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9029 p hg
    simpa only [d1408, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9031 (p : Pattern) (guard : d1409 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1408 p = 1 := by simpa only [d1409, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9030 p hg
    simpa only [d1409, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1409, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d1409, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9032 (p : Pattern) (guard : d1410 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1409 p = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9031 p hg
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9033 (p : Pattern) (guard : d1411 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1400 p = 1 := by simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9012 p hg
    simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1410 p = 1 := by simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9032 p hg
    simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9034 (p : Pattern) (guard : d1412 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1401 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9013 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1411 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9033 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9035 (p : Pattern) (guard : d1413 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1413, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d1413, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1413, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9034 p hg
    simpa only [d1413, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9036 (p : Pattern) (guard : d1414 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1414, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d1414, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1413 p = 1 := by simpa only [d1414, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9035 p hg
    simpa only [d1414, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9037 (p : Pattern) (guard : d1415 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1404 p = 1 := by simpa only [d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9016 p hg
    simpa only [d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1414 p = 1 := by simpa only [d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9036 p hg
    simpa only [d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9038 (p : Pattern) (guard : d1420 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1414 p = 1 := by simpa only [d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9036 p hg
    simpa only [d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9039 (p : Pattern) (guard : d1421 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1415 p = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9037 p hg
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1420 p = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9038 p hg
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9040 (p : Pattern) (guard : d1422 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1421 p = 1 := by simpa only [d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9039 p hg
    simpa only [d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9041 (p : Pattern) (guard : d1423 p = 1) : d47807 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1422 p = 1 := by simpa only [d1423, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9040 p hg
    simpa only [d1423, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1423, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d1423, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9042 (p : Pattern) (guard : d1424 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1424, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d1424, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1423 p = 1 := by simpa only [d1424, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9041 p hg
    simpa only [d1424, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9043 (p : Pattern) (guard : d1429 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1420 p = 1 := by simpa only [d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9038 p hg
    simpa only [d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9044 (p : Pattern) (guard : d1430 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1429 p = 1 := by simpa only [d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9043 p hg
    simpa only [d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9045 (p : Pattern) (guard : d1431 p = 1) : d47807 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1430 p = 1 := by simpa only [d1431, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9044 p hg
    simpa only [d1431, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1431, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d1431, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9046 (p : Pattern) (guard : d1432 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1432, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d1432, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1431 p = 1 := by simpa only [d1432, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9045 p hg
    simpa only [d1432, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9047 (p : Pattern) (guard : d1433 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1424 p = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9042 p hg
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1432 p = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9046 p hg
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9048 (p : Pattern) (guard : d1434 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1433 p = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9047 p hg
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9049 (p : Pattern) (guard : d1435 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1434 p = 1 := by simpa only [d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9048 p hg
    simpa only [d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9050 (p : Pattern) (guard : d1436 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1435 p = 1 := by simpa only [d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9049 p hg
    simpa only [d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9051 (p : Pattern) (guard : d1494 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1432 p = 1 := by simpa only [d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9046 p hg
    simpa only [d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9052 (p : Pattern) (guard : d1495 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1494 p = 1 := by simpa only [d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9051 p hg
    simpa only [d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9053 (p : Pattern) (guard : d1496 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1495 p = 1 := by simpa only [d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9052 p hg
    simpa only [d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9054 (p : Pattern) (guard : d1497 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1496 p = 1 := by simpa only [d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9053 p hg
    simpa only [d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9055 (p : Pattern) (guard : d53741 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1436 p = 1 := by simpa only [d53741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9050 p hg
    simpa only [d53741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1497 p = 1 := by simpa only [d53741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9054 p hg
    simpa only [d53741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9056 (p : Pattern) (guard : d53742 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53741 p = 1 := by simpa only [d53742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9055 p hg
    simpa only [d53742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9057 (p : Pattern) (guard : d53743 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d53742 p = 1 := by simpa only [d53743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9056 p hg
    simpa only [d53743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9058 (p : Pattern) (guard : d53744 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53743 p = 1 := by simpa only [d53744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9057 p hg
    simpa only [d53744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9059 (p : Pattern) (guard : d53745 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53744 p = 1 := by simpa only [d53745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9058 p hg
    simpa only [d53745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9060 (p : Pattern) (guard : d53746 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53746, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53746, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53745 p = 1 := by simpa only [d53746, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9059 p hg
    simpa only [d53746, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9061 (p : Pattern) (guard : d53747 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53746 p = 1 := by simpa only [d53747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9060 p hg
    simpa only [d53747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9062 (p : Pattern) (guard : d53748 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53747 p = 1 := by simpa only [d53748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9061 p hg
    simpa only [d53748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9063 (p : Pattern) (guard : d53749 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53748 p = 1 := by simpa only [d53749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9062 p hg
    simpa only [d53749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9064 (p : Pattern) (guard : d53750 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53749 p = 1 := by simpa only [d53750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9063 p hg
    simpa only [d53750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9065 (p : Pattern) (guard : d53751 p = 1) : d47865 p ≤ (-2 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53750 p = 1 := by simpa only [d53751, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9064 p hg
    simpa only [d53751, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53751, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8121 p hg
    simpa only [d53751, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9066 (p : Pattern) (guard : d53752 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d53740 p = 1 := by simpa only [d53752, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8909 p hg
    simpa only [d53752, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53751 p = 1 := by simpa only [d53752, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9065 p hg
    simpa only [d53752, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9067 (p : Pattern) (guard : d53753 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53752 p = 1 := by simpa only [d53753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9066 p hg
    simpa only [d53753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9068 (p : Pattern) (guard : d53754 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53753 p = 1 := by simpa only [d53754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9067 p hg
    simpa only [d53754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9069 (p : Pattern) (guard : d53755 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53754 p = 1 := by simpa only [d53755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9068 p hg
    simpa only [d53755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9070 (p : Pattern) (guard : d53756 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53755 p = 1 := by simpa only [d53756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9069 p hg
    simpa only [d53756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9071 (p : Pattern) (guard : d53757 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53756 p = 1 := by simpa only [d53757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9070 p hg
    simpa only [d53757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9072 (p : Pattern) (guard : d53758 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53757 p = 1 := by simpa only [d53758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9071 p hg
    simpa only [d53758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9073 (p : Pattern) (guard : d53759 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53758 p = 1 := by simpa only [d53759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9072 p hg
    simpa only [d53759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9074 (p : Pattern) (guard : d53760 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53759 p = 1 := by simpa only [d53760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9073 p hg
    simpa only [d53760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9075 (p : Pattern) (guard : d53761 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d53732 p = 1 := by simpa only [d53761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8700 p hg
    simpa only [d53761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53760 p = 1 := by simpa only [d53761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9074 p hg
    simpa only [d53761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9076 (p : Pattern) (guard : d1199 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8701 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9077 (p : Pattern) (guard : d1200 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9076 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9078 (p : Pattern) (guard : d1201 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9077 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9079 (p : Pattern) (guard : d308 p = 1) : d4 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare9080 (p : Pattern) (guard : d1519 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9079 p hg
    simpa only [d1519, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7940 p hg
    simpa only [d1519, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9081 (p : Pattern) (guard : d1520 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8287 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9080 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9082 (p : Pattern) (guard : d1521 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8468 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9081 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9083 (p : Pattern) (guard : d1522 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8701 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9082 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9084 (p : Pattern) (guard : d1523 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8705 p hg
    simpa only [d1523, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8286 p hg
    simpa only [d1523, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9085 (p : Pattern) (guard : d1524 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9084 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8706 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9086 (p : Pattern) (guard : d1525 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9085 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9087 (p : Pattern) (guard : d1526 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9086 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9088 (p : Pattern) (guard : d1527 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9083 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9087 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9089 (p : Pattern) (guard : d1528 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8709 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9090 (p : Pattern) (guard : d1529 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9088 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9089 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9091 (p : Pattern) (guard : d1530 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9078 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9090 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9092 (p : Pattern) (guard : d1203 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8714 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9093 (p : Pattern) (guard : d1204 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9092 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9094 (p : Pattern) (guard : d1205 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9093 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9095 (p : Pattern) (guard : d1531 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9080 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9096 (p : Pattern) (guard : d1532 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9081 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9095 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9097 (p : Pattern) (guard : d1533 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8714 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9096 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9098 (p : Pattern) (guard : d1534 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9097 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9099 (p : Pattern) (guard : d1535 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9098 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9100 (p : Pattern) (guard : d1536 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9094 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9099 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9101 (p : Pattern) (guard : d1537 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9091 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9100 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9102 (p : Pattern) (guard : d1538 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9101 p hg
    simpa only [d1538, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1538, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9103 (p : Pattern) (guard : d1539 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9082 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9096 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9104 (p : Pattern) (guard : d1540 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9080 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7941 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9105 (p : Pattern) (guard : d1541 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9104 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9106 (p : Pattern) (guard : d1542 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9086 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9105 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9107 (p : Pattern) (guard : d1543 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9103 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9106 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9108 (p : Pattern) (guard : d1544 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8721 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9109 (p : Pattern) (guard : d1545 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9107 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9108 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9110 (p : Pattern) (guard : d1546 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9090 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9109 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9111 (p : Pattern) (guard : d1547 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9095 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9112 (p : Pattern) (guard : d1548 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9096 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9111 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9113 (p : Pattern) (guard : d1549 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9112 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9114 (p : Pattern) (guard : d1550 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9113 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9115 (p : Pattern) (guard : d1551 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9099 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9114 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9116 (p : Pattern) (guard : d1552 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9110 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9115 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9117 (p : Pattern) (guard : d1553 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9116 p hg
    simpa only [d1553, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1553, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9118 (p : Pattern) (guard : d1554 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9102 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9117 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9119 (p : Pattern) (guard : d1555 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9118 p hg
    simpa only [d1555, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d1555, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9120 (p : Pattern) (guard : d1556 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9119 p hg
    simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9121 (p : Pattern) (guard : d1557 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1557, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9120 p hg
    simpa only [d1557, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9122 (p : Pattern) (guard : d1558 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9121 p hg
    simpa only [d1558, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d1558, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9123 (p : Pattern) (guard : d1559 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9105 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9124 (p : Pattern) (guard : d1560 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9112 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9123 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9125 (p : Pattern) (guard : d1561 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9124 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8743 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9126 (p : Pattern) (guard : d1562 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9109 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9125 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9127 (p : Pattern) (guard : d1563 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9111 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9128 (p : Pattern) (guard : d1564 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9127 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9129 (p : Pattern) (guard : d1565 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9128 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9130 (p : Pattern) (guard : d1566 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9114 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9129 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9131 (p : Pattern) (guard : d1567 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9126 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9130 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9132 (p : Pattern) (guard : d1568 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9131 p hg
    simpa only [d1568, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1568, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9133 (p : Pattern) (guard : d1569 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9117 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9132 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9134 (p : Pattern) (guard : d1570 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9133 p hg
    simpa only [d1570, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d1570, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9135 (p : Pattern) (guard : d1571 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9134 p hg
    simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9136 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1572, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9135 p hg
    simpa only [d1572, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9137 (p : Pattern) (guard : d1573 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9136 p hg
    simpa only [d1573, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d1573, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9138 (p : Pattern) (guard : d1574 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9122 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1573 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9137 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9139 (p : Pattern) (guard : d1575 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9123 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9140 (p : Pattern) (guard : d1576 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9139 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8743 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9141 (p : Pattern) (guard : d1577 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9140 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9129 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9142 (p : Pattern) (guard : d1578 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9129 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9143 (p : Pattern) (guard : d1579 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9141 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9142 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9144 (p : Pattern) (guard : d1580 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9143 p hg
    simpa only [d1580, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1580, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9145 (p : Pattern) (guard : d1581 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9132 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9144 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9146 (p : Pattern) (guard : d1582 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9145 p hg
    simpa only [d1582, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d1582, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9147 (p : Pattern) (guard : d1583 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9146 p hg
    simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9148 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1584, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9147 p hg
    simpa only [d1584, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9149 (p : Pattern) (guard : d1585 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9148 p hg
    simpa only [d1585, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d1585, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9150 (p : Pattern) (guard : d1586 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9137 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1585 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9149 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9151 (p : Pattern) (guard : d1587 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1574 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9138 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1586 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9150 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9152 (p : Pattern) (guard : d1588 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9149 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9153 (p : Pattern) (guard : d1589 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1586 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9150 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1588 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9152 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9154 (p : Pattern) (guard : d1590 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1587 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9151 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1589 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9153 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9155 (p : Pattern) (guard : d1591 p = 1) : d47686 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1591, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d1591, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1590 p = 1 := by simpa only [d1591, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9154 p hg
    simpa only [d1591, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9156 (p : Pattern) (guard : d1592 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1592, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d1592, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1591 p = 1 := by simpa only [d1592, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9155 p hg
    simpa only [d1592, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9157 (p : Pattern) (guard : d1593 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9140 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9158 (p : Pattern) (guard : d1594 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9157 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9159 (p : Pattern) (guard : d1595 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9158 p hg
    simpa only [d1595, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1595, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9160 (p : Pattern) (guard : d1596 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9159 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7952 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9161 (p : Pattern) (guard : d1597 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9160 p hg
    simpa only [d1597, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d1597, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9162 (p : Pattern) (guard : d1598 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1597 p = 1 := by simpa only [d1598, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9161 p hg
    simpa only [d1598, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1598, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d1598, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9163 (p : Pattern) (guard : d1599 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1599, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1599, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1598 p = 1 := by simpa only [d1599, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9162 p hg
    simpa only [d1599, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9164 (p : Pattern) (guard : d1600 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1599 p = 1 := by simpa only [d1600, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9163 p hg
    simpa only [d1600, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1600, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d1600, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9165 (p : Pattern) (guard : d1601 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1600 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9164 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9166 (p : Pattern) (guard : d1602 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9152 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1601 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9165 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9167 (p : Pattern) (guard : d1603 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1589 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9153 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1602 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9166 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9168 (p : Pattern) (guard : d1604 p = 1) : d47686 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1604, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d1604, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1603 p = 1 := by simpa only [d1604, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9167 p hg
    simpa only [d1604, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9169 (p : Pattern) (guard : d1605 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1605, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d1605, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1604 p = 1 := by simpa only [d1605, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9168 p hg
    simpa only [d1605, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9170 (p : Pattern) (guard : d1606 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1592 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9156 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1605 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9169 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9171 (p : Pattern) (guard : d1607 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1605 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9169 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9172 (p : Pattern) (guard : d1608 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1606 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9170 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1607 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9171 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9173 (p : Pattern) (guard : d1609 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1608 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9172 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9174 (p : Pattern) (guard : d1610 p = 1) : d47699 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1609 p = 1 := by simpa only [d1610, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9173 p hg
    simpa only [d1610, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1610, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d1610, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9175 (p : Pattern) (guard : d1611 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1611, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d1611, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1610 p = 1 := by simpa only [d1611, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9174 p hg
    simpa only [d1611, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9176 (p : Pattern) (guard : d1612 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1607 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9171 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9177 (p : Pattern) (guard : d1613 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1612 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9176 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9178 (p : Pattern) (guard : d1614 p = 1) : d47699 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1613 p = 1 := by simpa only [d1614, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9177 p hg
    simpa only [d1614, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1614, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d1614, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9179 (p : Pattern) (guard : d1615 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1615, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d1615, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1614 p = 1 := by simpa only [d1615, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9178 p hg
    simpa only [d1615, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9180 (p : Pattern) (guard : d1616 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1611 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9175 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1615 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9179 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9181 (p : Pattern) (guard : d1617 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1616 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9180 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9182 (p : Pattern) (guard : d1618 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1617 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9181 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9183 (p : Pattern) (guard : d1619 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1618 p = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9182 p hg
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9184 (p : Pattern) (guard : d1620 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1615 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9179 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9185 (p : Pattern) (guard : d1621 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1620 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9184 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9186 (p : Pattern) (guard : d1622 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1621 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9185 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9187 (p : Pattern) (guard : d1623 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1622 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9186 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9188 (p : Pattern) (guard : d1624 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1619 p = 1 := by simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9183 p hg
    simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1623 p = 1 := by simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9187 p hg
    simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9189 (p : Pattern) (guard : d1625 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1624 p = 1 := by simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9188 p hg
    simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9190 (p : Pattern) (guard : d1626 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1625 p = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9189 p hg
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9191 (p : Pattern) (guard : d1627 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1626 p = 1 := by simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9190 p hg
    simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9192 (p : Pattern) (guard : d1628 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1627 p = 1 := by simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9191 p hg
    simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9193 (p : Pattern) (guard : d1629 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1628 p = 1 := by simpa only [d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9192 p hg
    simpa only [d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9194 (p : Pattern) (guard : d1632 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1618 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9182 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9195 (p : Pattern) (guard : d1633 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1622 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9186 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9196 (p : Pattern) (guard : d1634 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1632 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9194 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1633 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9195 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9197 (p : Pattern) (guard : d1635 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1634 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9196 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9198 (p : Pattern) (guard : d1636 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1635 p = 1 := by simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9197 p hg
    simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9199 (p : Pattern) (guard : d1637 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1636 p = 1 := by simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9198 p hg
    simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9200 (p : Pattern) (guard : d1638 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1637 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9199 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9201 (p : Pattern) (guard : d1639 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1628 p = 1 := by simpa only [d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9192 p hg
    simpa only [d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1638 p = 1 := by simpa only [d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9200 p hg
    simpa only [d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9202 (p : Pattern) (guard : d1640 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d1629 p = 1 := by simpa only [d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9193 p hg
    simpa only [d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1639 p = 1 := by simpa only [d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9201 p hg
    simpa only [d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9203 (p : Pattern) (guard : d1641 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d1640 p = 1 := by simpa only [d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9202 p hg
    simpa only [d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9204 (p : Pattern) (guard : d53762 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d1641 p = 1 := by simpa only [d53762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9203 p hg
    simpa only [d53762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9205 (p : Pattern) (guard : d53763 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53762 p = 1 := by simpa only [d53763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9204 p hg
    simpa only [d53763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9206 (p : Pattern) (guard : d1199 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8809 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9207 (p : Pattern) (guard : d1200 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9206 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9208 (p : Pattern) (guard : d1201 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9207 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9209 (p : Pattern) (guard : d308 p = 1) : d5 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds5 p
  have hb := bounds12 p
  omega
theorem compare9210 (p : Pattern) (guard : d1519 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9209 p hg
    simpa only [d1519, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8002 p hg
    simpa only [d1519, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9211 (p : Pattern) (guard : d1520 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8345 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9210 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9212 (p : Pattern) (guard : d1521 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8540 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9211 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9213 (p : Pattern) (guard : d1522 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8809 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9212 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9214 (p : Pattern) (guard : d1523 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8813 p hg
    simpa only [d1523, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8344 p hg
    simpa only [d1523, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9215 (p : Pattern) (guard : d1524 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9214 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8814 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9216 (p : Pattern) (guard : d1525 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9215 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9217 (p : Pattern) (guard : d1526 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9216 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9218 (p : Pattern) (guard : d1527 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9213 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9217 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9219 (p : Pattern) (guard : d1528 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8817 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9220 (p : Pattern) (guard : d1529 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9218 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9219 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9221 (p : Pattern) (guard : d1530 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9208 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9220 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9222 (p : Pattern) (guard : d1203 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8822 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9223 (p : Pattern) (guard : d1204 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9222 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9224 (p : Pattern) (guard : d1205 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9223 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9225 (p : Pattern) (guard : d1531 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9210 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9226 (p : Pattern) (guard : d1532 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9211 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9225 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9227 (p : Pattern) (guard : d1533 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8822 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9226 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9228 (p : Pattern) (guard : d1534 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9227 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9229 (p : Pattern) (guard : d1535 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9228 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9230 (p : Pattern) (guard : d1536 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9224 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9229 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9231 (p : Pattern) (guard : d1537 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9221 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9230 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9232 (p : Pattern) (guard : d1538 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9231 p hg
    simpa only [d1538, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1538, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9233 (p : Pattern) (guard : d1539 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9212 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9226 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9234 (p : Pattern) (guard : d1540 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9210 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8003 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9235 (p : Pattern) (guard : d1541 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9234 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9236 (p : Pattern) (guard : d1542 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9216 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9235 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9237 (p : Pattern) (guard : d1543 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9233 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9236 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9238 (p : Pattern) (guard : d1544 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8829 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9239 (p : Pattern) (guard : d1545 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9237 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9238 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9240 (p : Pattern) (guard : d1546 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9220 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9239 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9241 (p : Pattern) (guard : d1547 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9225 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9242 (p : Pattern) (guard : d1548 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9226 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9241 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9243 (p : Pattern) (guard : d1549 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9242 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9244 (p : Pattern) (guard : d1550 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9243 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9245 (p : Pattern) (guard : d1551 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9229 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9244 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9246 (p : Pattern) (guard : d1552 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9240 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9245 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9247 (p : Pattern) (guard : d1553 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9246 p hg
    simpa only [d1553, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1553, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9248 (p : Pattern) (guard : d1554 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9232 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9247 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9249 (p : Pattern) (guard : d1555 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9248 p hg
    simpa only [d1555, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1555, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
