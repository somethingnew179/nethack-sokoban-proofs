import NetHack.Soko22Hazard87.Compare023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6000 (p : Pattern) (guard : d6975 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6973 p = 1 := by simpa only [d6975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5998 p hg
    simpa only [d6975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6974 p = 1 := by simpa only [d6975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5999 p hg
    simpa only [d6975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6001 (p : Pattern) (guard : d82153 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6975 p = 1 := by simpa only [d82153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6000 p hg
    simpa only [d82153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6002 (p : Pattern) (guard : d6266 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6256 p = 1 := by simpa only [d6266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5979 p hg
    simpa only [d6266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6003 (p : Pattern) (guard : d6320 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6266 p = 1 := by simpa only [d6320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d6320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6004 (p : Pattern) (guard : d6321 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6320 p = 1 := by simpa only [d6321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6003 p hg
    simpa only [d6321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6005 (p : Pattern) (guard : d82154 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82153 p = 1 := by simpa only [d82154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6001 p hg
    simpa only [d82154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6321 p = 1 := by simpa only [d82154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6004 p hg
    simpa only [d82154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6006 (p : Pattern) (guard : d82155 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d82155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5997 p hg
    simpa only [d82155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82154 p = 1 := by simpa only [d82155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6005 p hg
    simpa only [d82155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6007 (p : Pattern) (guard : d82156 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d82156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5992 p hg
    simpa only [d82156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82155 p = 1 := by simpa only [d82156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6006 p hg
    simpa only [d82156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6008 (p : Pattern) (guard : d82157 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d82151 p = 1 := by simpa only [d82157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5985 p hg
    simpa only [d82157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82156 p = 1 := by simpa only [d82157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6007 p hg
    simpa only [d82157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6009 (p : Pattern) (guard : d82158 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d82152 p = 1 := by simpa only [d82158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5986 p hg
    simpa only [d82158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82157 p = 1 := by simpa only [d82158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6008 p hg
    simpa only [d82158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6010 (p : Pattern) (guard : d6982 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6966 p = 1 := by simpa only [d6982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5974 p hg
    simpa only [d6982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1162 p = 1 := by simpa only [d6982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5877 p hg
    simpa only [d6982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6011 (p : Pattern) (guard : d6983 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6982 p = 1 := by simpa only [d6983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6010 p hg
    simpa only [d6983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6012 (p : Pattern) (guard : d6984 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d6983 p = 1 := by simpa only [d6984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6011 p hg
    simpa only [d6984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6013 (p : Pattern) (guard : d6985 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6984 p = 1 := by simpa only [d6985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d6985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6014 (p : Pattern) (guard : d6986 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6985 p = 1 := by simpa only [d6986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6013 p hg
    simpa only [d6986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6015 (p : Pattern) (guard : d1350 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1162 p = 1 := by simpa only [d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5877 p hg
    simpa only [d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6016 (p : Pattern) (guard : d1351 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1350 p = 1 := by simpa only [d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6015 p hg
    simpa only [d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6017 (p : Pattern) (guard : d1352 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1351 p = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6016 p hg
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6018 (p : Pattern) (guard : d1353 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1352 p = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6017 p hg
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6019 (p : Pattern) (guard : d1354 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1353 p = 1 := by simpa only [d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6018 p hg
    simpa only [d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6020 (p : Pattern) (guard : d6987 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6986 p = 1 := by simpa only [d6987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6014 p hg
    simpa only [d6987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1354 p = 1 := by simpa only [d6987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d6987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6021 (p : Pattern) (guard : d1356 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5887 p hg
    simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6022 (p : Pattern) (guard : d1357 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1356 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6023 (p : Pattern) (guard : d1358 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1357 p = 1 := by simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6022 p hg
    simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6024 (p : Pattern) (guard : d1359 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1358 p = 1 := by simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6023 p hg
    simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6025 (p : Pattern) (guard : d1360 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1359 p = 1 := by simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6024 p hg
    simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6026 (p : Pattern) (guard : d1361 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1354 p = 1 := by simpa only [d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1360 p = 1 := by simpa only [d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6027 (p : Pattern) (guard : d6988 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d6987 p = 1 := by simpa only [d6988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6020 p hg
    simpa only [d6988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1361 p = 1 := by simpa only [d6988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6026 p hg
    simpa only [d6988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6028 (p : Pattern) (guard : d82159 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82158 p = 1 := by simpa only [d82159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6009 p hg
    simpa only [d82159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6988 p = 1 := by simpa only [d82159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6027 p hg
    simpa only [d82159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6029 (p : Pattern) (guard : d82160 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82159 p = 1 := by simpa only [d82160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6028 p hg
    simpa only [d82160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6030 (p : Pattern) (guard : d82161 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d1181 p = 1 := by simpa only [d82161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d82161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82160 p = 1 := by simpa only [d82161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6029 p hg
    simpa only [d82161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6031 (p : Pattern) (guard : d1199 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5560 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6032 (p : Pattern) (guard : d1200 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6033 (p : Pattern) (guard : d1201 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6032 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6034 (p : Pattern) (guard : d1202 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6033 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d823 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6035 (p : Pattern) (guard : d1203 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5566 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6036 (p : Pattern) (guard : d1204 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6035 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6037 (p : Pattern) (guard : d1205 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6036 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6038 (p : Pattern) (guard : d1206 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6037 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5569 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6039 (p : Pattern) (guard : d1207 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1202 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6034 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1206 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6038 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6040 (p : Pattern) (guard : d1208 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1207 p = 1 := by simpa only [d1208, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6039 p hg
    simpa only [d1208, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1208, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d1208, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6041 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6042 (p : Pattern) (guard : d1084 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6041 p hg
    simpa only [d1084, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4680 p hg
    simpa only [d1084, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6043 (p : Pattern) (guard : d1085 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6042 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6044 (p : Pattern) (guard : d1086 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6045 (p : Pattern) (guard : d1087 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6044 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6046 (p : Pattern) (guard : d1088 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5186 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6045 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6047 (p : Pattern) (guard : d1089 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6046 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6048 (p : Pattern) (guard : d1090 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6047 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6049 (p : Pattern) (guard : d1091 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6048 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5570 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6050 (p : Pattern) (guard : d1092 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6049 p hg
    simpa only [d1092, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d1092, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6051 (p : Pattern) (guard : d1209 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1208 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6040 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6050 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6052 (p : Pattern) (guard : d1210 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6051 p hg
    simpa only [d1210, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1210, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6053 (p : Pattern) (guard : d1211 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1210 p = 1 := by simpa only [d1211, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6052 p hg
    simpa only [d1211, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1211, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1211, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6054 (p : Pattern) (guard : d1212 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1212, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d1212, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1211 p = 1 := by simpa only [d1212, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6053 p hg
    simpa only [d1212, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6055 (p : Pattern) (guard : d1213 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1212 p = 1 := by simpa only [d1213, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6054 p hg
    simpa only [d1213, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1213, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1213, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6056 (p : Pattern) (guard : d1093 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6044 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4471 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6057 (p : Pattern) (guard : d1094 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4890 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6056 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6058 (p : Pattern) (guard : d1095 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6057 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6059 (p : Pattern) (guard : d1096 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6047 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6058 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6060 (p : Pattern) (guard : d1097 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6059 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5195 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6061 (p : Pattern) (guard : d1098 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6060 p hg
    simpa only [d1098, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d1098, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6062 (p : Pattern) (guard : d1099 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6050 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6063 (p : Pattern) (guard : d1100 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6062 p hg
    simpa only [d1100, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1100, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6064 (p : Pattern) (guard : d1101 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6063 p hg
    simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6065 (p : Pattern) (guard : d1102 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6064 p hg
    simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6066 (p : Pattern) (guard : d1103 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6065 p hg
    simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6067 (p : Pattern) (guard : d1214 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1213 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6055 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1103 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6066 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6068 (p : Pattern) (guard : d1104 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4684 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4472 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6069 (p : Pattern) (guard : d1105 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6068 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6070 (p : Pattern) (guard : d1106 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6058 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6069 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6071 (p : Pattern) (guard : d1107 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6070 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6072 (p : Pattern) (guard : d1108 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6071 p hg
    simpa only [d1108, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d1108, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6073 (p : Pattern) (guard : d1109 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6072 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6074 (p : Pattern) (guard : d1110 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6073 p hg
    simpa only [d1110, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1110, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6075 (p : Pattern) (guard : d1111 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6074 p hg
    simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6076 (p : Pattern) (guard : d1112 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6075 p hg
    simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6077 (p : Pattern) (guard : d1113 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6076 p hg
    simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6078 (p : Pattern) (guard : d1114 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6066 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6077 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6079 (p : Pattern) (guard : d1215 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1214 p = 1 := by simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6067 p hg
    simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1114 p = 1 := by simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6078 p hg
    simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6080 (p : Pattern) (guard : d1115 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4472 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6081 (p : Pattern) (guard : d1116 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6080 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6082 (p : Pattern) (guard : d1117 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6081 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4474 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6083 (p : Pattern) (guard : d1118 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6082 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6084 (p : Pattern) (guard : d1119 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6083 p hg
    simpa only [d1119, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d1119, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6085 (p : Pattern) (guard : d1120 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6072 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6086 (p : Pattern) (guard : d1121 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6085 p hg
    simpa only [d1121, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1121, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6087 (p : Pattern) (guard : d1122 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6086 p hg
    simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6088 (p : Pattern) (guard : d1123 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6087 p hg
    simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6089 (p : Pattern) (guard : d1124 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6088 p hg
    simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6090 (p : Pattern) (guard : d1125 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6077 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6089 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6091 (p : Pattern) (guard : d1126 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1114 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6078 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6090 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6092 (p : Pattern) (guard : d1216 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1215 p = 1 := by simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6079 p hg
    simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6091 p hg
    simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6093 (p : Pattern) (guard : d1217 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1217, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d1217, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1216 p = 1 := by simpa only [d1217, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6092 p hg
    simpa only [d1217, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6094 (p : Pattern) (guard : d1218 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1218, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d1218, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1217 p = 1 := by simpa only [d1218, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6093 p hg
    simpa only [d1218, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6095 (p : Pattern) (guard : d1127 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6089 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6096 (p : Pattern) (guard : d1128 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6090 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1127 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6095 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6097 (p : Pattern) (guard : d1129 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6091 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1128 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6096 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6098 (p : Pattern) (guard : d1130 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1130, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d1130, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1129 p = 1 := by simpa only [d1130, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6097 p hg
    simpa only [d1130, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6099 (p : Pattern) (guard : d1131 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1131, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d1131, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1130 p = 1 := by simpa only [d1131, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6098 p hg
    simpa only [d1131, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6100 (p : Pattern) (guard : d1219 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1218 p = 1 := by simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1131 p = 1 := by simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6099 p hg
    simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6101 (p : Pattern) (guard : d1132 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6081 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6102 (p : Pattern) (guard : d1133 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6101 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6103 (p : Pattern) (guard : d1134 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6102 p hg
    simpa only [d1134, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d1134, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6104 (p : Pattern) (guard : d1135 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6103 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6105 (p : Pattern) (guard : d1136 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6104 p hg
    simpa only [d1136, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1136, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6106 (p : Pattern) (guard : d1137 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1136 p = 1 := by simpa only [d1137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6105 p hg
    simpa only [d1137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6107 (p : Pattern) (guard : d1138 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1138, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d1138, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1137 p = 1 := by simpa only [d1138, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6106 p hg
    simpa only [d1138, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6108 (p : Pattern) (guard : d1139 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1138 p = 1 := by simpa only [d1139, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6107 p hg
    simpa only [d1139, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1139, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1139, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6109 (p : Pattern) (guard : d1140 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1139 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6108 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6110 (p : Pattern) (guard : d1141 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6095 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1140 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6109 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6111 (p : Pattern) (guard : d1142 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1128 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6096 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1141 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6110 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6112 (p : Pattern) (guard : d1143 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1143, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d1143, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1142 p = 1 := by simpa only [d1143, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6111 p hg
    simpa only [d1143, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6113 (p : Pattern) (guard : d1144 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1144, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d1144, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1143 p = 1 := by simpa only [d1144, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6112 p hg
    simpa only [d1144, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6114 (p : Pattern) (guard : d1145 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1131 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6099 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1144 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6113 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6115 (p : Pattern) (guard : d1220 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1219 p = 1 := by simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6100 p hg
    simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1145 p = 1 := by simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6114 p hg
    simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6116 (p : Pattern) (guard : d1221 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1220 p = 1 := by simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6115 p hg
    simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6117 (p : Pattern) (guard : d1222 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1221 p = 1 := by simpa only [d1222, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6116 p hg
    simpa only [d1222, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1222, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d1222, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6118 (p : Pattern) (guard : d1223 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1223, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d1223, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1222 p = 1 := by simpa only [d1223, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6117 p hg
    simpa only [d1223, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6119 (p : Pattern) (guard : d6954 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1131 p = 1 := by simpa only [d6954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6099 p hg
    simpa only [d6954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d6954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6120 (p : Pattern) (guard : d5009 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d5009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6090 p hg
    simpa only [d5009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d5009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6121 (p : Pattern) (guard : d5010 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5190 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4470 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6122 (p : Pattern) (guard : d5011 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5010 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6121 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4471 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6123 (p : Pattern) (guard : d5012 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6122 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4472 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6124 (p : Pattern) (guard : d5013 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5012 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6123 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6125 (p : Pattern) (guard : d5014 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6058 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5013 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6124 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6126 (p : Pattern) (guard : d5015 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5014 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6125 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6127 (p : Pattern) (guard : d5016 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5015 p = 1 := by simpa only [d5016, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6126 p hg
    simpa only [d5016, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5016, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d5016, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6128 (p : Pattern) (guard : d5017 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5016 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6127 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6129 (p : Pattern) (guard : d5018 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6128 p hg
    simpa only [d5018, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d5018, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6130 (p : Pattern) (guard : d5019 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6129 p hg
    simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6131 (p : Pattern) (guard : d5020 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6130 p hg
    simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6132 (p : Pattern) (guard : d5021 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6131 p hg
    simpa only [d5021, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d5021, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6133 (p : Pattern) (guard : d5022 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6132 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6134 (p : Pattern) (guard : d5023 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d5023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6133 p hg
    simpa only [d5023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d5023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6135 (p : Pattern) (guard : d5024 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d5009 p = 1 := by simpa only [d5024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6120 p hg
    simpa only [d5024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5023 p = 1 := by simpa only [d5024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6134 p hg
    simpa only [d5024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6136 (p : Pattern) (guard : d5025 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5025, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d5025, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5024 p = 1 := by simpa only [d5025, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6135 p hg
    simpa only [d5025, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6137 (p : Pattern) (guard : d5026 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5026, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d5026, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5025 p = 1 := by simpa only [d5026, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6136 p hg
    simpa only [d5026, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6138 (p : Pattern) (guard : d5027 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d5026 p = 1 := by simpa only [d5027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6137 p hg
    simpa only [d5027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d5027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6139 (p : Pattern) (guard : d6955 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d6954 p = 1 := by simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6119 p hg
    simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5027 p = 1 := by simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6138 p hg
    simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6140 (p : Pattern) (guard : d6956 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6955 p = 1 := by simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6139 p hg
    simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6141 (p : Pattern) (guard : d6957 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6956 p = 1 := by simpa only [d6957, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6140 p hg
    simpa only [d6957, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6957, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d6957, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6142 (p : Pattern) (guard : d6958 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6958, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d6958, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6957 p = 1 := by simpa only [d6958, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6141 p hg
    simpa only [d6958, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6143 (p : Pattern) (guard : d6959 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1223 p = 1 := by simpa only [d6959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6118 p hg
    simpa only [d6959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6958 p = 1 := by simpa only [d6959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6142 p hg
    simpa only [d6959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6144 (p : Pattern) (guard : d6960 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6959 p = 1 := by simpa only [d6960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6143 p hg
    simpa only [d6960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6145 (p : Pattern) (guard : d6961 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6960 p = 1 := by simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6144 p hg
    simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6146 (p : Pattern) (guard : d6973 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6961 p = 1 := by simpa only [d6973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6145 p hg
    simpa only [d6973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6147 (p : Pattern) (guard : d5028 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1145 p = 1 := by simpa only [d5028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6114 p hg
    simpa only [d5028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5027 p = 1 := by simpa only [d5028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6138 p hg
    simpa only [d5028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6148 (p : Pattern) (guard : d5029 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d5028 p = 1 := by simpa only [d5029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6147 p hg
    simpa only [d5029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d5029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6149 (p : Pattern) (guard : d5030 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5029 p = 1 := by simpa only [d5030, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6148 p hg
    simpa only [d5030, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5030, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d5030, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6150 (p : Pattern) (guard : d5031 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5031, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d5031, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5030 p = 1 := by simpa only [d5031, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6149 p hg
    simpa only [d5031, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6151 (p : Pattern) (guard : d1146 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1144 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6113 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6152 (p : Pattern) (guard : d1151 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1146 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6151 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6153 (p : Pattern) (guard : d1152 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6154 (p : Pattern) (guard : d1153 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1152 p = 1 := by simpa only [d1153, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6153 p hg
    simpa only [d1153, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1153, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d1153, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6155 (p : Pattern) (guard : d1154 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1154, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d1154, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1153 p = 1 := by simpa only [d1154, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6154 p hg
    simpa only [d1154, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6156 (p : Pattern) (guard : d6963 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d5031 p = 1 := by simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6150 p hg
    simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1154 p = 1 := by simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6155 p hg
    simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6157 (p : Pattern) (guard : d6964 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6963 p = 1 := by simpa only [d6964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6156 p hg
    simpa only [d6964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6158 (p : Pattern) (guard : d6965 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6964 p = 1 := by simpa only [d6965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6157 p hg
    simpa only [d6965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6159 (p : Pattern) (guard : d6974 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6965 p = 1 := by simpa only [d6974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6158 p hg
    simpa only [d6974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6160 (p : Pattern) (guard : d6975 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6973 p = 1 := by simpa only [d6975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6146 p hg
    simpa only [d6975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6974 p = 1 := by simpa only [d6975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6159 p hg
    simpa only [d6975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6161 (p : Pattern) (guard : d82153 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6975 p = 1 := by simpa only [d82153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6160 p hg
    simpa only [d82153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6162 (p : Pattern) (guard : d1147 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1145 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6114 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1146 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6151 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6163 (p : Pattern) (guard : d1148 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1147 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6162 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6164 (p : Pattern) (guard : d1149 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d1149, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d1149, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1149, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d1149, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6165 (p : Pattern) (guard : d1150 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d1150, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1149 p = 1 := by simpa only [d1150, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6164 p hg
    simpa only [d1150, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6166 (p : Pattern) (guard : d6254 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d6254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6165 p hg
    simpa only [d6254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6167 (p : Pattern) (guard : d6255 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6254 p = 1 := by simpa only [d6255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6166 p hg
    simpa only [d6255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6168 (p : Pattern) (guard : d6256 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6255 p = 1 := by simpa only [d6256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6167 p hg
    simpa only [d6256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6169 (p : Pattern) (guard : d6266 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6256 p = 1 := by simpa only [d6266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6168 p hg
    simpa only [d6266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6170 (p : Pattern) (guard : d6320 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6266 p = 1 := by simpa only [d6320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6169 p hg
    simpa only [d6320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6171 (p : Pattern) (guard : d6321 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6320 p = 1 := by simpa only [d6321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6170 p hg
    simpa only [d6321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6172 (p : Pattern) (guard : d82154 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82153 p = 1 := by simpa only [d82154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6161 p hg
    simpa only [d82154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6321 p = 1 := by simpa only [d82154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6171 p hg
    simpa only [d82154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6173 (p : Pattern) (guard : d82162 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82154 p = 1 := by simpa only [d82162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6172 p hg
    simpa only [d82162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6174 (p : Pattern) (guard : d82163 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82162 p = 1 := by simpa only [d82163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6173 p hg
    simpa only [d82163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6175 (p : Pattern) (guard : d82164 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82164, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82164, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82163 p = 1 := by simpa only [d82164, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6174 p hg
    simpa only [d82164, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6176 (p : Pattern) (guard : d82165 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82164 p = 1 := by simpa only [d82165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6175 p hg
    simpa only [d82165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6177 (p : Pattern) (guard : d1159 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1154 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6155 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6178 (p : Pattern) (guard : d1160 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1159 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6177 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6179 (p : Pattern) (guard : d1161 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1160 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6178 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6180 (p : Pattern) (guard : d1172 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1161 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6179 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6181 (p : Pattern) (guard : d1356 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6180 p hg
    simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6182 (p : Pattern) (guard : d1357 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1356 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6181 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6183 (p : Pattern) (guard : d1358 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1357 p = 1 := by simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6182 p hg
    simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6184 (p : Pattern) (guard : d1359 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1358 p = 1 := by simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6183 p hg
    simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6185 (p : Pattern) (guard : d1360 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1359 p = 1 := by simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6184 p hg
    simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6186 (p : Pattern) (guard : d1370 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1370, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1370, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1360 p = 1 := by simpa only [d1370, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6185 p hg
    simpa only [d1370, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6187 (p : Pattern) (guard : d1371 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1370 p = 1 := by simpa only [d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6186 p hg
    simpa only [d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6188 (p : Pattern) (guard : d82166 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82165 p = 1 := by simpa only [d82166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6176 p hg
    simpa only [d82166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1371 p = 1 := by simpa only [d82166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6187 p hg
    simpa only [d82166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6189 (p : Pattern) (guard : d82167 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82166 p = 1 := by simpa only [d82167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6188 p hg
    simpa only [d82167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6190 (p : Pattern) (guard : d82168 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82167 p = 1 := by simpa only [d82168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6189 p hg
    simpa only [d82168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6191 (p : Pattern) (guard : d82169 p = 1) : d47768 p ≤ (-1 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82161 p = 1 := by simpa only [d82169, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6030 p hg
    simpa only [d82169, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82168 p = 1 := by simpa only [d82169, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6190 p hg
    simpa only [d82169, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6192 (p : Pattern) (guard : d1199 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5664 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6193 (p : Pattern) (guard : d1200 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6192 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6194 (p : Pattern) (guard : d1201 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6193 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6195 (p : Pattern) (guard : d1202 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6194 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d823 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5667 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6196 (p : Pattern) (guard : d1203 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6197 (p : Pattern) (guard : d1204 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6196 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6198 (p : Pattern) (guard : d1205 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6197 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6199 (p : Pattern) (guard : d1206 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6198 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6200 (p : Pattern) (guard : d1207 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1202 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6195 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1206 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6199 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6201 (p : Pattern) (guard : d1208 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1207 p = 1 := by simpa only [d1208, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6200 p hg
    simpa only [d1208, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1208, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d1208, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6202 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6203 (p : Pattern) (guard : d1084 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6202 p hg
    simpa only [d1084, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4722 p hg
    simpa only [d1084, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6204 (p : Pattern) (guard : d1085 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6203 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6205 (p : Pattern) (guard : d1086 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6204 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6206 (p : Pattern) (guard : d1087 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6205 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6207 (p : Pattern) (guard : d1088 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5273 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6206 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6208 (p : Pattern) (guard : d1089 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6207 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6209 (p : Pattern) (guard : d1090 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5667 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6208 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6210 (p : Pattern) (guard : d1091 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6209 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5674 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6211 (p : Pattern) (guard : d1092 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6210 p hg
    simpa only [d1092, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d1092, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6212 (p : Pattern) (guard : d1209 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1208 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6201 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6211 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6213 (p : Pattern) (guard : d1376 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1376, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d1376, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1209 p = 1 := by simpa only [d1376, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6212 p hg
    simpa only [d1376, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6214 (p : Pattern) (guard : d1210 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5924 p hg
    simpa only [d1210, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1210, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6215 (p : Pattern) (guard : d1377 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1376 p = 1 := by simpa only [d1377, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6213 p hg
    simpa only [d1377, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1210 p = 1 := by simpa only [d1377, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6214 p hg
    simpa only [d1377, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6216 (p : Pattern) (guard : d1199 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5681 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6217 (p : Pattern) (guard : d1200 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6216 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6218 (p : Pattern) (guard : d1201 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6217 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6219 (p : Pattern) (guard : d1202 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6218 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d823 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6220 (p : Pattern) (guard : d1203 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5687 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6221 (p : Pattern) (guard : d1204 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6220 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6222 (p : Pattern) (guard : d1205 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6221 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6223 (p : Pattern) (guard : d1206 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6222 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6224 (p : Pattern) (guard : d1207 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1202 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6219 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1206 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6223 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6225 (p : Pattern) (guard : d1208 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1207 p = 1 := by simpa only [d1208, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6224 p hg
    simpa only [d1208, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1208, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d1208, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6226 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6227 (p : Pattern) (guard : d1084 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6226 p hg
    simpa only [d1084, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4738 p hg
    simpa only [d1084, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6228 (p : Pattern) (guard : d1085 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6227 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6229 (p : Pattern) (guard : d1086 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6228 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6230 (p : Pattern) (guard : d1087 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6229 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6231 (p : Pattern) (guard : d1088 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5291 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6230 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6232 (p : Pattern) (guard : d1089 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6233 (p : Pattern) (guard : d1090 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6232 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6234 (p : Pattern) (guard : d1091 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6233 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5691 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6235 (p : Pattern) (guard : d1092 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6234 p hg
    simpa only [d1092, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d1092, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6236 (p : Pattern) (guard : d1209 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1208 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6225 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6235 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6237 (p : Pattern) (guard : d1210 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6236 p hg
    simpa only [d1210, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1210, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6238 (p : Pattern) (guard : d1211 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1210 p = 1 := by simpa only [d1211, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6237 p hg
    simpa only [d1211, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1211, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1211, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6239 (p : Pattern) (guard : d1378 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1377 p = 1 := by simpa only [d1378, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6215 p hg
    simpa only [d1378, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1211 p = 1 := by simpa only [d1378, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6238 p hg
    simpa only [d1378, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6240 (p : Pattern) (guard : d1379 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1378 p = 1 := by simpa only [d1379, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6239 p hg
    simpa only [d1379, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1379, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d1379, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6241 (p : Pattern) (guard : d1093 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6205 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6242 (p : Pattern) (guard : d1094 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4949 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6243 (p : Pattern) (guard : d1095 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6242 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6244 (p : Pattern) (guard : d1096 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6208 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6243 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6245 (p : Pattern) (guard : d1097 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6244 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6246 (p : Pattern) (guard : d1098 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6245 p hg
    simpa only [d1098, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d1098, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6247 (p : Pattern) (guard : d1099 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6211 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6246 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6248 (p : Pattern) (guard : d1380 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1380, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d1380, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1099 p = 1 := by simpa only [d1380, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d1380, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6249 (p : Pattern) (guard : d1100 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5814 p hg
    simpa only [d1100, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1100, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
