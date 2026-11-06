import NetHack.Sokoban12CostPartition.Directions26
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem row29 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir29_north p
  | south => exact dir29_south p
  | east => exact dir29_east p
  | west => exact dir29_west p
  | northEast => exact dir29_northEast p
  | northWest => exact dir29_northWest p
  | southEast => exact dir29_southEast p
  | southWest => exact dir29_southWest p
theorem row30 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir30_north p
  | south => exact dir30_south p
  | east => exact dir30_east p
  | west => exact dir30_west p
  | northEast => exact dir30_northEast p
  | northWest => exact dir30_northWest p
  | southEast => exact dir30_southEast p
  | southWest => exact dir30_southWest p
theorem row31 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir31_north p
  | south => exact dir31_south p
  | east => exact dir31_east p
  | west => exact dir31_west p
  | northEast => exact dir31_northEast p
  | northWest => exact dir31_northWest p
  | southEast => exact dir31_southEast p
  | southWest => exact dir31_southWest p
theorem row32 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir32_north p
  | south => exact dir32_south p
  | east => exact dir32_east p
  | west => exact dir32_west p
  | northEast => exact dir32_northEast p
  | northWest => exact dir32_northWest p
  | southEast => exact dir32_southEast p
  | southWest => exact dir32_southWest p
theorem row33 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir33_north p
  | south => exact dir33_south p
  | east => exact dir33_east p
  | west => exact dir33_west p
  | northEast => exact dir33_northEast p
  | northWest => exact dir33_northWest p
  | southEast => exact dir33_southEast p
  | southWest => exact dir33_southWest p
theorem row34 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir34_north p
  | south => exact dir34_south p
  | east => exact dir34_east p
  | west => exact dir34_west p
  | northEast => exact dir34_northEast p
  | northWest => exact dir34_northWest p
  | southEast => exact dir34_southEast p
  | southWest => exact dir34_southWest p
theorem row35 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir35_north p
  | south => exact dir35_south p
  | east => exact dir35_east p
  | west => exact dir35_west p
  | northEast => exact dir35_northEast p
  | northWest => exact dir35_northWest p
  | southEast => exact dir35_southEast p
  | southWest => exact dir35_southWest p
theorem row36 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir36_north p
  | south => exact dir36_south p
  | east => exact dir36_east p
  | west => exact dir36_west p
  | northEast => exact dir36_northEast p
  | northWest => exact dir36_northWest p
  | southEast => exact dir36_southEast p
  | southWest => exact dir36_southWest p
theorem row37 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir37_north p
  | south => exact dir37_south p
  | east => exact dir37_east p
  | west => exact dir37_west p
  | northEast => exact dir37_northEast p
  | northWest => exact dir37_northWest p
  | southEast => exact dir37_southEast p
  | southWest => exact dir37_southWest p
theorem row38 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir38_north p
  | south => exact dir38_south p
  | east => exact dir38_east p
  | west => exact dir38_west p
  | northEast => exact dir38_northEast p
  | northWest => exact dir38_northWest p
  | southEast => exact dir38_southEast p
  | southWest => exact dir38_southWest p
theorem row39 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir39_north p
  | south => exact dir39_south p
  | east => exact dir39_east p
  | west => exact dir39_west p
  | northEast => exact dir39_northEast p
  | northWest => exact dir39_northWest p
  | southEast => exact dir39_southEast p
  | southWest => exact dir39_southWest p
theorem row40 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir40_north p
  | south => exact dir40_south p
  | east => exact dir40_east p
  | west => exact dir40_west p
  | northEast => exact dir40_northEast p
  | northWest => exact dir40_northWest p
  | southEast => exact dir40_southEast p
  | southWest => exact dir40_southWest p
theorem row41 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir41_north p
  | south => exact dir41_south p
  | east => exact dir41_east p
  | west => exact dir41_west p
  | northEast => exact dir41_northEast p
  | northWest => exact dir41_northWest p
  | southEast => exact dir41_southEast p
  | southWest => exact dir41_southWest p
theorem row42 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir42_north p
  | south => exact dir42_south p
  | east => exact dir42_east p
  | west => exact dir42_west p
  | northEast => exact dir42_northEast p
  | northWest => exact dir42_northWest p
  | southEast => exact dir42_southEast p
  | southWest => exact dir42_southWest p
theorem row43 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir43_north p
  | south => exact dir43_south p
  | east => exact dir43_east p
  | west => exact dir43_west p
  | northEast => exact dir43_northEast p
  | northWest => exact dir43_northWest p
  | southEast => exact dir43_southEast p
  | southWest => exact dir43_southWest p
theorem row44 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir44_north p
  | south => exact dir44_south p
  | east => exact dir44_east p
  | west => exact dir44_west p
  | northEast => exact dir44_northEast p
  | northWest => exact dir44_northWest p
  | southEast => exact dir44_southEast p
  | southWest => exact dir44_southWest p
theorem row45 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir45_north p
  | south => exact dir45_south p
  | east => exact dir45_east p
  | west => exact dir45_west p
  | northEast => exact dir45_northEast p
  | northWest => exact dir45_northWest p
  | southEast => exact dir45_southEast p
  | southWest => exact dir45_southWest p
theorem row46 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir46_north p
  | south => exact dir46_south p
  | east => exact dir46_east p
  | west => exact dir46_west p
  | northEast => exact dir46_northEast p
  | northWest => exact dir46_northWest p
  | southEast => exact dir46_southEast p
  | southWest => exact dir46_southWest p
theorem row47 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir47_north p
  | south => exact dir47_south p
  | east => exact dir47_east p
  | west => exact dir47_west p
  | northEast => exact dir47_northEast p
  | northWest => exact dir47_northWest p
  | southEast => exact dir47_southEast p
  | southWest => exact dir47_southWest p
theorem row48 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir48_north p
  | south => exact dir48_south p
  | east => exact dir48_east p
  | west => exact dir48_west p
  | northEast => exact dir48_northEast p
  | northWest => exact dir48_northWest p
  | southEast => exact dir48_southEast p
  | southWest => exact dir48_southWest p
theorem row49 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir49_north p
  | south => exact dir49_south p
  | east => exact dir49_east p
  | west => exact dir49_west p
  | northEast => exact dir49_northEast p
  | northWest => exact dir49_northWest p
  | southEast => exact dir49_southEast p
  | southWest => exact dir49_southWest p
theorem row50 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir50_north p
  | south => exact dir50_south p
  | east => exact dir50_east p
  | west => exact dir50_west p
  | northEast => exact dir50_northEast p
  | northWest => exact dir50_northWest p
  | southEast => exact dir50_southEast p
  | southWest => exact dir50_southWest p
theorem row55 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir55_north p
  | south => exact dir55_south p
  | east => exact dir55_east p
  | west => exact dir55_west p
  | northEast => exact dir55_northEast p
  | northWest => exact dir55_northWest p
  | southEast => exact dir55_southEast p
  | southWest => exact dir55_southWest p
theorem row56 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir56_north p
  | south => exact dir56_south p
  | east => exact dir56_east p
  | west => exact dir56_west p
  | northEast => exact dir56_northEast p
  | northWest => exact dir56_northWest p
  | southEast => exact dir56_southEast p
  | southWest => exact dir56_southWest p
theorem row76 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir76_north p
  | south => exact dir76_south p
  | east => exact dir76_east p
  | west => exact dir76_west p
  | northEast => exact dir76_northEast p
  | northWest => exact dir76_northWest p
  | southEast => exact dir76_southEast p
  | southWest => exact dir76_southWest p
theorem row82 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir82_north p
  | south => exact dir82_south p
  | east => exact dir82_east p
  | west => exact dir82_west p
  | northEast => exact dir82_northEast p
  | northWest => exact dir82_northWest p
  | southEast => exact dir82_southEast p
  | southWest => exact dir82_southWest p
theorem row102 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir102_north p
  | south => exact dir102_south p
  | east => exact dir102_east p
  | west => exact dir102_west p
  | northEast => exact dir102_northEast p
  | northWest => exact dir102_northWest p
  | southEast => exact dir102_southEast p
  | southWest => exact dir102_southWest p
theorem row105 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir105_north p
  | south => exact dir105_south p
  | east => exact dir105_east p
  | west => exact dir105_west p
  | northEast => exact dir105_northEast p
  | northWest => exact dir105_northWest p
  | southEast => exact dir105_southEast p
  | southWest => exact dir105_southWest p
theorem row106 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir106_north p
  | south => exact dir106_south p
  | east => exact dir106_east p
  | west => exact dir106_west p
  | northEast => exact dir106_northEast p
  | northWest => exact dir106_northWest p
  | southEast => exact dir106_southEast p
  | southWest => exact dir106_southWest p
theorem row108 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir108_north p
  | south => exact dir108_south p
  | east => exact dir108_east p
  | west => exact dir108_west p
  | northEast => exact dir108_northEast p
  | northWest => exact dir108_northWest p
  | southEast => exact dir108_southEast p
  | southWest => exact dir108_southWest p
theorem row115 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir115_north p
  | south => exact dir115_south p
  | east => exact dir115_east p
  | west => exact dir115_west p
  | northEast => exact dir115_northEast p
  | northWest => exact dir115_northWest p
  | southEast => exact dir115_southEast p
  | southWest => exact dir115_southWest p
theorem row116 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir116_north p
  | south => exact dir116_south p
  | east => exact dir116_east p
  | west => exact dir116_west p
  | northEast => exact dir116_northEast p
  | northWest => exact dir116_northWest p
  | southEast => exact dir116_southEast p
  | southWest => exact dir116_southWest p
theorem row117 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir117_north p
  | south => exact dir117_south p
  | east => exact dir117_east p
  | west => exact dir117_west p
  | northEast => exact dir117_northEast p
  | northWest => exact dir117_northWest p
  | southEast => exact dir117_southEast p
  | southWest => exact dir117_southWest p
theorem row128 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir128_north p
  | south => exact dir128_south p
  | east => exact dir128_east p
  | west => exact dir128_west p
  | northEast => exact dir128_northEast p
  | northWest => exact dir128_northWest p
  | southEast => exact dir128_southEast p
  | southWest => exact dir128_southWest p
theorem row131 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir131_north p
  | south => exact dir131_south p
  | east => exact dir131_east p
  | west => exact dir131_west p
  | northEast => exact dir131_northEast p
  | northWest => exact dir131_northWest p
  | southEast => exact dir131_southEast p
  | southWest => exact dir131_southWest p
theorem row132 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir132_north p
  | south => exact dir132_south p
  | east => exact dir132_east p
  | west => exact dir132_west p
  | northEast => exact dir132_northEast p
  | northWest => exact dir132_northWest p
  | southEast => exact dir132_southEast p
  | southWest => exact dir132_southWest p
theorem row133 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir133_north p
  | south => exact dir133_south p
  | east => exact dir133_east p
  | west => exact dir133_west p
  | northEast => exact dir133_northEast p
  | northWest => exact dir133_northWest p
  | southEast => exact dir133_southEast p
  | southWest => exact dir133_southWest p
theorem row134 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir134_north p
  | south => exact dir134_south p
  | east => exact dir134_east p
  | west => exact dir134_west p
  | northEast => exact dir134_northEast p
  | northWest => exact dir134_northWest p
  | southEast => exact dir134_southEast p
  | southWest => exact dir134_southWest p
theorem row135 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir135_north p
  | south => exact dir135_south p
  | east => exact dir135_east p
  | west => exact dir135_west p
  | northEast => exact dir135_northEast p
  | northWest => exact dir135_northWest p
  | southEast => exact dir135_southEast p
  | southWest => exact dir135_southWest p
theorem row140 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir140_north p
  | south => exact dir140_south p
  | east => exact dir140_east p
  | west => exact dir140_west p
  | northEast => exact dir140_northEast p
  | northWest => exact dir140_northWest p
  | southEast => exact dir140_southEast p
  | southWest => exact dir140_southWest p
theorem row141 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir141_north p
  | south => exact dir141_south p
  | east => exact dir141_east p
  | west => exact dir141_west p
  | northEast => exact dir141_northEast p
  | northWest => exact dir141_northWest p
  | southEast => exact dir141_southEast p
  | southWest => exact dir141_southWest p
theorem row142 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir142_north p
  | south => exact dir142_south p
  | east => exact dir142_east p
  | west => exact dir142_west p
  | northEast => exact dir142_northEast p
  | northWest => exact dir142_northWest p
  | southEast => exact dir142_southEast p
  | southWest => exact dir142_southWest p
theorem row143 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir143_north p
  | south => exact dir143_south p
  | east => exact dir143_east p
  | west => exact dir143_west p
  | northEast => exact dir143_northEast p
  | northWest => exact dir143_northWest p
  | southEast => exact dir143_southEast p
  | southWest => exact dir143_southWest p
theorem row154 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir154_north p
  | south => exact dir154_south p
  | east => exact dir154_east p
  | west => exact dir154_west p
  | northEast => exact dir154_northEast p
  | northWest => exact dir154_northWest p
  | southEast => exact dir154_southEast p
  | southWest => exact dir154_southWest p
theorem row157 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir157_north p
  | south => exact dir157_south p
  | east => exact dir157_east p
  | west => exact dir157_west p
  | northEast => exact dir157_northEast p
  | northWest => exact dir157_northWest p
  | southEast => exact dir157_southEast p
  | southWest => exact dir157_southWest p
theorem row158 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir158_north p
  | south => exact dir158_south p
  | east => exact dir158_east p
  | west => exact dir158_west p
  | northEast => exact dir158_northEast p
  | northWest => exact dir158_northWest p
  | southEast => exact dir158_southEast p
  | southWest => exact dir158_southWest p
theorem row159 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir159_north p
  | south => exact dir159_south p
  | east => exact dir159_east p
  | west => exact dir159_west p
  | northEast => exact dir159_northEast p
  | northWest => exact dir159_northWest p
  | southEast => exact dir159_southEast p
  | southWest => exact dir159_southWest p
theorem row160 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir160_north p
  | south => exact dir160_south p
  | east => exact dir160_east p
  | west => exact dir160_west p
  | northEast => exact dir160_northEast p
  | northWest => exact dir160_northWest p
  | southEast => exact dir160_southEast p
  | southWest => exact dir160_southWest p
theorem row161 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir161_north p
  | south => exact dir161_south p
  | east => exact dir161_east p
  | west => exact dir161_west p
  | northEast => exact dir161_northEast p
  | northWest => exact dir161_northWest p
  | southEast => exact dir161_southEast p
  | southWest => exact dir161_southWest p
theorem row163 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir163_north p
  | south => exact dir163_south p
  | east => exact dir163_east p
  | west => exact dir163_west p
  | northEast => exact dir163_northEast p
  | northWest => exact dir163_northWest p
  | southEast => exact dir163_southEast p
  | southWest => exact dir163_southWest p
theorem row164 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir164_north p
  | south => exact dir164_south p
  | east => exact dir164_east p
  | west => exact dir164_west p
  | northEast => exact dir164_northEast p
  | northWest => exact dir164_northWest p
  | southEast => exact dir164_southEast p
  | southWest => exact dir164_southWest p
theorem row166 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir166_north p
  | south => exact dir166_south p
  | east => exact dir166_east p
  | west => exact dir166_west p
  | northEast => exact dir166_northEast p
  | northWest => exact dir166_northWest p
  | southEast => exact dir166_southEast p
  | southWest => exact dir166_southWest p
theorem row167 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir167_north p
  | south => exact dir167_south p
  | east => exact dir167_east p
  | west => exact dir167_west p
  | northEast => exact dir167_northEast p
  | northWest => exact dir167_northWest p
  | southEast => exact dir167_southEast p
  | southWest => exact dir167_southWest p
theorem row168 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir168_north p
  | south => exact dir168_south p
  | east => exact dir168_east p
  | west => exact dir168_west p
  | northEast => exact dir168_northEast p
  | northWest => exact dir168_northWest p
  | southEast => exact dir168_southEast p
  | southWest => exact dir168_southWest p
theorem row169 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir169_north p
  | south => exact dir169_south p
  | east => exact dir169_east p
  | west => exact dir169_west p
  | northEast => exact dir169_northEast p
  | northWest => exact dir169_northWest p
  | southEast => exact dir169_southEast p
  | southWest => exact dir169_southWest p
theorem row180 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir180_north p
  | south => exact dir180_south p
  | east => exact dir180_east p
  | west => exact dir180_west p
  | northEast => exact dir180_northEast p
  | northWest => exact dir180_northWest p
  | southEast => exact dir180_southEast p
  | southWest => exact dir180_southWest p
theorem row184 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir184_north p
  | south => exact dir184_south p
  | east => exact dir184_east p
  | west => exact dir184_west p
  | northEast => exact dir184_northEast p
  | northWest => exact dir184_northWest p
  | southEast => exact dir184_southEast p
  | southWest => exact dir184_southWest p
theorem row185 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir185_north p
  | south => exact dir185_south p
  | east => exact dir185_east p
  | west => exact dir185_west p
  | northEast => exact dir185_northEast p
  | northWest => exact dir185_northWest p
  | southEast => exact dir185_southEast p
  | southWest => exact dir185_southWest p
theorem row186 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir186_north p
  | south => exact dir186_south p
  | east => exact dir186_east p
  | west => exact dir186_west p
  | northEast => exact dir186_northEast p
  | northWest => exact dir186_northWest p
  | southEast => exact dir186_southEast p
  | southWest => exact dir186_southWest p
theorem row187 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir187_north p
  | south => exact dir187_south p
  | east => exact dir187_east p
  | west => exact dir187_west p
  | northEast => exact dir187_northEast p
  | northWest => exact dir187_northWest p
  | southEast => exact dir187_southEast p
  | southWest => exact dir187_southWest p
theorem row189 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir189_north p
  | south => exact dir189_south p
  | east => exact dir189_east p
  | west => exact dir189_west p
  | northEast => exact dir189_northEast p
  | northWest => exact dir189_northWest p
  | southEast => exact dir189_southEast p
  | southWest => exact dir189_southWest p
theorem row190 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir190_north p
  | south => exact dir190_south p
  | east => exact dir190_east p
  | west => exact dir190_west p
  | northEast => exact dir190_northEast p
  | northWest => exact dir190_northWest p
  | southEast => exact dir190_southEast p
  | southWest => exact dir190_southWest p
theorem row191 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir191_north p
  | south => exact dir191_south p
  | east => exact dir191_east p
  | west => exact dir191_west p
  | northEast => exact dir191_northEast p
  | northWest => exact dir191_northWest p
  | southEast => exact dir191_southEast p
  | southWest => exact dir191_southWest p
theorem row192 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir192_north p
  | south => exact dir192_south p
  | east => exact dir192_east p
  | west => exact dir192_west p
  | northEast => exact dir192_northEast p
  | northWest => exact dir192_northWest p
  | southEast => exact dir192_southEast p
  | southWest => exact dir192_southWest p
theorem row193 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir193_north p
  | south => exact dir193_south p
  | east => exact dir193_east p
  | west => exact dir193_west p
  | northEast => exact dir193_northEast p
  | northWest => exact dir193_northWest p
  | southEast => exact dir193_southEast p
  | southWest => exact dir193_southWest p
theorem row194 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir194_north p
  | south => exact dir194_south p
  | east => exact dir194_east p
  | west => exact dir194_west p
  | northEast => exact dir194_northEast p
  | northWest => exact dir194_northWest p
  | southEast => exact dir194_southEast p
  | southWest => exact dir194_southWest p
theorem row206 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir206_north p
  | south => exact dir206_south p
  | east => exact dir206_east p
  | west => exact dir206_west p
  | northEast => exact dir206_northEast p
  | northWest => exact dir206_northWest p
  | southEast => exact dir206_southEast p
  | southWest => exact dir206_southWest p
theorem row210 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir210_north p
  | south => exact dir210_south p
  | east => exact dir210_east p
  | west => exact dir210_west p
  | northEast => exact dir210_northEast p
  | northWest => exact dir210_northWest p
  | southEast => exact dir210_southEast p
  | southWest => exact dir210_southWest p
theorem row211 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir211_north p
  | south => exact dir211_south p
  | east => exact dir211_east p
  | west => exact dir211_west p
  | northEast => exact dir211_northEast p
  | northWest => exact dir211_northWest p
  | southEast => exact dir211_southEast p
  | southWest => exact dir211_southWest p
theorem row212 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir212_north p
  | south => exact dir212_south p
  | east => exact dir212_east p
  | west => exact dir212_west p
  | northEast => exact dir212_northEast p
  | northWest => exact dir212_northWest p
  | southEast => exact dir212_southEast p
  | southWest => exact dir212_southWest p
theorem row213 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir213_north p
  | south => exact dir213_south p
  | east => exact dir213_east p
  | west => exact dir213_west p
  | northEast => exact dir213_northEast p
  | northWest => exact dir213_northWest p
  | southEast => exact dir213_southEast p
  | southWest => exact dir213_southWest p
theorem row214 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir214_north p
  | south => exact dir214_south p
  | east => exact dir214_east p
  | west => exact dir214_west p
  | northEast => exact dir214_northEast p
  | northWest => exact dir214_northWest p
  | southEast => exact dir214_southEast p
  | southWest => exact dir214_southWest p
theorem row215 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir215_north p
  | south => exact dir215_south p
  | east => exact dir215_east p
  | west => exact dir215_west p
  | northEast => exact dir215_northEast p
  | northWest => exact dir215_northWest p
  | southEast => exact dir215_southEast p
  | southWest => exact dir215_southWest p
theorem row216 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir216_north p
  | south => exact dir216_south p
  | east => exact dir216_east p
  | west => exact dir216_west p
  | northEast => exact dir216_northEast p
  | northWest => exact dir216_northWest p
  | southEast => exact dir216_southEast p
  | southWest => exact dir216_southWest p
theorem row218 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir218_north p
  | south => exact dir218_south p
  | east => exact dir218_east p
  | west => exact dir218_west p
  | northEast => exact dir218_northEast p
  | northWest => exact dir218_northWest p
  | southEast => exact dir218_southEast p
  | southWest => exact dir218_southWest p
theorem row219 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir219_north p
  | south => exact dir219_south p
  | east => exact dir219_east p
  | west => exact dir219_west p
  | northEast => exact dir219_northEast p
  | northWest => exact dir219_northWest p
  | southEast => exact dir219_southEast p
  | southWest => exact dir219_southWest p
theorem row220 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir220_north p
  | south => exact dir220_south p
  | east => exact dir220_east p
  | west => exact dir220_west p
  | northEast => exact dir220_northEast p
  | northWest => exact dir220_northWest p
  | southEast => exact dir220_southEast p
  | southWest => exact dir220_southWest p
theorem row232 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir232_north p
  | south => exact dir232_south p
  | east => exact dir232_east p
  | west => exact dir232_west p
  | northEast => exact dir232_northEast p
  | northWest => exact dir232_northWest p
  | southEast => exact dir232_southEast p
  | southWest => exact dir232_southWest p
theorem row236 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir236_north p
  | south => exact dir236_south p
  | east => exact dir236_east p
  | west => exact dir236_west p
  | northEast => exact dir236_northEast p
  | northWest => exact dir236_northWest p
  | southEast => exact dir236_southEast p
  | southWest => exact dir236_southWest p
theorem row237 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir237_north p
  | south => exact dir237_south p
  | east => exact dir237_east p
  | west => exact dir237_west p
  | northEast => exact dir237_northEast p
  | northWest => exact dir237_northWest p
  | southEast => exact dir237_southEast p
  | southWest => exact dir237_southWest p
theorem row238 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir238_north p
  | south => exact dir238_south p
  | east => exact dir238_east p
  | west => exact dir238_west p
  | northEast => exact dir238_northEast p
  | northWest => exact dir238_northWest p
  | southEast => exact dir238_southEast p
  | southWest => exact dir238_southWest p
theorem row239 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir239_north p
  | south => exact dir239_south p
  | east => exact dir239_east p
  | west => exact dir239_west p
  | northEast => exact dir239_northEast p
  | northWest => exact dir239_northWest p
  | southEast => exact dir239_southEast p
  | southWest => exact dir239_southWest p
theorem row241 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir241_north p
  | south => exact dir241_south p
  | east => exact dir241_east p
  | west => exact dir241_west p
  | northEast => exact dir241_northEast p
  | northWest => exact dir241_northWest p
  | southEast => exact dir241_southEast p
  | southWest => exact dir241_southWest p
theorem row242 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir242_north p
  | south => exact dir242_south p
  | east => exact dir242_east p
  | west => exact dir242_west p
  | northEast => exact dir242_northEast p
  | northWest => exact dir242_northWest p
  | southEast => exact dir242_southEast p
  | southWest => exact dir242_southWest p
theorem row244 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir244_north p
  | south => exact dir244_south p
  | east => exact dir244_east p
  | west => exact dir244_west p
  | northEast => exact dir244_northEast p
  | northWest => exact dir244_northWest p
  | southEast => exact dir244_southEast p
  | southWest => exact dir244_southWest p
theorem row245 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir245_north p
  | south => exact dir245_south p
  | east => exact dir245_east p
  | west => exact dir245_west p
  | northEast => exact dir245_northEast p
  | northWest => exact dir245_northWest p
  | southEast => exact dir245_southEast p
  | southWest => exact dir245_southWest p
theorem row246 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir246_north p
  | south => exact dir246_south p
  | east => exact dir246_east p
  | west => exact dir246_west p
  | northEast => exact dir246_northEast p
  | northWest => exact dir246_northWest p
  | southEast => exact dir246_southEast p
  | southWest => exact dir246_southWest p
theorem row252 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir252_north p
  | south => exact dir252_south p
  | east => exact dir252_east p
  | west => exact dir252_west p
  | northEast => exact dir252_northEast p
  | northWest => exact dir252_northWest p
  | southEast => exact dir252_southEast p
  | southWest => exact dir252_southWest p
theorem row253 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir253_north p
  | south => exact dir253_south p
  | east => exact dir253_east p
  | west => exact dir253_west p
  | northEast => exact dir253_northEast p
  | northWest => exact dir253_northWest p
  | southEast => exact dir253_southEast p
  | southWest => exact dir253_southWest p
theorem row254 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir254_north p
  | south => exact dir254_south p
  | east => exact dir254_east p
  | west => exact dir254_west p
  | northEast => exact dir254_northEast p
  | northWest => exact dir254_northWest p
  | southEast => exact dir254_southEast p
  | southWest => exact dir254_southWest p
theorem row255 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir255_north p
  | south => exact dir255_south p
  | east => exact dir255_east p
  | west => exact dir255_west p
  | northEast => exact dir255_northEast p
  | northWest => exact dir255_northWest p
  | southEast => exact dir255_southEast p
  | southWest => exact dir255_southWest p
theorem row256 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir256_north p
  | south => exact dir256_south p
  | east => exact dir256_east p
  | west => exact dir256_west p
  | northEast => exact dir256_northEast p
  | northWest => exact dir256_northWest p
  | southEast => exact dir256_southEast p
  | southWest => exact dir256_southWest p
theorem row258 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir258_north p
  | south => exact dir258_south p
  | east => exact dir258_east p
  | west => exact dir258_west p
  | northEast => exact dir258_northEast p
  | northWest => exact dir258_northWest p
  | southEast => exact dir258_southEast p
  | southWest => exact dir258_southWest p
theorem row262 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir262_north p
  | south => exact dir262_south p
  | east => exact dir262_east p
  | west => exact dir262_west p
  | northEast => exact dir262_northEast p
  | northWest => exact dir262_northWest p
  | southEast => exact dir262_southEast p
  | southWest => exact dir262_southWest p
theorem row263 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir263_north p
  | south => exact dir263_south p
  | east => exact dir263_east p
  | west => exact dir263_west p
  | northEast => exact dir263_northEast p
  | northWest => exact dir263_northWest p
  | southEast => exact dir263_southEast p
  | southWest => exact dir263_southWest p
theorem row264 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir264_north p
  | south => exact dir264_south p
  | east => exact dir264_east p
  | west => exact dir264_west p
  | northEast => exact dir264_northEast p
  | northWest => exact dir264_northWest p
  | southEast => exact dir264_southEast p
  | southWest => exact dir264_southWest p
theorem row265 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir265_north p
  | south => exact dir265_south p
  | east => exact dir265_east p
  | west => exact dir265_west p
  | northEast => exact dir265_northEast p
  | northWest => exact dir265_northWest p
  | southEast => exact dir265_southEast p
  | southWest => exact dir265_southWest p
theorem row270 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir270_north p
  | south => exact dir270_south p
  | east => exact dir270_east p
  | west => exact dir270_west p
  | northEast => exact dir270_northEast p
  | northWest => exact dir270_northWest p
  | southEast => exact dir270_southEast p
  | southWest => exact dir270_southWest p
theorem row271 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir271_north p
  | south => exact dir271_south p
  | east => exact dir271_east p
  | west => exact dir271_west p
  | northEast => exact dir271_northEast p
  | northWest => exact dir271_northWest p
  | southEast => exact dir271_southEast p
  | southWest => exact dir271_southWest p
theorem row272 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir272_north p
  | south => exact dir272_south p
  | east => exact dir272_east p
  | west => exact dir272_west p
  | northEast => exact dir272_northEast p
  | northWest => exact dir272_northWest p
  | southEast => exact dir272_southEast p
  | southWest => exact dir272_southWest p
theorem row276 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir276_north p
  | south => exact dir276_south p
  | east => exact dir276_east p
  | west => exact dir276_west p
  | northEast => exact dir276_northEast p
  | northWest => exact dir276_northWest p
  | southEast => exact dir276_southEast p
  | southWest => exact dir276_southWest p
theorem row278 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir278_north p
  | south => exact dir278_south p
  | east => exact dir278_east p
  | west => exact dir278_west p
  | northEast => exact dir278_northEast p
  | northWest => exact dir278_northWest p
  | southEast => exact dir278_southEast p
  | southWest => exact dir278_southWest p
theorem row279 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir279_north p
  | south => exact dir279_south p
  | east => exact dir279_east p
  | west => exact dir279_west p
  | northEast => exact dir279_northEast p
  | northWest => exact dir279_northWest p
  | southEast => exact dir279_southEast p
  | southWest => exact dir279_southWest p
theorem row280 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir280_north p
  | south => exact dir280_south p
  | east => exact dir280_east p
  | west => exact dir280_west p
  | northEast => exact dir280_northEast p
  | northWest => exact dir280_northWest p
  | southEast => exact dir280_southEast p
  | southWest => exact dir280_southWest p
theorem row281 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir281_north p
  | south => exact dir281_south p
  | east => exact dir281_east p
  | west => exact dir281_west p
  | northEast => exact dir281_northEast p
  | northWest => exact dir281_northWest p
  | southEast => exact dir281_southEast p
  | southWest => exact dir281_southWest p
theorem row282 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir282_north p
  | south => exact dir282_south p
  | east => exact dir282_east p
  | west => exact dir282_west p
  | northEast => exact dir282_northEast p
  | northWest => exact dir282_northWest p
  | southEast => exact dir282_southEast p
  | southWest => exact dir282_southWest p
theorem row284 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir284_north p
  | south => exact dir284_south p
  | east => exact dir284_east p
  | west => exact dir284_west p
  | northEast => exact dir284_northEast p
  | northWest => exact dir284_northWest p
  | southEast => exact dir284_southEast p
  | southWest => exact dir284_southWest p
theorem row288 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir288_north p
  | south => exact dir288_south p
  | east => exact dir288_east p
  | west => exact dir288_west p
  | northEast => exact dir288_northEast p
  | northWest => exact dir288_northWest p
  | southEast => exact dir288_southEast p
  | southWest => exact dir288_southWest p
theorem row289 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir289_north p
  | south => exact dir289_south p
  | east => exact dir289_east p
  | west => exact dir289_west p
  | northEast => exact dir289_northEast p
  | northWest => exact dir289_northWest p
  | southEast => exact dir289_southEast p
  | southWest => exact dir289_southWest p
theorem row290 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir290_north p
  | south => exact dir290_south p
  | east => exact dir290_east p
  | west => exact dir290_west p
  | northEast => exact dir290_northEast p
  | northWest => exact dir290_northWest p
  | southEast => exact dir290_southEast p
  | southWest => exact dir290_southWest p
theorem row291 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir291_north p
  | south => exact dir291_south p
  | east => exact dir291_east p
  | west => exact dir291_west p
  | northEast => exact dir291_northEast p
  | northWest => exact dir291_northWest p
  | southEast => exact dir291_southEast p
  | southWest => exact dir291_southWest p
theorem row292 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir292_north p
  | south => exact dir292_south p
  | east => exact dir292_east p
  | west => exact dir292_west p
  | northEast => exact dir292_northEast p
  | northWest => exact dir292_northWest p
  | southEast => exact dir292_southEast p
  | southWest => exact dir292_southWest p
theorem row293 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir293_north p
  | south => exact dir293_south p
  | east => exact dir293_east p
  | west => exact dir293_west p
  | northEast => exact dir293_northEast p
  | northWest => exact dir293_northWest p
  | southEast => exact dir293_southEast p
  | southWest => exact dir293_southWest p
theorem row294 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir294_north p
  | south => exact dir294_south p
  | east => exact dir294_east p
  | west => exact dir294_west p
  | northEast => exact dir294_northEast p
  | northWest => exact dir294_northWest p
  | southEast => exact dir294_southEast p
  | southWest => exact dir294_southWest p
theorem row296 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir296_north p
  | south => exact dir296_south p
  | east => exact dir296_east p
  | west => exact dir296_west p
  | northEast => exact dir296_northEast p
  | northWest => exact dir296_northWest p
  | southEast => exact dir296_southEast p
  | southWest => exact dir296_southWest p
theorem row297 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir297_north p
  | south => exact dir297_south p
  | east => exact dir297_east p
  | west => exact dir297_west p
  | northEast => exact dir297_northEast p
  | northWest => exact dir297_northWest p
  | southEast => exact dir297_southEast p
  | southWest => exact dir297_southWest p
theorem row304 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir304_north p
  | south => exact dir304_south p
  | east => exact dir304_east p
  | west => exact dir304_west p
  | northEast => exact dir304_northEast p
  | northWest => exact dir304_northWest p
  | southEast => exact dir304_southEast p
  | southWest => exact dir304_southWest p
theorem row305 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir305_north p
  | south => exact dir305_south p
  | east => exact dir305_east p
  | west => exact dir305_west p
  | northEast => exact dir305_northEast p
  | northWest => exact dir305_northWest p
  | southEast => exact dir305_southEast p
  | southWest => exact dir305_southWest p
theorem row306 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir306_north p
  | south => exact dir306_south p
  | east => exact dir306_east p
  | west => exact dir306_west p
  | northEast => exact dir306_northEast p
  | northWest => exact dir306_northWest p
  | southEast => exact dir306_southEast p
  | southWest => exact dir306_southWest p
theorem row307 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir307_north p
  | south => exact dir307_south p
  | east => exact dir307_east p
  | west => exact dir307_west p
  | northEast => exact dir307_northEast p
  | northWest => exact dir307_northWest p
  | southEast => exact dir307_southEast p
  | southWest => exact dir307_southWest p
theorem row308 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir308_north p
  | south => exact dir308_south p
  | east => exact dir308_east p
  | west => exact dir308_west p
  | northEast => exact dir308_northEast p
  | northWest => exact dir308_northWest p
  | southEast => exact dir308_southEast p
  | southWest => exact dir308_southWest p
theorem row310 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir310_north p
  | south => exact dir310_south p
  | east => exact dir310_east p
  | west => exact dir310_west p
  | northEast => exact dir310_northEast p
  | northWest => exact dir310_northWest p
  | southEast => exact dir310_southEast p
  | southWest => exact dir310_southWest p
theorem row317 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir317_north p
  | south => exact dir317_south p
  | east => exact dir317_east p
  | west => exact dir317_west p
  | northEast => exact dir317_northEast p
  | northWest => exact dir317_northWest p
  | southEast => exact dir317_southEast p
  | southWest => exact dir317_southWest p
theorem row318 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir318_north p
  | south => exact dir318_south p
  | east => exact dir318_east p
  | west => exact dir318_west p
  | northEast => exact dir318_northEast p
  | northWest => exact dir318_northWest p
  | southEast => exact dir318_southEast p
  | southWest => exact dir318_southWest p
theorem row319 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir319_north p
  | south => exact dir319_south p
  | east => exact dir319_east p
  | west => exact dir319_west p
  | northEast => exact dir319_northEast p
  | northWest => exact dir319_northWest p
  | southEast => exact dir319_southEast p
  | southWest => exact dir319_southWest p
theorem row320 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir320_north p
  | south => exact dir320_south p
  | east => exact dir320_east p
  | west => exact dir320_west p
  | northEast => exact dir320_northEast p
  | northWest => exact dir320_northWest p
  | southEast => exact dir320_southEast p
  | southWest => exact dir320_southWest p
theorem row322 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir322_north p
  | south => exact dir322_south p
  | east => exact dir322_east p
  | west => exact dir322_west p
  | northEast => exact dir322_northEast p
  | northWest => exact dir322_northWest p
  | southEast => exact dir322_southEast p
  | southWest => exact dir322_southWest p
theorem row328 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir328_north p
  | south => exact dir328_south p
  | east => exact dir328_east p
  | west => exact dir328_west p
  | northEast => exact dir328_northEast p
  | northWest => exact dir328_northWest p
  | southEast => exact dir328_southEast p
  | southWest => exact dir328_southWest p
theorem row330 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir330_north p
  | south => exact dir330_south p
  | east => exact dir330_east p
  | west => exact dir330_west p
  | northEast => exact dir330_northEast p
  | northWest => exact dir330_northWest p
  | southEast => exact dir330_southEast p
  | southWest => exact dir330_southWest p
theorem row331 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir331_north p
  | south => exact dir331_south p
  | east => exact dir331_east p
  | west => exact dir331_west p
  | northEast => exact dir331_northEast p
  | northWest => exact dir331_northWest p
  | southEast => exact dir331_southEast p
  | southWest => exact dir331_southWest p
theorem row332 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir332_north p
  | south => exact dir332_south p
  | east => exact dir332_east p
  | west => exact dir332_west p
  | northEast => exact dir332_northEast p
  | northWest => exact dir332_northWest p
  | southEast => exact dir332_southEast p
  | southWest => exact dir332_southWest p
theorem row333 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir333_north p
  | south => exact dir333_south p
  | east => exact dir333_east p
  | west => exact dir333_west p
  | northEast => exact dir333_northEast p
  | northWest => exact dir333_northWest p
  | southEast => exact dir333_southEast p
  | southWest => exact dir333_southWest p
theorem row334 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir334_north p
  | south => exact dir334_south p
  | east => exact dir334_east p
  | west => exact dir334_west p
  | northEast => exact dir334_northEast p
  | northWest => exact dir334_northWest p
  | southEast => exact dir334_southEast p
  | southWest => exact dir334_southWest p
theorem row336 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir336_north p
  | south => exact dir336_south p
  | east => exact dir336_east p
  | west => exact dir336_west p
  | northEast => exact dir336_northEast p
  | northWest => exact dir336_northWest p
  | southEast => exact dir336_southEast p
  | southWest => exact dir336_southWest p
theorem row345 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir345_north p
  | south => exact dir345_south p
  | east => exact dir345_east p
  | west => exact dir345_west p
  | northEast => exact dir345_northEast p
  | northWest => exact dir345_northWest p
  | southEast => exact dir345_southEast p
  | southWest => exact dir345_southWest p
theorem row348 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir348_north p
  | south => exact dir348_south p
  | east => exact dir348_east p
  | west => exact dir348_west p
  | northEast => exact dir348_northEast p
  | northWest => exact dir348_northWest p
  | southEast => exact dir348_southEast p
  | southWest => exact dir348_southWest p
theorem row356 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir356_north p
  | south => exact dir356_south p
  | east => exact dir356_east p
  | west => exact dir356_west p
  | northEast => exact dir356_northEast p
  | northWest => exact dir356_northWest p
  | southEast => exact dir356_southEast p
  | southWest => exact dir356_southWest p
theorem row357 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir357_north p
  | south => exact dir357_south p
  | east => exact dir357_east p
  | west => exact dir357_west p
  | northEast => exact dir357_northEast p
  | northWest => exact dir357_northWest p
  | southEast => exact dir357_southEast p
  | southWest => exact dir357_southWest p
theorem row358 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir358_north p
  | south => exact dir358_south p
  | east => exact dir358_east p
  | west => exact dir358_west p
  | northEast => exact dir358_northEast p
  | northWest => exact dir358_northWest p
  | southEast => exact dir358_southEast p
  | southWest => exact dir358_southWest p
theorem row359 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir359_north p
  | south => exact dir359_south p
  | east => exact dir359_east p
  | west => exact dir359_west p
  | northEast => exact dir359_northEast p
  | northWest => exact dir359_northWest p
  | southEast => exact dir359_southEast p
  | southWest => exact dir359_southWest p
theorem row360 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir360_north p
  | south => exact dir360_south p
  | east => exact dir360_east p
  | west => exact dir360_west p
  | northEast => exact dir360_northEast p
  | northWest => exact dir360_northWest p
  | southEast => exact dir360_southEast p
  | southWest => exact dir360_southWest p
theorem row370 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir370_north p
  | south => exact dir370_south p
  | east => exact dir370_east p
  | west => exact dir370_west p
  | northEast => exact dir370_northEast p
  | northWest => exact dir370_northWest p
  | southEast => exact dir370_southEast p
  | southWest => exact dir370_southWest p
theorem row371 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir371_north p
  | south => exact dir371_south p
  | east => exact dir371_east p
  | west => exact dir371_west p
  | northEast => exact dir371_northEast p
  | northWest => exact dir371_northWest p
  | southEast => exact dir371_southEast p
  | southWest => exact dir371_southWest p
theorem row372 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir372_north p
  | south => exact dir372_south p
  | east => exact dir372_east p
  | west => exact dir372_west p
  | northEast => exact dir372_northEast p
  | northWest => exact dir372_northWest p
  | southEast => exact dir372_southEast p
  | southWest => exact dir372_southWest p
theorem row373 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir373_north p
  | south => exact dir373_south p
  | east => exact dir373_east p
  | west => exact dir373_west p
  | northEast => exact dir373_northEast p
  | northWest => exact dir373_northWest p
  | southEast => exact dir373_southEast p
  | southWest => exact dir373_southWest p
theorem row374 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir374_north p
  | south => exact dir374_south p
  | east => exact dir374_east p
  | west => exact dir374_west p
  | northEast => exact dir374_northEast p
  | northWest => exact dir374_northWest p
  | southEast => exact dir374_southEast p
  | southWest => exact dir374_southWest p
theorem row380 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir380_north p
  | south => exact dir380_south p
  | east => exact dir380_east p
  | west => exact dir380_west p
  | northEast => exact dir380_northEast p
  | northWest => exact dir380_northWest p
  | southEast => exact dir380_southEast p
  | southWest => exact dir380_southWest p
theorem row382 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir382_north p
  | south => exact dir382_south p
  | east => exact dir382_east p
  | west => exact dir382_west p
  | northEast => exact dir382_northEast p
  | northWest => exact dir382_northWest p
  | southEast => exact dir382_southEast p
  | southWest => exact dir382_southWest p
theorem row383 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir383_north p
  | south => exact dir383_south p
  | east => exact dir383_east p
  | west => exact dir383_west p
  | northEast => exact dir383_northEast p
  | northWest => exact dir383_northWest p
  | southEast => exact dir383_southEast p
  | southWest => exact dir383_southWest p
theorem row384 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir384_north p
  | south => exact dir384_south p
  | east => exact dir384_east p
  | west => exact dir384_west p
  | northEast => exact dir384_northEast p
  | northWest => exact dir384_northWest p
  | southEast => exact dir384_southEast p
  | southWest => exact dir384_southWest p
theorem row385 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir385_north p
  | south => exact dir385_south p
  | east => exact dir385_east p
  | west => exact dir385_west p
  | northEast => exact dir385_northEast p
  | northWest => exact dir385_northWest p
  | southEast => exact dir385_southEast p
  | southWest => exact dir385_southWest p
theorem row386 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir386_north p
  | south => exact dir386_south p
  | east => exact dir386_east p
  | west => exact dir386_west p
  | northEast => exact dir386_northEast p
  | northWest => exact dir386_northWest p
  | southEast => exact dir386_southEast p
  | southWest => exact dir386_southWest p
theorem row396 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir396_north p
  | south => exact dir396_south p
  | east => exact dir396_east p
  | west => exact dir396_west p
  | northEast => exact dir396_northEast p
  | northWest => exact dir396_northWest p
  | southEast => exact dir396_southEast p
  | southWest => exact dir396_southWest p
theorem row397 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir397_north p
  | south => exact dir397_south p
  | east => exact dir397_east p
  | west => exact dir397_west p
  | northEast => exact dir397_northEast p
  | northWest => exact dir397_northWest p
  | southEast => exact dir397_southEast p
  | southWest => exact dir397_southWest p
theorem row399 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir399_north p
  | south => exact dir399_south p
  | east => exact dir399_east p
  | west => exact dir399_west p
  | northEast => exact dir399_northEast p
  | northWest => exact dir399_northWest p
  | southEast => exact dir399_southEast p
  | southWest => exact dir399_southWest p
theorem row400 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir400_north p
  | south => exact dir400_south p
  | east => exact dir400_east p
  | west => exact dir400_west p
  | northEast => exact dir400_northEast p
  | northWest => exact dir400_northWest p
  | southEast => exact dir400_southEast p
  | southWest => exact dir400_southWest p
theorem row408 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir408_north p
  | south => exact dir408_south p
  | east => exact dir408_east p
  | west => exact dir408_west p
  | northEast => exact dir408_northEast p
  | northWest => exact dir408_northWest p
  | southEast => exact dir408_southEast p
  | southWest => exact dir408_southWest p
theorem row409 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir409_north p
  | south => exact dir409_south p
  | east => exact dir409_east p
  | west => exact dir409_west p
  | northEast => exact dir409_northEast p
  | northWest => exact dir409_northWest p
  | southEast => exact dir409_southEast p
  | southWest => exact dir409_southWest p
theorem row410 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir410_north p
  | south => exact dir410_south p
  | east => exact dir410_east p
  | west => exact dir410_west p
  | northEast => exact dir410_northEast p
  | northWest => exact dir410_northWest p
  | southEast => exact dir410_southEast p
  | southWest => exact dir410_southWest p
theorem row411 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir411_north p
  | south => exact dir411_south p
  | east => exact dir411_east p
  | west => exact dir411_west p
  | northEast => exact dir411_northEast p
  | northWest => exact dir411_northWest p
  | southEast => exact dir411_southEast p
  | southWest => exact dir411_southWest p
theorem row412 (p : Pattern) : rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 p = true := by
  change allDirs.all (fun direction => directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir412_north p
  | south => exact dir412_south p
  | east => exact dir412_east p
  | west => exact dir412_west p
  | northEast => exact dir412_northEast p
  | northWest => exact dir412_northWest p
  | southEast => exact dir412_southEast p
  | southWest => exact dir412_southWest p
theorem all_rows : ∀ player ∈ soko1_2.board.floor, ∀ p, rowCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus player p = true := by
  exact List.forall_mem_cons.mpr ⟨row29, (List.forall_mem_cons.mpr ⟨row30, (List.forall_mem_cons.mpr ⟨row31, (List.forall_mem_cons.mpr ⟨row32, (List.forall_mem_cons.mpr ⟨row33, (List.forall_mem_cons.mpr ⟨row34, (List.forall_mem_cons.mpr ⟨row35, (List.forall_mem_cons.mpr ⟨row36, (List.forall_mem_cons.mpr ⟨row37, (List.forall_mem_cons.mpr ⟨row38, (List.forall_mem_cons.mpr ⟨row39, (List.forall_mem_cons.mpr ⟨row40, (List.forall_mem_cons.mpr ⟨row41, (List.forall_mem_cons.mpr ⟨row42, (List.forall_mem_cons.mpr ⟨row43, (List.forall_mem_cons.mpr ⟨row44, (List.forall_mem_cons.mpr ⟨row45, (List.forall_mem_cons.mpr ⟨row46, (List.forall_mem_cons.mpr ⟨row47, (List.forall_mem_cons.mpr ⟨row48, (List.forall_mem_cons.mpr ⟨row49, (List.forall_mem_cons.mpr ⟨row50, (List.forall_mem_cons.mpr ⟨row55, (List.forall_mem_cons.mpr ⟨row56, (List.forall_mem_cons.mpr ⟨row76, (List.forall_mem_cons.mpr ⟨row82, (List.forall_mem_cons.mpr ⟨row102, (List.forall_mem_cons.mpr ⟨row105, (List.forall_mem_cons.mpr ⟨row106, (List.forall_mem_cons.mpr ⟨row108, (List.forall_mem_cons.mpr ⟨row115, (List.forall_mem_cons.mpr ⟨row116, (List.forall_mem_cons.mpr ⟨row117, (List.forall_mem_cons.mpr ⟨row128, (List.forall_mem_cons.mpr ⟨row131, (List.forall_mem_cons.mpr ⟨row132, (List.forall_mem_cons.mpr ⟨row133, (List.forall_mem_cons.mpr ⟨row134, (List.forall_mem_cons.mpr ⟨row135, (List.forall_mem_cons.mpr ⟨row140, (List.forall_mem_cons.mpr ⟨row141, (List.forall_mem_cons.mpr ⟨row142, (List.forall_mem_cons.mpr ⟨row143, (List.forall_mem_cons.mpr ⟨row154, (List.forall_mem_cons.mpr ⟨row157, (List.forall_mem_cons.mpr ⟨row158, (List.forall_mem_cons.mpr ⟨row159, (List.forall_mem_cons.mpr ⟨row160, (List.forall_mem_cons.mpr ⟨row161, (List.forall_mem_cons.mpr ⟨row163, (List.forall_mem_cons.mpr ⟨row164, (List.forall_mem_cons.mpr ⟨row166, (List.forall_mem_cons.mpr ⟨row167, (List.forall_mem_cons.mpr ⟨row168, (List.forall_mem_cons.mpr ⟨row169, (List.forall_mem_cons.mpr ⟨row180, (List.forall_mem_cons.mpr ⟨row184, (List.forall_mem_cons.mpr ⟨row185, (List.forall_mem_cons.mpr ⟨row186, (List.forall_mem_cons.mpr ⟨row187, (List.forall_mem_cons.mpr ⟨row189, (List.forall_mem_cons.mpr ⟨row190, (List.forall_mem_cons.mpr ⟨row191, (List.forall_mem_cons.mpr ⟨row192, (List.forall_mem_cons.mpr ⟨row193, (List.forall_mem_cons.mpr ⟨row194, (List.forall_mem_cons.mpr ⟨row206, (List.forall_mem_cons.mpr ⟨row210, (List.forall_mem_cons.mpr ⟨row211, (List.forall_mem_cons.mpr ⟨row212, (List.forall_mem_cons.mpr ⟨row213, (List.forall_mem_cons.mpr ⟨row214, (List.forall_mem_cons.mpr ⟨row215, (List.forall_mem_cons.mpr ⟨row216, (List.forall_mem_cons.mpr ⟨row218, (List.forall_mem_cons.mpr ⟨row219, (List.forall_mem_cons.mpr ⟨row220, (List.forall_mem_cons.mpr ⟨row232, (List.forall_mem_cons.mpr ⟨row236, (List.forall_mem_cons.mpr ⟨row237, (List.forall_mem_cons.mpr ⟨row238, (List.forall_mem_cons.mpr ⟨row239, (List.forall_mem_cons.mpr ⟨row241, (List.forall_mem_cons.mpr ⟨row242, (List.forall_mem_cons.mpr ⟨row244, (List.forall_mem_cons.mpr ⟨row245, (List.forall_mem_cons.mpr ⟨row246, (List.forall_mem_cons.mpr ⟨row252, (List.forall_mem_cons.mpr ⟨row253, (List.forall_mem_cons.mpr ⟨row254, (List.forall_mem_cons.mpr ⟨row255, (List.forall_mem_cons.mpr ⟨row256, (List.forall_mem_cons.mpr ⟨row258, (List.forall_mem_cons.mpr ⟨row262, (List.forall_mem_cons.mpr ⟨row263, (List.forall_mem_cons.mpr ⟨row264, (List.forall_mem_cons.mpr ⟨row265, (List.forall_mem_cons.mpr ⟨row270, (List.forall_mem_cons.mpr ⟨row271, (List.forall_mem_cons.mpr ⟨row272, (List.forall_mem_cons.mpr ⟨row276, (List.forall_mem_cons.mpr ⟨row278, (List.forall_mem_cons.mpr ⟨row279, (List.forall_mem_cons.mpr ⟨row280, (List.forall_mem_cons.mpr ⟨row281, (List.forall_mem_cons.mpr ⟨row282, (List.forall_mem_cons.mpr ⟨row284, (List.forall_mem_cons.mpr ⟨row288, (List.forall_mem_cons.mpr ⟨row289, (List.forall_mem_cons.mpr ⟨row290, (List.forall_mem_cons.mpr ⟨row291, (List.forall_mem_cons.mpr ⟨row292, (List.forall_mem_cons.mpr ⟨row293, (List.forall_mem_cons.mpr ⟨row294, (List.forall_mem_cons.mpr ⟨row296, (List.forall_mem_cons.mpr ⟨row297, (List.forall_mem_cons.mpr ⟨row304, (List.forall_mem_cons.mpr ⟨row305, (List.forall_mem_cons.mpr ⟨row306, (List.forall_mem_cons.mpr ⟨row307, (List.forall_mem_cons.mpr ⟨row308, (List.forall_mem_cons.mpr ⟨row310, (List.forall_mem_cons.mpr ⟨row317, (List.forall_mem_cons.mpr ⟨row318, (List.forall_mem_cons.mpr ⟨row319, (List.forall_mem_cons.mpr ⟨row320, (List.forall_mem_cons.mpr ⟨row322, (List.forall_mem_cons.mpr ⟨row328, (List.forall_mem_cons.mpr ⟨row330, (List.forall_mem_cons.mpr ⟨row331, (List.forall_mem_cons.mpr ⟨row332, (List.forall_mem_cons.mpr ⟨row333, (List.forall_mem_cons.mpr ⟨row334, (List.forall_mem_cons.mpr ⟨row336, (List.forall_mem_cons.mpr ⟨row345, (List.forall_mem_cons.mpr ⟨row348, (List.forall_mem_cons.mpr ⟨row356, (List.forall_mem_cons.mpr ⟨row357, (List.forall_mem_cons.mpr ⟨row358, (List.forall_mem_cons.mpr ⟨row359, (List.forall_mem_cons.mpr ⟨row360, (List.forall_mem_cons.mpr ⟨row370, (List.forall_mem_cons.mpr ⟨row371, (List.forall_mem_cons.mpr ⟨row372, (List.forall_mem_cons.mpr ⟨row373, (List.forall_mem_cons.mpr ⟨row374, (List.forall_mem_cons.mpr ⟨row380, (List.forall_mem_cons.mpr ⟨row382, (List.forall_mem_cons.mpr ⟨row383, (List.forall_mem_cons.mpr ⟨row384, (List.forall_mem_cons.mpr ⟨row385, (List.forall_mem_cons.mpr ⟨row386, (List.forall_mem_cons.mpr ⟨row396, (List.forall_mem_cons.mpr ⟨row397, (List.forall_mem_cons.mpr ⟨row399, (List.forall_mem_cons.mpr ⟨row400, (List.forall_mem_cons.mpr ⟨row408, (List.forall_mem_cons.mpr ⟨row409, (List.forall_mem_cons.mpr ⟨row410, (List.forall_mem_cons.mpr ⟨row411, (List.forall_mem_cons.mpr ⟨row412, (by intro player member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
def certificate : Certificate soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential where
  allowance := 2
  support := support
  unique := by decide
  bonus := bonus
  nonnegative := nonnegative
  walk := by
    intro player floor direction target adjacent targetFloor p guard
    exact row_walk (all_rows player floor p) direction target adjacent targetFloor guard
  stay := by
    intro player floor direction source first landing diagonal adjacent sourceFloor firstAdj firstFloor target p guard
    exact row_stay (all_rows player floor p) direction source first landing diagonal adjacent sourceFloor firstAdj firstFloor target guard
  consume := by
    intro player floor direction source first landing diagonal adjacent sourceFloor firstAdj firstFloor target hole p guard
    exact row_consume (all_rows player floor p) direction source first landing diagonal adjacent sourceFloor firstAdj firstFloor target hole guard
  goal := goal
theorem initial_value : value certificate soko1_2.initial = 217 := by decide
/-- A partial lower bound, not initial pushes-optimality. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_2.board soko1_2.initial directions final pushes moves)
    (completed : Goal final) : 217 ≤ pushes :=
  pushes_minimal_of_potential (stepBound certificate Generated.soko1_2_potential_valid)
    (goalBound certificate Generated.soko1_2_potential_valid) 217 initial_value trace completed
end NetHack.Sokoban12CostPartition
