import NetHack.Sokoban32Refined.Directions28
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem row28 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir28_north p
  | south => exact dir28_south p
  | east => exact dir28_east p
  | west => exact dir28_west p
  | northEast => exact dir28_northEast p
  | northWest => exact dir28_northWest p
  | southEast => exact dir28_southEast p
  | southWest => exact dir28_southWest p
theorem row29 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 direction p) = true
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
theorem row42 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 direction p) = true
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
theorem row43 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 direction p) = true
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
theorem row44 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 direction p) = true
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
theorem row45 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 direction p) = true
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
theorem row46 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 direction p) = true
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
theorem row47 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 direction p) = true
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
theorem row48 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 direction p) = true
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
theorem row49 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 direction p) = true
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
theorem row50 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 direction p) = true
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
theorem row53 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir53_north p
  | south => exact dir53_south p
  | east => exact dir53_east p
  | west => exact dir53_west p
  | northEast => exact dir53_northEast p
  | northWest => exact dir53_northWest p
  | southEast => exact dir53_southEast p
  | southWest => exact dir53_southWest p
theorem row54 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir54_north p
  | south => exact dir54_south p
  | east => exact dir54_east p
  | west => exact dir54_west p
  | northEast => exact dir54_northEast p
  | northWest => exact dir54_northWest p
  | southEast => exact dir54_southEast p
  | southWest => exact dir54_southWest p
theorem row55 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 direction p) = true
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
theorem row56 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 direction p) = true
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
theorem row57 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir57_north p
  | south => exact dir57_south p
  | east => exact dir57_east p
  | west => exact dir57_west p
  | northEast => exact dir57_northEast p
  | northWest => exact dir57_northWest p
  | southEast => exact dir57_southEast p
  | southWest => exact dir57_southWest p
theorem row58 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir58_north p
  | south => exact dir58_south p
  | east => exact dir58_east p
  | west => exact dir58_west p
  | northEast => exact dir58_northEast p
  | northWest => exact dir58_northWest p
  | southEast => exact dir58_southEast p
  | southWest => exact dir58_southWest p
theorem row59 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir59_north p
  | south => exact dir59_south p
  | east => exact dir59_east p
  | west => exact dir59_west p
  | northEast => exact dir59_northEast p
  | northWest => exact dir59_northWest p
  | southEast => exact dir59_southEast p
  | southWest => exact dir59_southWest p
theorem row60 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir60_north p
  | south => exact dir60_south p
  | east => exact dir60_east p
  | west => exact dir60_west p
  | northEast => exact dir60_northEast p
  | northWest => exact dir60_northWest p
  | southEast => exact dir60_southEast p
  | southWest => exact dir60_southWest p
theorem row61 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir61_north p
  | south => exact dir61_south p
  | east => exact dir61_east p
  | west => exact dir61_west p
  | northEast => exact dir61_northEast p
  | northWest => exact dir61_northWest p
  | southEast => exact dir61_southEast p
  | southWest => exact dir61_southWest p
theorem row62 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir62_north p
  | south => exact dir62_south p
  | east => exact dir62_east p
  | west => exact dir62_west p
  | northEast => exact dir62_northEast p
  | northWest => exact dir62_northWest p
  | southEast => exact dir62_southEast p
  | southWest => exact dir62_southWest p
theorem row68 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir68_north p
  | south => exact dir68_south p
  | east => exact dir68_east p
  | west => exact dir68_west p
  | northEast => exact dir68_northEast p
  | northWest => exact dir68_northWest p
  | southEast => exact dir68_southEast p
  | southWest => exact dir68_southWest p
theorem row69 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir69_north p
  | south => exact dir69_south p
  | east => exact dir69_east p
  | west => exact dir69_west p
  | northEast => exact dir69_northEast p
  | northWest => exact dir69_northWest p
  | southEast => exact dir69_southEast p
  | southWest => exact dir69_southWest p
theorem row70 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir70_north p
  | south => exact dir70_south p
  | east => exact dir70_east p
  | west => exact dir70_west p
  | northEast => exact dir70_northEast p
  | northWest => exact dir70_northWest p
  | southEast => exact dir70_southEast p
  | southWest => exact dir70_southWest p
theorem row71 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir71_north p
  | south => exact dir71_south p
  | east => exact dir71_east p
  | west => exact dir71_west p
  | northEast => exact dir71_northEast p
  | northWest => exact dir71_northWest p
  | southEast => exact dir71_southEast p
  | southWest => exact dir71_southWest p
theorem row72 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir72_north p
  | south => exact dir72_south p
  | east => exact dir72_east p
  | west => exact dir72_west p
  | northEast => exact dir72_northEast p
  | northWest => exact dir72_northWest p
  | southEast => exact dir72_southEast p
  | southWest => exact dir72_southWest p
theorem row73 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir73_north p
  | south => exact dir73_south p
  | east => exact dir73_east p
  | west => exact dir73_west p
  | northEast => exact dir73_northEast p
  | northWest => exact dir73_northWest p
  | southEast => exact dir73_southEast p
  | southWest => exact dir73_southWest p
theorem row74 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir74_north p
  | south => exact dir74_south p
  | east => exact dir74_east p
  | west => exact dir74_west p
  | northEast => exact dir74_northEast p
  | northWest => exact dir74_northWest p
  | southEast => exact dir74_southEast p
  | southWest => exact dir74_southWest p
theorem row75 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir75_north p
  | south => exact dir75_south p
  | east => exact dir75_east p
  | west => exact dir75_west p
  | northEast => exact dir75_northEast p
  | northWest => exact dir75_northWest p
  | southEast => exact dir75_southEast p
  | southWest => exact dir75_southWest p
theorem row76 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 direction p) = true
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
theorem row79 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir79_north p
  | south => exact dir79_south p
  | east => exact dir79_east p
  | west => exact dir79_west p
  | northEast => exact dir79_northEast p
  | northWest => exact dir79_northWest p
  | southEast => exact dir79_southEast p
  | southWest => exact dir79_southWest p
theorem row80 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir80_north p
  | south => exact dir80_south p
  | east => exact dir80_east p
  | west => exact dir80_west p
  | northEast => exact dir80_northEast p
  | northWest => exact dir80_northWest p
  | southEast => exact dir80_southEast p
  | southWest => exact dir80_southWest p
theorem row86 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir86_north p
  | south => exact dir86_south p
  | east => exact dir86_east p
  | west => exact dir86_west p
  | northEast => exact dir86_northEast p
  | northWest => exact dir86_northWest p
  | southEast => exact dir86_southEast p
  | southWest => exact dir86_southWest p
theorem row88 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir88_north p
  | south => exact dir88_south p
  | east => exact dir88_east p
  | west => exact dir88_west p
  | northEast => exact dir88_northEast p
  | northWest => exact dir88_northWest p
  | southEast => exact dir88_southEast p
  | southWest => exact dir88_southWest p
theorem row94 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir94_north p
  | south => exact dir94_south p
  | east => exact dir94_east p
  | west => exact dir94_west p
  | northEast => exact dir94_northEast p
  | northWest => exact dir94_northWest p
  | southEast => exact dir94_southEast p
  | southWest => exact dir94_southWest p
theorem row95 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir95_north p
  | south => exact dir95_south p
  | east => exact dir95_east p
  | west => exact dir95_west p
  | northEast => exact dir95_northEast p
  | northWest => exact dir95_northWest p
  | southEast => exact dir95_southEast p
  | southWest => exact dir95_southWest p
theorem row96 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir96_north p
  | south => exact dir96_south p
  | east => exact dir96_east p
  | west => exact dir96_west p
  | northEast => exact dir96_northEast p
  | northWest => exact dir96_northWest p
  | southEast => exact dir96_southEast p
  | southWest => exact dir96_southWest p
theorem row97 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir97_north p
  | south => exact dir97_south p
  | east => exact dir97_east p
  | west => exact dir97_west p
  | northEast => exact dir97_northEast p
  | northWest => exact dir97_northWest p
  | southEast => exact dir97_southEast p
  | southWest => exact dir97_southWest p
theorem row98 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir98_north p
  | south => exact dir98_south p
  | east => exact dir98_east p
  | west => exact dir98_west p
  | northEast => exact dir98_northEast p
  | northWest => exact dir98_northWest p
  | southEast => exact dir98_southEast p
  | southWest => exact dir98_southWest p
theorem row99 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir99_north p
  | south => exact dir99_south p
  | east => exact dir99_east p
  | west => exact dir99_west p
  | northEast => exact dir99_northEast p
  | northWest => exact dir99_northWest p
  | southEast => exact dir99_southEast p
  | southWest => exact dir99_southWest p
theorem row100 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir100_north p
  | south => exact dir100_south p
  | east => exact dir100_east p
  | west => exact dir100_west p
  | northEast => exact dir100_northEast p
  | northWest => exact dir100_northWest p
  | southEast => exact dir100_southEast p
  | southWest => exact dir100_southWest p
theorem row101 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir101_north p
  | south => exact dir101_south p
  | east => exact dir101_east p
  | west => exact dir101_west p
  | northEast => exact dir101_northEast p
  | northWest => exact dir101_northWest p
  | southEast => exact dir101_southEast p
  | southWest => exact dir101_southWest p
theorem row102 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 direction p) = true
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
theorem row105 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 direction p) = true
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
theorem row106 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 direction p) = true
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
theorem row108 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 direction p) = true
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
theorem row109 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir109_north p
  | south => exact dir109_south p
  | east => exact dir109_east p
  | west => exact dir109_west p
  | northEast => exact dir109_northEast p
  | northWest => exact dir109_northWest p
  | southEast => exact dir109_southEast p
  | southWest => exact dir109_southWest p
theorem row110 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir110_north p
  | south => exact dir110_south p
  | east => exact dir110_east p
  | west => exact dir110_west p
  | northEast => exact dir110_northEast p
  | northWest => exact dir110_northWest p
  | southEast => exact dir110_southEast p
  | southWest => exact dir110_southWest p
theorem row112 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir112_north p
  | south => exact dir112_south p
  | east => exact dir112_east p
  | west => exact dir112_west p
  | northEast => exact dir112_northEast p
  | northWest => exact dir112_northWest p
  | southEast => exact dir112_southEast p
  | southWest => exact dir112_southWest p
theorem row113 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir113_north p
  | south => exact dir113_south p
  | east => exact dir113_east p
  | west => exact dir113_west p
  | northEast => exact dir113_northEast p
  | northWest => exact dir113_northWest p
  | southEast => exact dir113_southEast p
  | southWest => exact dir113_southWest p
theorem row114 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir114_north p
  | south => exact dir114_south p
  | east => exact dir114_east p
  | west => exact dir114_west p
  | northEast => exact dir114_northEast p
  | northWest => exact dir114_northWest p
  | southEast => exact dir114_southEast p
  | southWest => exact dir114_southWest p
theorem row120 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir120_north p
  | south => exact dir120_south p
  | east => exact dir120_east p
  | west => exact dir120_west p
  | northEast => exact dir120_northEast p
  | northWest => exact dir120_northWest p
  | southEast => exact dir120_southEast p
  | southWest => exact dir120_southWest p
theorem row121 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir121_north p
  | south => exact dir121_south p
  | east => exact dir121_east p
  | west => exact dir121_west p
  | northEast => exact dir121_northEast p
  | northWest => exact dir121_northWest p
  | southEast => exact dir121_southEast p
  | southWest => exact dir121_southWest p
theorem row122 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir122_north p
  | south => exact dir122_south p
  | east => exact dir122_east p
  | west => exact dir122_west p
  | northEast => exact dir122_northEast p
  | northWest => exact dir122_northWest p
  | southEast => exact dir122_southEast p
  | southWest => exact dir122_southWest p
theorem row123 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir123_north p
  | south => exact dir123_south p
  | east => exact dir123_east p
  | west => exact dir123_west p
  | northEast => exact dir123_northEast p
  | northWest => exact dir123_northWest p
  | southEast => exact dir123_southEast p
  | southWest => exact dir123_southWest p
theorem row124 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir124_north p
  | south => exact dir124_south p
  | east => exact dir124_east p
  | west => exact dir124_west p
  | northEast => exact dir124_northEast p
  | northWest => exact dir124_northWest p
  | southEast => exact dir124_southEast p
  | southWest => exact dir124_southWest p
theorem row125 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir125_north p
  | south => exact dir125_south p
  | east => exact dir125_east p
  | west => exact dir125_west p
  | northEast => exact dir125_northEast p
  | northWest => exact dir125_northWest p
  | southEast => exact dir125_southEast p
  | southWest => exact dir125_southWest p
theorem row126 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir126_north p
  | south => exact dir126_south p
  | east => exact dir126_east p
  | west => exact dir126_west p
  | northEast => exact dir126_northEast p
  | northWest => exact dir126_northWest p
  | southEast => exact dir126_southEast p
  | southWest => exact dir126_southWest p
theorem row127 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir127_north p
  | south => exact dir127_south p
  | east => exact dir127_east p
  | west => exact dir127_west p
  | northEast => exact dir127_northEast p
  | northWest => exact dir127_northWest p
  | southEast => exact dir127_southEast p
  | southWest => exact dir127_southWest p
theorem row128 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 direction p) = true
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
theorem row131 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 direction p) = true
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
theorem row132 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 direction p) = true
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
theorem row133 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 direction p) = true
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
theorem row134 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 direction p) = true
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
theorem row135 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 direction p) = true
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
theorem row136 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir136_north p
  | south => exact dir136_south p
  | east => exact dir136_east p
  | west => exact dir136_west p
  | northEast => exact dir136_northEast p
  | northWest => exact dir136_northWest p
  | southEast => exact dir136_southEast p
  | southWest => exact dir136_southWest p
theorem row137 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir137_north p
  | south => exact dir137_south p
  | east => exact dir137_east p
  | west => exact dir137_west p
  | northEast => exact dir137_northEast p
  | northWest => exact dir137_northWest p
  | southEast => exact dir137_southEast p
  | southWest => exact dir137_southWest p
theorem row138 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir138_north p
  | south => exact dir138_south p
  | east => exact dir138_east p
  | west => exact dir138_west p
  | northEast => exact dir138_northEast p
  | northWest => exact dir138_northWest p
  | southEast => exact dir138_southEast p
  | southWest => exact dir138_southWest p
theorem row139 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir139_north p
  | south => exact dir139_south p
  | east => exact dir139_east p
  | west => exact dir139_west p
  | northEast => exact dir139_northEast p
  | northWest => exact dir139_northWest p
  | southEast => exact dir139_southEast p
  | southWest => exact dir139_southWest p
theorem row146 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir146_north p
  | south => exact dir146_south p
  | east => exact dir146_east p
  | west => exact dir146_west p
  | northEast => exact dir146_northEast p
  | northWest => exact dir146_northWest p
  | southEast => exact dir146_southEast p
  | southWest => exact dir146_southWest p
theorem row147 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir147_north p
  | south => exact dir147_south p
  | east => exact dir147_east p
  | west => exact dir147_west p
  | northEast => exact dir147_northEast p
  | northWest => exact dir147_northWest p
  | southEast => exact dir147_southEast p
  | southWest => exact dir147_southWest p
theorem row148 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir148_north p
  | south => exact dir148_south p
  | east => exact dir148_east p
  | west => exact dir148_west p
  | northEast => exact dir148_northEast p
  | northWest => exact dir148_northWest p
  | southEast => exact dir148_southEast p
  | southWest => exact dir148_southWest p
theorem row149 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir149_north p
  | south => exact dir149_south p
  | east => exact dir149_east p
  | west => exact dir149_west p
  | northEast => exact dir149_northEast p
  | northWest => exact dir149_northWest p
  | southEast => exact dir149_southEast p
  | southWest => exact dir149_southWest p
theorem row150 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir150_north p
  | south => exact dir150_south p
  | east => exact dir150_east p
  | west => exact dir150_west p
  | northEast => exact dir150_northEast p
  | northWest => exact dir150_northWest p
  | southEast => exact dir150_southEast p
  | southWest => exact dir150_southWest p
theorem row151 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir151_north p
  | south => exact dir151_south p
  | east => exact dir151_east p
  | west => exact dir151_west p
  | northEast => exact dir151_northEast p
  | northWest => exact dir151_northWest p
  | southEast => exact dir151_southEast p
  | southWest => exact dir151_southWest p
theorem row152 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir152_north p
  | south => exact dir152_south p
  | east => exact dir152_east p
  | west => exact dir152_west p
  | northEast => exact dir152_northEast p
  | northWest => exact dir152_northWest p
  | southEast => exact dir152_southEast p
  | southWest => exact dir152_southWest p
theorem row153 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir153_north p
  | south => exact dir153_south p
  | east => exact dir153_east p
  | west => exact dir153_west p
  | northEast => exact dir153_northEast p
  | northWest => exact dir153_northWest p
  | southEast => exact dir153_southEast p
  | southWest => exact dir153_southWest p
theorem row154 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 direction p) = true
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
theorem row157 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 direction p) = true
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
theorem row158 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 direction p) = true
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
theorem row159 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 direction p) = true
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
theorem row160 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 direction p) = true
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
theorem row161 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 direction p) = true
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
theorem row162 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir162_north p
  | south => exact dir162_south p
  | east => exact dir162_east p
  | west => exact dir162_west p
  | northEast => exact dir162_northEast p
  | northWest => exact dir162_northWest p
  | southEast => exact dir162_southEast p
  | southWest => exact dir162_southWest p
theorem row163 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 direction p) = true
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
theorem row165 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir165_north p
  | south => exact dir165_south p
  | east => exact dir165_east p
  | west => exact dir165_west p
  | northEast => exact dir165_northEast p
  | northWest => exact dir165_northWest p
  | southEast => exact dir165_southEast p
  | southWest => exact dir165_southWest p
theorem row166 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 direction p) = true
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
theorem row172 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir172_north p
  | south => exact dir172_south p
  | east => exact dir172_east p
  | west => exact dir172_west p
  | northEast => exact dir172_northEast p
  | northWest => exact dir172_northWest p
  | southEast => exact dir172_southEast p
  | southWest => exact dir172_southWest p
theorem row173 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir173_north p
  | south => exact dir173_south p
  | east => exact dir173_east p
  | west => exact dir173_west p
  | northEast => exact dir173_northEast p
  | northWest => exact dir173_northWest p
  | southEast => exact dir173_southEast p
  | southWest => exact dir173_southWest p
theorem row174 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir174_north p
  | south => exact dir174_south p
  | east => exact dir174_east p
  | west => exact dir174_west p
  | northEast => exact dir174_northEast p
  | northWest => exact dir174_northWest p
  | southEast => exact dir174_southEast p
  | southWest => exact dir174_southWest p
theorem row175 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir175_north p
  | south => exact dir175_south p
  | east => exact dir175_east p
  | west => exact dir175_west p
  | northEast => exact dir175_northEast p
  | northWest => exact dir175_northWest p
  | southEast => exact dir175_southEast p
  | southWest => exact dir175_southWest p
theorem row176 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir176_north p
  | south => exact dir176_south p
  | east => exact dir176_east p
  | west => exact dir176_west p
  | northEast => exact dir176_northEast p
  | northWest => exact dir176_northWest p
  | southEast => exact dir176_southEast p
  | southWest => exact dir176_southWest p
theorem row177 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir177_north p
  | south => exact dir177_south p
  | east => exact dir177_east p
  | west => exact dir177_west p
  | northEast => exact dir177_northEast p
  | northWest => exact dir177_northWest p
  | southEast => exact dir177_southEast p
  | southWest => exact dir177_southWest p
theorem row178 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir178_north p
  | south => exact dir178_south p
  | east => exact dir178_east p
  | west => exact dir178_west p
  | northEast => exact dir178_northEast p
  | northWest => exact dir178_northWest p
  | southEast => exact dir178_southEast p
  | southWest => exact dir178_southWest p
theorem row179 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir179_north p
  | south => exact dir179_south p
  | east => exact dir179_east p
  | west => exact dir179_west p
  | northEast => exact dir179_northEast p
  | northWest => exact dir179_northWest p
  | southEast => exact dir179_southEast p
  | southWest => exact dir179_southWest p
theorem row180 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 direction p) = true
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
theorem row183 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir183_north p
  | south => exact dir183_south p
  | east => exact dir183_east p
  | west => exact dir183_west p
  | northEast => exact dir183_northEast p
  | northWest => exact dir183_northWest p
  | southEast => exact dir183_southEast p
  | southWest => exact dir183_southWest p
theorem row188 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir188_north p
  | south => exact dir188_south p
  | east => exact dir188_east p
  | west => exact dir188_west p
  | northEast => exact dir188_northEast p
  | northWest => exact dir188_northWest p
  | southEast => exact dir188_southEast p
  | southWest => exact dir188_southWest p
theorem row189 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 direction p) = true
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
theorem row192 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 direction p) = true
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
theorem row198 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir198_north p
  | south => exact dir198_south p
  | east => exact dir198_east p
  | west => exact dir198_west p
  | northEast => exact dir198_northEast p
  | northWest => exact dir198_northWest p
  | southEast => exact dir198_southEast p
  | southWest => exact dir198_southWest p
theorem row199 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir199_north p
  | south => exact dir199_south p
  | east => exact dir199_east p
  | west => exact dir199_west p
  | northEast => exact dir199_northEast p
  | northWest => exact dir199_northWest p
  | southEast => exact dir199_southEast p
  | southWest => exact dir199_southWest p
theorem row200 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir200_north p
  | south => exact dir200_south p
  | east => exact dir200_east p
  | west => exact dir200_west p
  | northEast => exact dir200_northEast p
  | northWest => exact dir200_northWest p
  | southEast => exact dir200_southEast p
  | southWest => exact dir200_southWest p
theorem row201 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir201_north p
  | south => exact dir201_south p
  | east => exact dir201_east p
  | west => exact dir201_west p
  | northEast => exact dir201_northEast p
  | northWest => exact dir201_northWest p
  | southEast => exact dir201_southEast p
  | southWest => exact dir201_southWest p
theorem row202 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir202_north p
  | south => exact dir202_south p
  | east => exact dir202_east p
  | west => exact dir202_west p
  | northEast => exact dir202_northEast p
  | northWest => exact dir202_northWest p
  | southEast => exact dir202_southEast p
  | southWest => exact dir202_southWest p
theorem row203 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir203_north p
  | south => exact dir203_south p
  | east => exact dir203_east p
  | west => exact dir203_west p
  | northEast => exact dir203_northEast p
  | northWest => exact dir203_northWest p
  | southEast => exact dir203_southEast p
  | southWest => exact dir203_southWest p
theorem row204 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir204_north p
  | south => exact dir204_south p
  | east => exact dir204_east p
  | west => exact dir204_west p
  | northEast => exact dir204_northEast p
  | northWest => exact dir204_northWest p
  | southEast => exact dir204_southEast p
  | southWest => exact dir204_southWest p
theorem row205 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir205_north p
  | south => exact dir205_south p
  | east => exact dir205_east p
  | west => exact dir205_west p
  | northEast => exact dir205_northEast p
  | northWest => exact dir205_northWest p
  | southEast => exact dir205_southEast p
  | southWest => exact dir205_southWest p
theorem row206 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 direction p) = true
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
theorem row209 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir209_north p
  | south => exact dir209_south p
  | east => exact dir209_east p
  | west => exact dir209_west p
  | northEast => exact dir209_northEast p
  | northWest => exact dir209_northWest p
  | southEast => exact dir209_southEast p
  | southWest => exact dir209_southWest p
theorem row210 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 direction p) = true
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
theorem row211 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 direction p) = true
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
theorem row212 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 direction p) = true
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
theorem row213 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 direction p) = true
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
theorem row214 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 direction p) = true
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
theorem row215 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 direction p) = true
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
theorem row216 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 direction p) = true
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
theorem row218 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 direction p) = true
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
theorem row224 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir224_north p
  | south => exact dir224_south p
  | east => exact dir224_east p
  | west => exact dir224_west p
  | northEast => exact dir224_northEast p
  | northWest => exact dir224_northWest p
  | southEast => exact dir224_southEast p
  | southWest => exact dir224_southWest p
theorem row225 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir225_north p
  | south => exact dir225_south p
  | east => exact dir225_east p
  | west => exact dir225_west p
  | northEast => exact dir225_northEast p
  | northWest => exact dir225_northWest p
  | southEast => exact dir225_southEast p
  | southWest => exact dir225_southWest p
theorem row226 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir226_north p
  | south => exact dir226_south p
  | east => exact dir226_east p
  | west => exact dir226_west p
  | northEast => exact dir226_northEast p
  | northWest => exact dir226_northWest p
  | southEast => exact dir226_southEast p
  | southWest => exact dir226_southWest p
theorem row227 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir227_north p
  | south => exact dir227_south p
  | east => exact dir227_east p
  | west => exact dir227_west p
  | northEast => exact dir227_northEast p
  | northWest => exact dir227_northWest p
  | southEast => exact dir227_southEast p
  | southWest => exact dir227_southWest p
theorem row228 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir228_north p
  | south => exact dir228_south p
  | east => exact dir228_east p
  | west => exact dir228_west p
  | northEast => exact dir228_northEast p
  | northWest => exact dir228_northWest p
  | southEast => exact dir228_southEast p
  | southWest => exact dir228_southWest p
theorem row229 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir229_north p
  | south => exact dir229_south p
  | east => exact dir229_east p
  | west => exact dir229_west p
  | northEast => exact dir229_northEast p
  | northWest => exact dir229_northWest p
  | southEast => exact dir229_southEast p
  | southWest => exact dir229_southWest p
theorem row230 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir230_north p
  | south => exact dir230_south p
  | east => exact dir230_east p
  | west => exact dir230_west p
  | northEast => exact dir230_northEast p
  | northWest => exact dir230_northWest p
  | southEast => exact dir230_southEast p
  | southWest => exact dir230_southWest p
theorem row231 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir231_north p
  | south => exact dir231_south p
  | east => exact dir231_east p
  | west => exact dir231_west p
  | northEast => exact dir231_northEast p
  | northWest => exact dir231_northWest p
  | southEast => exact dir231_southEast p
  | southWest => exact dir231_southWest p
theorem row232 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 direction p) = true
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
theorem row235 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir235_north p
  | south => exact dir235_south p
  | east => exact dir235_east p
  | west => exact dir235_west p
  | northEast => exact dir235_northEast p
  | northWest => exact dir235_northWest p
  | southEast => exact dir235_southEast p
  | southWest => exact dir235_southWest p
theorem row239 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 direction p) = true
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
theorem row241 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 direction p) = true
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
theorem row242 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 direction p) = true
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
theorem row243 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir243_north p
  | south => exact dir243_south p
  | east => exact dir243_east p
  | west => exact dir243_west p
  | northEast => exact dir243_northEast p
  | northWest => exact dir243_northWest p
  | southEast => exact dir243_southEast p
  | southWest => exact dir243_southWest p
theorem row244 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 direction p) = true
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
theorem row245 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 direction p) = true
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
theorem row261 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir261_north p
  | south => exact dir261_south p
  | east => exact dir261_east p
  | west => exact dir261_west p
  | northEast => exact dir261_northEast p
  | northWest => exact dir261_northWest p
  | southEast => exact dir261_southEast p
  | southWest => exact dir261_southWest p
theorem row262 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 direction p) = true
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
theorem row263 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 direction p) = true
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
theorem row265 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 direction p) = true
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
theorem row266 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir266_north p
  | south => exact dir266_south p
  | east => exact dir266_east p
  | west => exact dir266_west p
  | northEast => exact dir266_northEast p
  | northWest => exact dir266_northWest p
  | southEast => exact dir266_southEast p
  | southWest => exact dir266_southWest p
theorem row267 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir267_north p
  | south => exact dir267_south p
  | east => exact dir267_east p
  | west => exact dir267_west p
  | northEast => exact dir267_northEast p
  | northWest => exact dir267_northWest p
  | southEast => exact dir267_southEast p
  | southWest => exact dir267_southWest p
theorem row269 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir269_north p
  | south => exact dir269_south p
  | east => exact dir269_east p
  | west => exact dir269_west p
  | northEast => exact dir269_northEast p
  | northWest => exact dir269_northWest p
  | southEast => exact dir269_southEast p
  | southWest => exact dir269_southWest p
theorem row270 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 direction p) = true
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
theorem row271 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 direction p) = true
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
theorem row272 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 direction p) = true
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
theorem row273 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir273_north p
  | south => exact dir273_south p
  | east => exact dir273_east p
  | west => exact dir273_west p
  | northEast => exact dir273_northEast p
  | northWest => exact dir273_northWest p
  | southEast => exact dir273_southEast p
  | southWest => exact dir273_southWest p
theorem row274 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir274_north p
  | south => exact dir274_south p
  | east => exact dir274_east p
  | west => exact dir274_west p
  | northEast => exact dir274_northEast p
  | northWest => exact dir274_northWest p
  | southEast => exact dir274_southEast p
  | southWest => exact dir274_southWest p
theorem row275 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir275_north p
  | south => exact dir275_south p
  | east => exact dir275_east p
  | west => exact dir275_west p
  | northEast => exact dir275_northEast p
  | northWest => exact dir275_northWest p
  | southEast => exact dir275_southEast p
  | southWest => exact dir275_southWest p
theorem row276 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 direction p) = true
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
theorem row277 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir277_north p
  | south => exact dir277_south p
  | east => exact dir277_east p
  | west => exact dir277_west p
  | northEast => exact dir277_northEast p
  | northWest => exact dir277_northWest p
  | southEast => exact dir277_southEast p
  | southWest => exact dir277_southWest p
theorem row278 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 direction p) = true
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
theorem row279 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 direction p) = true
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
theorem row280 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 direction p) = true
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
theorem row281 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 direction p) = true
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
theorem row282 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 direction p) = true
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
theorem row283 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir283_north p
  | south => exact dir283_south p
  | east => exact dir283_east p
  | west => exact dir283_west p
  | northEast => exact dir283_northEast p
  | northWest => exact dir283_northWest p
  | southEast => exact dir283_southEast p
  | southWest => exact dir283_southWest p
theorem row284 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 direction p) = true
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
theorem row287 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir287_north p
  | south => exact dir287_south p
  | east => exact dir287_east p
  | west => exact dir287_west p
  | northEast => exact dir287_northEast p
  | northWest => exact dir287_northWest p
  | southEast => exact dir287_southEast p
  | southWest => exact dir287_southWest p
theorem row288 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 direction p) = true
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
theorem row289 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 direction p) = true
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
theorem row290 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 direction p) = true
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
theorem row291 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 direction p) = true
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
theorem row292 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 direction p) = true
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
theorem row293 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 direction p) = true
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
theorem row294 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 direction p) = true
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
theorem row295 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir295_north p
  | south => exact dir295_south p
  | east => exact dir295_east p
  | west => exact dir295_west p
  | northEast => exact dir295_northEast p
  | northWest => exact dir295_northWest p
  | southEast => exact dir295_southEast p
  | southWest => exact dir295_southWest p
theorem row317 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 direction p) = true
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
theorem row318 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 direction p) = true
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
theorem row320 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 direction p) = true
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
theorem row321 (p : Pattern) : rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 p = true := by
  change allDirs.all (fun direction => directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir321_north p
  | south => exact dir321_south p
  | east => exact dir321_east p
  | west => exact dir321_west p
  | northEast => exact dir321_northEast p
  | northWest => exact dir321_northWest p
  | southEast => exact dir321_southEast p
  | southWest => exact dir321_southWest p
theorem all_rows : ∀ player ∈ soko3_2.board.floor, ∀ p, rowCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus player p = true := by
  exact List.forall_mem_cons.mpr ⟨row28, (List.forall_mem_cons.mpr ⟨row29, (List.forall_mem_cons.mpr ⟨row42, (List.forall_mem_cons.mpr ⟨row43, (List.forall_mem_cons.mpr ⟨row44, (List.forall_mem_cons.mpr ⟨row45, (List.forall_mem_cons.mpr ⟨row46, (List.forall_mem_cons.mpr ⟨row47, (List.forall_mem_cons.mpr ⟨row48, (List.forall_mem_cons.mpr ⟨row49, (List.forall_mem_cons.mpr ⟨row50, (List.forall_mem_cons.mpr ⟨row53, (List.forall_mem_cons.mpr ⟨row54, (List.forall_mem_cons.mpr ⟨row55, (List.forall_mem_cons.mpr ⟨row56, (List.forall_mem_cons.mpr ⟨row57, (List.forall_mem_cons.mpr ⟨row58, (List.forall_mem_cons.mpr ⟨row59, (List.forall_mem_cons.mpr ⟨row60, (List.forall_mem_cons.mpr ⟨row61, (List.forall_mem_cons.mpr ⟨row62, (List.forall_mem_cons.mpr ⟨row68, (List.forall_mem_cons.mpr ⟨row69, (List.forall_mem_cons.mpr ⟨row70, (List.forall_mem_cons.mpr ⟨row71, (List.forall_mem_cons.mpr ⟨row72, (List.forall_mem_cons.mpr ⟨row73, (List.forall_mem_cons.mpr ⟨row74, (List.forall_mem_cons.mpr ⟨row75, (List.forall_mem_cons.mpr ⟨row76, (List.forall_mem_cons.mpr ⟨row79, (List.forall_mem_cons.mpr ⟨row80, (List.forall_mem_cons.mpr ⟨row86, (List.forall_mem_cons.mpr ⟨row88, (List.forall_mem_cons.mpr ⟨row94, (List.forall_mem_cons.mpr ⟨row95, (List.forall_mem_cons.mpr ⟨row96, (List.forall_mem_cons.mpr ⟨row97, (List.forall_mem_cons.mpr ⟨row98, (List.forall_mem_cons.mpr ⟨row99, (List.forall_mem_cons.mpr ⟨row100, (List.forall_mem_cons.mpr ⟨row101, (List.forall_mem_cons.mpr ⟨row102, (List.forall_mem_cons.mpr ⟨row105, (List.forall_mem_cons.mpr ⟨row106, (List.forall_mem_cons.mpr ⟨row108, (List.forall_mem_cons.mpr ⟨row109, (List.forall_mem_cons.mpr ⟨row110, (List.forall_mem_cons.mpr ⟨row112, (List.forall_mem_cons.mpr ⟨row113, (List.forall_mem_cons.mpr ⟨row114, (List.forall_mem_cons.mpr ⟨row120, (List.forall_mem_cons.mpr ⟨row121, (List.forall_mem_cons.mpr ⟨row122, (List.forall_mem_cons.mpr ⟨row123, (List.forall_mem_cons.mpr ⟨row124, (List.forall_mem_cons.mpr ⟨row125, (List.forall_mem_cons.mpr ⟨row126, (List.forall_mem_cons.mpr ⟨row127, (List.forall_mem_cons.mpr ⟨row128, (List.forall_mem_cons.mpr ⟨row131, (List.forall_mem_cons.mpr ⟨row132, (List.forall_mem_cons.mpr ⟨row133, (List.forall_mem_cons.mpr ⟨row134, (List.forall_mem_cons.mpr ⟨row135, (List.forall_mem_cons.mpr ⟨row136, (List.forall_mem_cons.mpr ⟨row137, (List.forall_mem_cons.mpr ⟨row138, (List.forall_mem_cons.mpr ⟨row139, (List.forall_mem_cons.mpr ⟨row146, (List.forall_mem_cons.mpr ⟨row147, (List.forall_mem_cons.mpr ⟨row148, (List.forall_mem_cons.mpr ⟨row149, (List.forall_mem_cons.mpr ⟨row150, (List.forall_mem_cons.mpr ⟨row151, (List.forall_mem_cons.mpr ⟨row152, (List.forall_mem_cons.mpr ⟨row153, (List.forall_mem_cons.mpr ⟨row154, (List.forall_mem_cons.mpr ⟨row157, (List.forall_mem_cons.mpr ⟨row158, (List.forall_mem_cons.mpr ⟨row159, (List.forall_mem_cons.mpr ⟨row160, (List.forall_mem_cons.mpr ⟨row161, (List.forall_mem_cons.mpr ⟨row162, (List.forall_mem_cons.mpr ⟨row163, (List.forall_mem_cons.mpr ⟨row165, (List.forall_mem_cons.mpr ⟨row166, (List.forall_mem_cons.mpr ⟨row172, (List.forall_mem_cons.mpr ⟨row173, (List.forall_mem_cons.mpr ⟨row174, (List.forall_mem_cons.mpr ⟨row175, (List.forall_mem_cons.mpr ⟨row176, (List.forall_mem_cons.mpr ⟨row177, (List.forall_mem_cons.mpr ⟨row178, (List.forall_mem_cons.mpr ⟨row179, (List.forall_mem_cons.mpr ⟨row180, (List.forall_mem_cons.mpr ⟨row183, (List.forall_mem_cons.mpr ⟨row188, (List.forall_mem_cons.mpr ⟨row189, (List.forall_mem_cons.mpr ⟨row192, (List.forall_mem_cons.mpr ⟨row198, (List.forall_mem_cons.mpr ⟨row199, (List.forall_mem_cons.mpr ⟨row200, (List.forall_mem_cons.mpr ⟨row201, (List.forall_mem_cons.mpr ⟨row202, (List.forall_mem_cons.mpr ⟨row203, (List.forall_mem_cons.mpr ⟨row204, (List.forall_mem_cons.mpr ⟨row205, (List.forall_mem_cons.mpr ⟨row206, (List.forall_mem_cons.mpr ⟨row209, (List.forall_mem_cons.mpr ⟨row210, (List.forall_mem_cons.mpr ⟨row211, (List.forall_mem_cons.mpr ⟨row212, (List.forall_mem_cons.mpr ⟨row213, (List.forall_mem_cons.mpr ⟨row214, (List.forall_mem_cons.mpr ⟨row215, (List.forall_mem_cons.mpr ⟨row216, (List.forall_mem_cons.mpr ⟨row218, (List.forall_mem_cons.mpr ⟨row224, (List.forall_mem_cons.mpr ⟨row225, (List.forall_mem_cons.mpr ⟨row226, (List.forall_mem_cons.mpr ⟨row227, (List.forall_mem_cons.mpr ⟨row228, (List.forall_mem_cons.mpr ⟨row229, (List.forall_mem_cons.mpr ⟨row230, (List.forall_mem_cons.mpr ⟨row231, (List.forall_mem_cons.mpr ⟨row232, (List.forall_mem_cons.mpr ⟨row235, (List.forall_mem_cons.mpr ⟨row239, (List.forall_mem_cons.mpr ⟨row241, (List.forall_mem_cons.mpr ⟨row242, (List.forall_mem_cons.mpr ⟨row243, (List.forall_mem_cons.mpr ⟨row244, (List.forall_mem_cons.mpr ⟨row245, (List.forall_mem_cons.mpr ⟨row261, (List.forall_mem_cons.mpr ⟨row262, (List.forall_mem_cons.mpr ⟨row263, (List.forall_mem_cons.mpr ⟨row265, (List.forall_mem_cons.mpr ⟨row266, (List.forall_mem_cons.mpr ⟨row267, (List.forall_mem_cons.mpr ⟨row269, (List.forall_mem_cons.mpr ⟨row270, (List.forall_mem_cons.mpr ⟨row271, (List.forall_mem_cons.mpr ⟨row272, (List.forall_mem_cons.mpr ⟨row273, (List.forall_mem_cons.mpr ⟨row274, (List.forall_mem_cons.mpr ⟨row275, (List.forall_mem_cons.mpr ⟨row276, (List.forall_mem_cons.mpr ⟨row277, (List.forall_mem_cons.mpr ⟨row278, (List.forall_mem_cons.mpr ⟨row279, (List.forall_mem_cons.mpr ⟨row280, (List.forall_mem_cons.mpr ⟨row281, (List.forall_mem_cons.mpr ⟨row282, (List.forall_mem_cons.mpr ⟨row283, (List.forall_mem_cons.mpr ⟨row284, (List.forall_mem_cons.mpr ⟨row287, (List.forall_mem_cons.mpr ⟨row288, (List.forall_mem_cons.mpr ⟨row289, (List.forall_mem_cons.mpr ⟨row290, (List.forall_mem_cons.mpr ⟨row291, (List.forall_mem_cons.mpr ⟨row292, (List.forall_mem_cons.mpr ⟨row293, (List.forall_mem_cons.mpr ⟨row294, (List.forall_mem_cons.mpr ⟨row295, (List.forall_mem_cons.mpr ⟨row317, (List.forall_mem_cons.mpr ⟨row318, (List.forall_mem_cons.mpr ⟨row320, (List.forall_mem_cons.mpr ⟨row321, (by intro player member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
def certificate : Certificate soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential where
  allowance := 4
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
theorem initial_value : value certificate soko3_2.initial = 136 := by decide
/-- A partial lower bound, not initial pushes-optimality. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial directions final pushes moves)
    (completed : Goal final) : 136 ≤ pushes :=
  pushes_minimal_of_potential (stepBound certificate Generated.soko3_2_potential_valid)
    (goalBound certificate Generated.soko3_2_potential_valid) 136 initial_value trace completed
end NetHack.Sokoban32Refined
