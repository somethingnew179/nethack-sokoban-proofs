import NetHack.Sokoban22Refined85.Directions22
import NetHack.Sokoban22Refined85.InitialNumbers
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem row25 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir25_north p
  | south => exact dir25_south p
  | east => exact dir25_east p
  | west => exact dir25_west p
  | northEast => exact dir25_northEast p
  | northWest => exact dir25_northWest p
  | southEast => exact dir25_southEast p
  | southWest => exact dir25_southWest p
theorem row27 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir27_north p
  | south => exact dir27_south p
  | east => exact dir27_east p
  | west => exact dir27_west p
  | northEast => exact dir27_northEast p
  | northWest => exact dir27_northWest p
  | southEast => exact dir27_southEast p
  | southWest => exact dir27_southWest p
theorem row28 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 direction p) = true
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
theorem row29 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 direction p) = true
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
theorem row30 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 direction p) = true
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
theorem row45 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 direction p) = true
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
theorem row46 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 direction p) = true
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
theorem row47 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 direction p) = true
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
theorem row48 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 direction p) = true
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
theorem row49 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 direction p) = true
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
theorem row50 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 direction p) = true
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
theorem row51 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir51_north p
  | south => exact dir51_south p
  | east => exact dir51_east p
  | west => exact dir51_west p
  | northEast => exact dir51_northEast p
  | northWest => exact dir51_northWest p
  | southEast => exact dir51_southEast p
  | southWest => exact dir51_southWest p
theorem row52 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir52_north p
  | south => exact dir52_south p
  | east => exact dir52_east p
  | west => exact dir52_west p
  | northEast => exact dir52_northEast p
  | northWest => exact dir52_northWest p
  | southEast => exact dir52_southEast p
  | southWest => exact dir52_southWest p
theorem row67 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir67_north p
  | south => exact dir67_south p
  | east => exact dir67_east p
  | west => exact dir67_west p
  | northEast => exact dir67_northEast p
  | northWest => exact dir67_northWest p
  | southEast => exact dir67_southEast p
  | southWest => exact dir67_southWest p
theorem row69 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 direction p) = true
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
theorem row70 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 direction p) = true
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
theorem row71 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 direction p) = true
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
theorem row73 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 direction p) = true
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
theorem row74 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 direction p) = true
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
theorem row76 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 direction p) = true
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
theorem row78 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir78_north p
  | south => exact dir78_south p
  | east => exact dir78_east p
  | west => exact dir78_west p
  | northEast => exact dir78_northEast p
  | northWest => exact dir78_northWest p
  | southEast => exact dir78_southEast p
  | southWest => exact dir78_southWest p
theorem row79 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 direction p) = true
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
theorem row80 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 direction p) = true
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
theorem row81 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir81_north p
  | south => exact dir81_south p
  | east => exact dir81_east p
  | west => exact dir81_west p
  | northEast => exact dir81_northEast p
  | northWest => exact dir81_northWest p
  | southEast => exact dir81_southEast p
  | southWest => exact dir81_southWest p
theorem row82 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 direction p) = true
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
theorem row83 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir83_north p
  | south => exact dir83_south p
  | east => exact dir83_east p
  | west => exact dir83_west p
  | northEast => exact dir83_northEast p
  | northWest => exact dir83_northWest p
  | southEast => exact dir83_southEast p
  | southWest => exact dir83_southWest p
theorem row84 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir84_north p
  | south => exact dir84_south p
  | east => exact dir84_east p
  | west => exact dir84_west p
  | northEast => exact dir84_northEast p
  | northWest => exact dir84_northWest p
  | southEast => exact dir84_southEast p
  | southWest => exact dir84_southWest p
theorem row89 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir89_north p
  | south => exact dir89_south p
  | east => exact dir89_east p
  | west => exact dir89_west p
  | northEast => exact dir89_northEast p
  | northWest => exact dir89_northWest p
  | southEast => exact dir89_southEast p
  | southWest => exact dir89_southWest p
theorem row90 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir90_north p
  | south => exact dir90_south p
  | east => exact dir90_east p
  | west => exact dir90_west p
  | northEast => exact dir90_northEast p
  | northWest => exact dir90_northWest p
  | southEast => exact dir90_southEast p
  | southWest => exact dir90_southWest p
theorem row91 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir91_north p
  | south => exact dir91_south p
  | east => exact dir91_east p
  | west => exact dir91_west p
  | northEast => exact dir91_northEast p
  | northWest => exact dir91_northWest p
  | southEast => exact dir91_southEast p
  | southWest => exact dir91_southWest p
theorem row93 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir93_north p
  | south => exact dir93_south p
  | east => exact dir93_east p
  | west => exact dir93_west p
  | northEast => exact dir93_northEast p
  | northWest => exact dir93_northWest p
  | southEast => exact dir93_southEast p
  | southWest => exact dir93_southWest p
theorem row94 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 direction p) = true
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
theorem row95 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 direction p) = true
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
theorem row96 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 direction p) = true
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
theorem row97 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 direction p) = true
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
theorem row98 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 direction p) = true
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
theorem row100 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 direction p) = true
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
theorem row101 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 direction p) = true
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
theorem row102 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 direction p) = true
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
theorem row103 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir103_north p
  | south => exact dir103_south p
  | east => exact dir103_east p
  | west => exact dir103_west p
  | northEast => exact dir103_northEast p
  | northWest => exact dir103_northWest p
  | southEast => exact dir103_southEast p
  | southWest => exact dir103_southWest p
theorem row104 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir104_north p
  | south => exact dir104_south p
  | east => exact dir104_east p
  | west => exact dir104_west p
  | northEast => exact dir104_northEast p
  | northWest => exact dir104_northWest p
  | southEast => exact dir104_southEast p
  | southWest => exact dir104_southWest p
theorem row105 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 direction p) = true
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
theorem row106 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 direction p) = true
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
theorem row111 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir111_north p
  | south => exact dir111_south p
  | east => exact dir111_east p
  | west => exact dir111_west p
  | northEast => exact dir111_northEast p
  | northWest => exact dir111_northWest p
  | southEast => exact dir111_southEast p
  | southWest => exact dir111_southWest p
theorem row113 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 direction p) = true
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
theorem row114 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 direction p) = true
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
theorem row115 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 direction p) = true
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
theorem row116 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 direction p) = true
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
theorem row118 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir118_north p
  | south => exact dir118_south p
  | east => exact dir118_east p
  | west => exact dir118_west p
  | northEast => exact dir118_northEast p
  | northWest => exact dir118_northWest p
  | southEast => exact dir118_southEast p
  | southWest => exact dir118_southWest p
theorem row119 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir119_north p
  | south => exact dir119_south p
  | east => exact dir119_east p
  | west => exact dir119_west p
  | northEast => exact dir119_northEast p
  | northWest => exact dir119_northWest p
  | southEast => exact dir119_southEast p
  | southWest => exact dir119_southWest p
theorem row120 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 direction p) = true
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
theorem row122 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 direction p) = true
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
theorem row123 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 direction p) = true
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
theorem row124 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 direction p) = true
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
theorem row125 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 direction p) = true
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
theorem row126 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 direction p) = true
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
theorem row127 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 direction p) = true
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
theorem row128 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 direction p) = true
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
theorem row133 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 direction p) = true
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
theorem row134 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 direction p) = true
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
theorem row135 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 direction p) = true
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
theorem row136 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 direction p) = true
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
theorem row138 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 direction p) = true
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
theorem row141 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 direction p) = true
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
theorem row144 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir144_north p
  | south => exact dir144_south p
  | east => exact dir144_east p
  | west => exact dir144_west p
  | northEast => exact dir144_northEast p
  | northWest => exact dir144_northWest p
  | southEast => exact dir144_southEast p
  | southWest => exact dir144_southWest p
theorem row145 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir145_north p
  | south => exact dir145_south p
  | east => exact dir145_east p
  | west => exact dir145_west p
  | northEast => exact dir145_northEast p
  | northWest => exact dir145_northWest p
  | southEast => exact dir145_southEast p
  | southWest => exact dir145_southWest p
theorem row146 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 direction p) = true
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
theorem row147 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 direction p) = true
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
theorem row148 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 direction p) = true
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
theorem row149 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 direction p) = true
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
theorem row150 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 direction p) = true
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
theorem row155 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir155_north p
  | south => exact dir155_south p
  | east => exact dir155_east p
  | west => exact dir155_west p
  | northEast => exact dir155_northEast p
  | northWest => exact dir155_northWest p
  | southEast => exact dir155_southEast p
  | southWest => exact dir155_southWest p
theorem row156 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir156_north p
  | south => exact dir156_south p
  | east => exact dir156_east p
  | west => exact dir156_west p
  | northEast => exact dir156_northEast p
  | northWest => exact dir156_northWest p
  | southEast => exact dir156_southEast p
  | southWest => exact dir156_southWest p
theorem row157 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 direction p) = true
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
theorem row158 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 direction p) = true
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
theorem row159 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 direction p) = true
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
theorem row160 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 direction p) = true
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
theorem row161 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 direction p) = true
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
theorem row162 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 direction p) = true
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
theorem row163 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 direction p) = true
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
theorem row164 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 direction p) = true
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
theorem row166 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 direction p) = true
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
theorem row167 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 direction p) = true
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
theorem row168 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 direction p) = true
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
theorem row169 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 direction p) = true
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
theorem row170 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir170_north p
  | south => exact dir170_south p
  | east => exact dir170_east p
  | west => exact dir170_west p
  | northEast => exact dir170_northEast p
  | northWest => exact dir170_northWest p
  | southEast => exact dir170_southEast p
  | southWest => exact dir170_southWest p
theorem row171 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir171_north p
  | south => exact dir171_south p
  | east => exact dir171_east p
  | west => exact dir171_west p
  | northEast => exact dir171_northEast p
  | northWest => exact dir171_northWest p
  | southEast => exact dir171_southEast p
  | southWest => exact dir171_southWest p
theorem row172 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 direction p) = true
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
theorem row177 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 direction p) = true
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
theorem row180 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 direction p) = true
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
theorem row181 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir181_north p
  | south => exact dir181_south p
  | east => exact dir181_east p
  | west => exact dir181_west p
  | northEast => exact dir181_northEast p
  | northWest => exact dir181_northWest p
  | southEast => exact dir181_southEast p
  | southWest => exact dir181_southWest p
theorem row182 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir182_north p
  | south => exact dir182_south p
  | east => exact dir182_east p
  | west => exact dir182_west p
  | northEast => exact dir182_northEast p
  | northWest => exact dir182_northWest p
  | southEast => exact dir182_southEast p
  | southWest => exact dir182_southWest p
theorem row184 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 direction p) = true
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
theorem row185 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 direction p) = true
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
theorem row186 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 direction p) = true
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
theorem row188 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 direction p) = true
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
theorem row189 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 direction p) = true
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
theorem row190 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 direction p) = true
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
theorem row191 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 direction p) = true
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
theorem row192 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 direction p) = true
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
theorem row193 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 direction p) = true
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
theorem row194 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 direction p) = true
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
theorem row199 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 direction p) = true
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
theorem row200 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 direction p) = true
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
theorem row201 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 direction p) = true
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
theorem row202 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 direction p) = true
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
theorem row204 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 direction p) = true
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
theorem row210 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 direction p) = true
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
theorem row211 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 direction p) = true
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
theorem row212 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 direction p) = true
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
theorem row213 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 direction p) = true
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
theorem row214 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 direction p) = true
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
theorem row215 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 direction p) = true
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
theorem row216 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 direction p) = true
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
theorem row218 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 direction p) = true
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
theorem row223 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir223_north p
  | south => exact dir223_south p
  | east => exact dir223_east p
  | west => exact dir223_west p
  | northEast => exact dir223_northEast p
  | northWest => exact dir223_northWest p
  | southEast => exact dir223_southEast p
  | southWest => exact dir223_southWest p
theorem row224 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 direction p) = true
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
theorem row225 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 direction p) = true
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
theorem row226 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 direction p) = true
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
theorem row240 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir240_north p
  | south => exact dir240_south p
  | east => exact dir240_east p
  | west => exact dir240_west p
  | northEast => exact dir240_northEast p
  | northWest => exact dir240_northWest p
  | southEast => exact dir240_southEast p
  | southWest => exact dir240_southWest p
theorem row245 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 direction p) = true
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
theorem row246 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 direction p) = true
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
theorem row247 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir247_north p
  | south => exact dir247_south p
  | east => exact dir247_east p
  | west => exact dir247_west p
  | northEast => exact dir247_northEast p
  | northWest => exact dir247_northWest p
  | southEast => exact dir247_southEast p
  | southWest => exact dir247_southWest p
theorem row248 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir248_north p
  | south => exact dir248_south p
  | east => exact dir248_east p
  | west => exact dir248_west p
  | northEast => exact dir248_northEast p
  | northWest => exact dir248_northWest p
  | southEast => exact dir248_southEast p
  | southWest => exact dir248_southWest p
theorem row249 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir249_north p
  | south => exact dir249_south p
  | east => exact dir249_east p
  | west => exact dir249_west p
  | northEast => exact dir249_northEast p
  | northWest => exact dir249_northWest p
  | southEast => exact dir249_southEast p
  | southWest => exact dir249_southWest p
theorem row250 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir250_north p
  | south => exact dir250_south p
  | east => exact dir250_east p
  | west => exact dir250_west p
  | northEast => exact dir250_northEast p
  | northWest => exact dir250_northWest p
  | southEast => exact dir250_southEast p
  | southWest => exact dir250_southWest p
theorem row251 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir251_north p
  | south => exact dir251_south p
  | east => exact dir251_east p
  | west => exact dir251_west p
  | northEast => exact dir251_northEast p
  | northWest => exact dir251_northWest p
  | southEast => exact dir251_southEast p
  | southWest => exact dir251_southWest p
theorem row252 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 direction p) = true
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
theorem row253 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 direction p) = true
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
theorem row254 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 direction p) = true
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
theorem row255 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 direction p) = true
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
theorem row256 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 direction p) = true
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
theorem row257 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir257_north p
  | south => exact dir257_south p
  | east => exact dir257_east p
  | west => exact dir257_west p
  | northEast => exact dir257_northEast p
  | northWest => exact dir257_northWest p
  | southEast => exact dir257_southEast p
  | southWest => exact dir257_southWest p
theorem row258 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 direction p) = true
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
theorem row259 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir259_north p
  | south => exact dir259_south p
  | east => exact dir259_east p
  | west => exact dir259_west p
  | northEast => exact dir259_northEast p
  | northWest => exact dir259_northWest p
  | southEast => exact dir259_southEast p
  | southWest => exact dir259_southWest p
theorem row260 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 direction p) = true
  apply List.all_eq_true.mpr
  intro direction member
  cases direction with
  | north => exact dir260_north p
  | south => exact dir260_south p
  | east => exact dir260_east p
  | west => exact dir260_west p
  | northEast => exact dir260_northEast p
  | northWest => exact dir260_northWest p
  | southEast => exact dir260_southEast p
  | southWest => exact dir260_southWest p
theorem row262 (p : Pattern) : rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 p = true := by
  change allDirs.all (fun direction => directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 direction p) = true
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
theorem all_rows : ∀ player ∈ soko2_2.board.floor, ∀ p, rowCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus player p = true := by
  exact List.forall_mem_cons.mpr ⟨row25, (List.forall_mem_cons.mpr ⟨row27, (List.forall_mem_cons.mpr ⟨row28, (List.forall_mem_cons.mpr ⟨row29, (List.forall_mem_cons.mpr ⟨row30, (List.forall_mem_cons.mpr ⟨row45, (List.forall_mem_cons.mpr ⟨row46, (List.forall_mem_cons.mpr ⟨row47, (List.forall_mem_cons.mpr ⟨row48, (List.forall_mem_cons.mpr ⟨row49, (List.forall_mem_cons.mpr ⟨row50, (List.forall_mem_cons.mpr ⟨row51, (List.forall_mem_cons.mpr ⟨row52, (List.forall_mem_cons.mpr ⟨row67, (List.forall_mem_cons.mpr ⟨row69, (List.forall_mem_cons.mpr ⟨row70, (List.forall_mem_cons.mpr ⟨row71, (List.forall_mem_cons.mpr ⟨row73, (List.forall_mem_cons.mpr ⟨row74, (List.forall_mem_cons.mpr ⟨row76, (List.forall_mem_cons.mpr ⟨row78, (List.forall_mem_cons.mpr ⟨row79, (List.forall_mem_cons.mpr ⟨row80, (List.forall_mem_cons.mpr ⟨row81, (List.forall_mem_cons.mpr ⟨row82, (List.forall_mem_cons.mpr ⟨row83, (List.forall_mem_cons.mpr ⟨row84, (List.forall_mem_cons.mpr ⟨row89, (List.forall_mem_cons.mpr ⟨row90, (List.forall_mem_cons.mpr ⟨row91, (List.forall_mem_cons.mpr ⟨row93, (List.forall_mem_cons.mpr ⟨row94, (List.forall_mem_cons.mpr ⟨row95, (List.forall_mem_cons.mpr ⟨row96, (List.forall_mem_cons.mpr ⟨row97, (List.forall_mem_cons.mpr ⟨row98, (List.forall_mem_cons.mpr ⟨row100, (List.forall_mem_cons.mpr ⟨row101, (List.forall_mem_cons.mpr ⟨row102, (List.forall_mem_cons.mpr ⟨row103, (List.forall_mem_cons.mpr ⟨row104, (List.forall_mem_cons.mpr ⟨row105, (List.forall_mem_cons.mpr ⟨row106, (List.forall_mem_cons.mpr ⟨row111, (List.forall_mem_cons.mpr ⟨row113, (List.forall_mem_cons.mpr ⟨row114, (List.forall_mem_cons.mpr ⟨row115, (List.forall_mem_cons.mpr ⟨row116, (List.forall_mem_cons.mpr ⟨row118, (List.forall_mem_cons.mpr ⟨row119, (List.forall_mem_cons.mpr ⟨row120, (List.forall_mem_cons.mpr ⟨row122, (List.forall_mem_cons.mpr ⟨row123, (List.forall_mem_cons.mpr ⟨row124, (List.forall_mem_cons.mpr ⟨row125, (List.forall_mem_cons.mpr ⟨row126, (List.forall_mem_cons.mpr ⟨row127, (List.forall_mem_cons.mpr ⟨row128, (List.forall_mem_cons.mpr ⟨row133, (List.forall_mem_cons.mpr ⟨row134, (List.forall_mem_cons.mpr ⟨row135, (List.forall_mem_cons.mpr ⟨row136, (List.forall_mem_cons.mpr ⟨row138, (List.forall_mem_cons.mpr ⟨row141, (List.forall_mem_cons.mpr ⟨row144, (List.forall_mem_cons.mpr ⟨row145, (List.forall_mem_cons.mpr ⟨row146, (List.forall_mem_cons.mpr ⟨row147, (List.forall_mem_cons.mpr ⟨row148, (List.forall_mem_cons.mpr ⟨row149, (List.forall_mem_cons.mpr ⟨row150, (List.forall_mem_cons.mpr ⟨row155, (List.forall_mem_cons.mpr ⟨row156, (List.forall_mem_cons.mpr ⟨row157, (List.forall_mem_cons.mpr ⟨row158, (List.forall_mem_cons.mpr ⟨row159, (List.forall_mem_cons.mpr ⟨row160, (List.forall_mem_cons.mpr ⟨row161, (List.forall_mem_cons.mpr ⟨row162, (List.forall_mem_cons.mpr ⟨row163, (List.forall_mem_cons.mpr ⟨row164, (List.forall_mem_cons.mpr ⟨row166, (List.forall_mem_cons.mpr ⟨row167, (List.forall_mem_cons.mpr ⟨row168, (List.forall_mem_cons.mpr ⟨row169, (List.forall_mem_cons.mpr ⟨row170, (List.forall_mem_cons.mpr ⟨row171, (List.forall_mem_cons.mpr ⟨row172, (List.forall_mem_cons.mpr ⟨row177, (List.forall_mem_cons.mpr ⟨row180, (List.forall_mem_cons.mpr ⟨row181, (List.forall_mem_cons.mpr ⟨row182, (List.forall_mem_cons.mpr ⟨row184, (List.forall_mem_cons.mpr ⟨row185, (List.forall_mem_cons.mpr ⟨row186, (List.forall_mem_cons.mpr ⟨row188, (List.forall_mem_cons.mpr ⟨row189, (List.forall_mem_cons.mpr ⟨row190, (List.forall_mem_cons.mpr ⟨row191, (List.forall_mem_cons.mpr ⟨row192, (List.forall_mem_cons.mpr ⟨row193, (List.forall_mem_cons.mpr ⟨row194, (List.forall_mem_cons.mpr ⟨row199, (List.forall_mem_cons.mpr ⟨row200, (List.forall_mem_cons.mpr ⟨row201, (List.forall_mem_cons.mpr ⟨row202, (List.forall_mem_cons.mpr ⟨row204, (List.forall_mem_cons.mpr ⟨row210, (List.forall_mem_cons.mpr ⟨row211, (List.forall_mem_cons.mpr ⟨row212, (List.forall_mem_cons.mpr ⟨row213, (List.forall_mem_cons.mpr ⟨row214, (List.forall_mem_cons.mpr ⟨row215, (List.forall_mem_cons.mpr ⟨row216, (List.forall_mem_cons.mpr ⟨row218, (List.forall_mem_cons.mpr ⟨row223, (List.forall_mem_cons.mpr ⟨row224, (List.forall_mem_cons.mpr ⟨row225, (List.forall_mem_cons.mpr ⟨row226, (List.forall_mem_cons.mpr ⟨row240, (List.forall_mem_cons.mpr ⟨row245, (List.forall_mem_cons.mpr ⟨row246, (List.forall_mem_cons.mpr ⟨row247, (List.forall_mem_cons.mpr ⟨row248, (List.forall_mem_cons.mpr ⟨row249, (List.forall_mem_cons.mpr ⟨row250, (List.forall_mem_cons.mpr ⟨row251, (List.forall_mem_cons.mpr ⟨row252, (List.forall_mem_cons.mpr ⟨row253, (List.forall_mem_cons.mpr ⟨row254, (List.forall_mem_cons.mpr ⟨row255, (List.forall_mem_cons.mpr ⟨row256, (List.forall_mem_cons.mpr ⟨row257, (List.forall_mem_cons.mpr ⟨row258, (List.forall_mem_cons.mpr ⟨row259, (List.forall_mem_cons.mpr ⟨row260, (List.forall_mem_cons.mpr ⟨row262, (by intro player member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
def certificate : Certificate soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential where
  allowance := 5
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
theorem initial_value : value certificate soko2_2.initial = 85 := by
  change Generated.soko2_2Potential.value soko2_2.initial +
    (if Good soko2_2.board soko2_2.initial.holes 5 soko2_2.initial then
      bonus soko2_2.initial.player (project soko2_2.initial.boulders) else 0) = 85
  rw [if_pos initial_good, initial_base, initial_bonus]
  rfl
/-- A partial lower bound, not initial pushes-optimality. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko2_2.board soko2_2.initial directions final pushes moves)
    (completed : Goal final) : 85 ≤ pushes :=
  pushes_minimal_of_potential (stepBound certificate Generated.soko2_2_potential_valid)
    (goalBound certificate Generated.soko2_2_potential_valid) 85 initial_value trace completed
end NetHack.Sokoban22Refined85
