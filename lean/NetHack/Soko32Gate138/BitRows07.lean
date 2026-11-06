import NetHack.Soko32Gate138.Bit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko32Gate138
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
def heroes07 : List Cell := soko3_2.board.floor.drop 84 |>.take 12
theorem checked07 : heroes07.all (fun hero => (allPatterns gateSupport).all (rowCheck soko3_2.board soko3_2.initial.holes localPotential gateSupport gate hero)) = true := by decide +kernel
end NetHack.Soko32Gate138
