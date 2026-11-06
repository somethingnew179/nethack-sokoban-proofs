import NetHack.Sokoban.PatternBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.PatternCertificate
theorem rowFacts_checked : edges.all rowFacts = true := by decide


end NetHack.Sokoban.PatternCertificate
