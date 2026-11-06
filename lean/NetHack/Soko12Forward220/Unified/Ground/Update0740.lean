import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0740_0_checked : (List.range' 378880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0740_1_checked : (List.range' 379008 96).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0740_range (index : Nat) (lower : 378880 ≤ index) (upper : index < 379104) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 379008 then
    exact segment_sound _ 378880 128 Update0740_0_checked index (by omega) (by omega)
  else
    exact segment_sound _ 379008 96 Update0740_1_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
