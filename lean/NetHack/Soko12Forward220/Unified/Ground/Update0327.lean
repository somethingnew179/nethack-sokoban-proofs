import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0327_0_checked : (List.range' 167424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0327_1_checked : (List.range' 167552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0327_2_checked : (List.range' 167680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0327_3_checked : (List.range' 167808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0327_range (index : Nat) (lower : 167424 ≤ index) (upper : index < 167936) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 167680 then
    if cut : index < 167552 then
      exact segment_sound _ 167424 128 Update0327_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 167552 128 Update0327_1_checked index (by omega) (by omega)
  else
    if cut : index < 167808 then
      exact segment_sound _ 167680 128 Update0327_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 167808 128 Update0327_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
