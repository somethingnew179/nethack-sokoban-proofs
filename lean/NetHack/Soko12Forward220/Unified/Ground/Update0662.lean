import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0662_0_checked : (List.range' 338944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0662_1_checked : (List.range' 339072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0662_2_checked : (List.range' 339200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0662_3_checked : (List.range' 339328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0662_range (index : Nat) (lower : 338944 ≤ index) (upper : index < 339456) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 339200 then
    if cut : index < 339072 then
      exact segment_sound _ 338944 128 Update0662_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 339072 128 Update0662_1_checked index (by omega) (by omega)
  else
    if cut : index < 339328 then
      exact segment_sound _ 339200 128 Update0662_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 339328 128 Update0662_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
