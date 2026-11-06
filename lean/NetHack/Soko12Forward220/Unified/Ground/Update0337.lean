import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0337_0_checked : (List.range' 172544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0337_1_checked : (List.range' 172672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0337_2_checked : (List.range' 172800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0337_3_checked : (List.range' 172928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0337_range (index : Nat) (lower : 172544 ≤ index) (upper : index < 173056) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 172800 then
    if cut : index < 172672 then
      exact segment_sound _ 172544 128 Update0337_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 172672 128 Update0337_1_checked index (by omega) (by omega)
  else
    if cut : index < 172928 then
      exact segment_sound _ 172800 128 Update0337_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 172928 128 Update0337_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
