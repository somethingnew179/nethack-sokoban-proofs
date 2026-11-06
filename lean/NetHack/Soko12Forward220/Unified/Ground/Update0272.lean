import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0272_0_checked : (List.range' 139264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0272_1_checked : (List.range' 139392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0272_2_checked : (List.range' 139520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0272_3_checked : (List.range' 139648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0272_range (index : Nat) (lower : 139264 ≤ index) (upper : index < 139776) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 139520 then
    if cut : index < 139392 then
      exact segment_sound _ 139264 128 Update0272_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 139392 128 Update0272_1_checked index (by omega) (by omega)
  else
    if cut : index < 139648 then
      exact segment_sound _ 139520 128 Update0272_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 139648 128 Update0272_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
