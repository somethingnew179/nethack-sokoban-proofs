import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0271_0_checked : (List.range' 138752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0271_1_checked : (List.range' 138880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0271_2_checked : (List.range' 139008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0271_3_checked : (List.range' 139136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0271_range (index : Nat) (lower : 138752 ≤ index) (upper : index < 139264) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 139008 then
    if cut : index < 138880 then
      exact segment_sound _ 138752 128 Update0271_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 138880 128 Update0271_1_checked index (by omega) (by omega)
  else
    if cut : index < 139136 then
      exact segment_sound _ 139008 128 Update0271_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 139136 128 Update0271_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
