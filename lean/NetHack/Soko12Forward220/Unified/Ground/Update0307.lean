import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0307_0_checked : (List.range' 157184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0307_1_checked : (List.range' 157312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0307_2_checked : (List.range' 157440 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0307_3_checked : (List.range' 157568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0307_range (index : Nat) (lower : 157184 ≤ index) (upper : index < 157696) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 157440 then
    if cut : index < 157312 then
      exact segment_sound _ 157184 128 Update0307_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 157312 128 Update0307_1_checked index (by omega) (by omega)
  else
    if cut : index < 157568 then
      exact segment_sound _ 157440 128 Update0307_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 157568 128 Update0307_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
