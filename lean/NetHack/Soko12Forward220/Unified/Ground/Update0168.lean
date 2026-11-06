import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0168_0_checked : (List.range' 86016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0168_1_checked : (List.range' 86144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0168_2_checked : (List.range' 86272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0168_3_checked : (List.range' 86400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0168_range (index : Nat) (lower : 86016 ≤ index) (upper : index < 86528) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 86272 then
    if cut : index < 86144 then
      exact segment_sound _ 86016 128 Update0168_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 86144 128 Update0168_1_checked index (by omega) (by omega)
  else
    if cut : index < 86400 then
      exact segment_sound _ 86272 128 Update0168_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 86400 128 Update0168_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
