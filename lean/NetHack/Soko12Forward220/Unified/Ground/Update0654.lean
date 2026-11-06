import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0654_0_checked : (List.range' 334848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0654_1_checked : (List.range' 334976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0654_2_checked : (List.range' 335104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0654_3_checked : (List.range' 335232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0654_range (index : Nat) (lower : 334848 ≤ index) (upper : index < 335360) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 335104 then
    if cut : index < 334976 then
      exact segment_sound _ 334848 128 Update0654_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 334976 128 Update0654_1_checked index (by omega) (by omega)
  else
    if cut : index < 335232 then
      exact segment_sound _ 335104 128 Update0654_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 335232 128 Update0654_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
