import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0349_0_checked : (List.range' 178688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0349_1_checked : (List.range' 178816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0349_2_checked : (List.range' 178944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0349_3_checked : (List.range' 179072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0349_range (index : Nat) (lower : 178688 ≤ index) (upper : index < 179200) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 178944 then
    if cut : index < 178816 then
      exact segment_sound _ 178688 128 Update0349_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 178816 128 Update0349_1_checked index (by omega) (by omega)
  else
    if cut : index < 179072 then
      exact segment_sound _ 178944 128 Update0349_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 179072 128 Update0349_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
