import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0550_0_checked : (List.range' 281600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0550_1_checked : (List.range' 281728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0550_2_checked : (List.range' 281856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0550_3_checked : (List.range' 281984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0550_range (index : Nat) (lower : 281600 ≤ index) (upper : index < 282112) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 281856 then
    if cut : index < 281728 then
      exact segment_sound _ 281600 128 Update0550_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 281728 128 Update0550_1_checked index (by omega) (by omega)
  else
    if cut : index < 281984 then
      exact segment_sound _ 281856 128 Update0550_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 281984 128 Update0550_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
