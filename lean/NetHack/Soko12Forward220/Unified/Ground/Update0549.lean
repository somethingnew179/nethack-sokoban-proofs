import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0549_0_checked : (List.range' 281088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0549_1_checked : (List.range' 281216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0549_2_checked : (List.range' 281344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0549_3_checked : (List.range' 281472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0549_range (index : Nat) (lower : 281088 ≤ index) (upper : index < 281600) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 281344 then
    if cut : index < 281216 then
      exact segment_sound _ 281088 128 Update0549_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 281216 128 Update0549_1_checked index (by omega) (by omega)
  else
    if cut : index < 281472 then
      exact segment_sound _ 281344 128 Update0549_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 281472 128 Update0549_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
