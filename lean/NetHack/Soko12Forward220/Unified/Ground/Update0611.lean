import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0611_0_checked : (List.range' 312832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0611_1_checked : (List.range' 312960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0611_2_checked : (List.range' 313088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0611_3_checked : (List.range' 313216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0611_range (index : Nat) (lower : 312832 ≤ index) (upper : index < 313344) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 313088 then
    if cut : index < 312960 then
      exact segment_sound _ 312832 128 Update0611_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 312960 128 Update0611_1_checked index (by omega) (by omega)
  else
    if cut : index < 313216 then
      exact segment_sound _ 313088 128 Update0611_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 313216 128 Update0611_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
