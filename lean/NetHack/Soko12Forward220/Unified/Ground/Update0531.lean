import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0531_0_checked : (List.range' 271872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0531_1_checked : (List.range' 272000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0531_2_checked : (List.range' 272128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0531_3_checked : (List.range' 272256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0531_range (index : Nat) (lower : 271872 ≤ index) (upper : index < 272384) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 272128 then
    if cut : index < 272000 then
      exact segment_sound _ 271872 128 Update0531_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 272000 128 Update0531_1_checked index (by omega) (by omega)
  else
    if cut : index < 272256 then
      exact segment_sound _ 272128 128 Update0531_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 272256 128 Update0531_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
