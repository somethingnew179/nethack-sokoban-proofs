import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0412_0_checked : (List.range' 210944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0412_1_checked : (List.range' 211072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0412_2_checked : (List.range' 211200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0412_3_checked : (List.range' 211328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0412_range (index : Nat) (lower : 210944 ≤ index) (upper : index < 211456) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 211200 then
    if cut : index < 211072 then
      exact segment_sound _ 210944 128 Update0412_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 211072 128 Update0412_1_checked index (by omega) (by omega)
  else
    if cut : index < 211328 then
      exact segment_sound _ 211200 128 Update0412_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 211328 128 Update0412_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
