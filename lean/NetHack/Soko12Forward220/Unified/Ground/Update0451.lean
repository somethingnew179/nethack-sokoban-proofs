import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0451_0_checked : (List.range' 230912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0451_1_checked : (List.range' 231040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0451_2_checked : (List.range' 231168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0451_3_checked : (List.range' 231296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0451_range (index : Nat) (lower : 230912 ≤ index) (upper : index < 231424) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 231168 then
    if cut : index < 231040 then
      exact segment_sound _ 230912 128 Update0451_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 231040 128 Update0451_1_checked index (by omega) (by omega)
  else
    if cut : index < 231296 then
      exact segment_sound _ 231168 128 Update0451_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 231296 128 Update0451_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
