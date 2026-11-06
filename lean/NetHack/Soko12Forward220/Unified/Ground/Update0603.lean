import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0603_0_checked : (List.range' 308736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0603_1_checked : (List.range' 308864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0603_2_checked : (List.range' 308992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0603_3_checked : (List.range' 309120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0603_range (index : Nat) (lower : 308736 ≤ index) (upper : index < 309248) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 308992 then
    if cut : index < 308864 then
      exact segment_sound _ 308736 128 Update0603_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 308864 128 Update0603_1_checked index (by omega) (by omega)
  else
    if cut : index < 309120 then
      exact segment_sound _ 308992 128 Update0603_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 309120 128 Update0603_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
