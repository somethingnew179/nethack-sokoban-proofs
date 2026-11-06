import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0144_0_checked : (List.range' 73728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0144_1_checked : (List.range' 73856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0144_2_checked : (List.range' 73984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0144_3_checked : (List.range' 74112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0144_range (index : Nat) (lower : 73728 ≤ index) (upper : index < 74240) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 73984 then
    if cut : index < 73856 then
      exact segment_sound _ 73728 128 Update0144_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 73856 128 Update0144_1_checked index (by omega) (by omega)
  else
    if cut : index < 74112 then
      exact segment_sound _ 73984 128 Update0144_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 74112 128 Update0144_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
