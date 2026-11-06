import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0521_0_checked : (List.range' 266752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0521_1_checked : (List.range' 266880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0521_2_checked : (List.range' 267008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0521_3_checked : (List.range' 267136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0521_range (index : Nat) (lower : 266752 ≤ index) (upper : index < 267264) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 267008 then
    if cut : index < 266880 then
      exact segment_sound _ 266752 128 Update0521_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 266880 128 Update0521_1_checked index (by omega) (by omega)
  else
    if cut : index < 267136 then
      exact segment_sound _ 267008 128 Update0521_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 267136 128 Update0521_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
