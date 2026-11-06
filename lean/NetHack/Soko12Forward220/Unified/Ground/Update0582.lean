import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0582_0_checked : (List.range' 297984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0582_1_checked : (List.range' 298112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0582_2_checked : (List.range' 298240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0582_3_checked : (List.range' 298368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0582_range (index : Nat) (lower : 297984 ≤ index) (upper : index < 298496) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 298240 then
    if cut : index < 298112 then
      exact segment_sound _ 297984 128 Update0582_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 298112 128 Update0582_1_checked index (by omega) (by omega)
  else
    if cut : index < 298368 then
      exact segment_sound _ 298240 128 Update0582_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 298368 128 Update0582_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
