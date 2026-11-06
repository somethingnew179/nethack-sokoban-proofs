import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0598_0_checked : (List.range' 306176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0598_1_checked : (List.range' 306304 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0598_2_checked : (List.range' 306432 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0598_3_checked : (List.range' 306560 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0598_range (index : Nat) (lower : 306176 ≤ index) (upper : index < 306688) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 306432 then
    if cut : index < 306304 then
      exact segment_sound _ 306176 128 Update0598_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 306304 128 Update0598_1_checked index (by omega) (by omega)
  else
    if cut : index < 306560 then
      exact segment_sound _ 306432 128 Update0598_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 306560 128 Update0598_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
