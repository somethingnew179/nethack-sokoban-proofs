import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0583_0_checked : (List.range' 298496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0583_1_checked : (List.range' 298624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0583_2_checked : (List.range' 298752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0583_3_checked : (List.range' 298880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0583_range (index : Nat) (lower : 298496 ≤ index) (upper : index < 299008) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 298752 then
    if cut : index < 298624 then
      exact segment_sound _ 298496 128 Update0583_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 298624 128 Update0583_1_checked index (by omega) (by omega)
  else
    if cut : index < 298880 then
      exact segment_sound _ 298752 128 Update0583_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 298880 128 Update0583_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
