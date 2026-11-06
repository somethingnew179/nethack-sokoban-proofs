import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0427_0_checked : (List.range' 218624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0427_1_checked : (List.range' 218752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0427_2_checked : (List.range' 218880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0427_3_checked : (List.range' 219008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0427_range (index : Nat) (lower : 218624 ≤ index) (upper : index < 219136) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 218880 then
    if cut : index < 218752 then
      exact segment_sound _ 218624 128 Update0427_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 218752 128 Update0427_1_checked index (by omega) (by omega)
  else
    if cut : index < 219008 then
      exact segment_sound _ 218880 128 Update0427_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 219008 128 Update0427_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
