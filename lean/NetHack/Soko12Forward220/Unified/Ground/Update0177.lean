import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0177_0_checked : (List.range' 90624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0177_1_checked : (List.range' 90752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0177_2_checked : (List.range' 90880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0177_3_checked : (List.range' 91008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0177_range (index : Nat) (lower : 90624 ≤ index) (upper : index < 91136) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 90880 then
    if cut : index < 90752 then
      exact segment_sound _ 90624 128 Update0177_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 90752 128 Update0177_1_checked index (by omega) (by omega)
  else
    if cut : index < 91008 then
      exact segment_sound _ 90880 128 Update0177_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 91008 128 Update0177_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
