import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0171_0_checked : (List.range' 87552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0171_1_checked : (List.range' 87680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0171_2_checked : (List.range' 87808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0171_3_checked : (List.range' 87936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0171_range (index : Nat) (lower : 87552 ≤ index) (upper : index < 88064) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 87808 then
    if cut : index < 87680 then
      exact segment_sound _ 87552 128 Update0171_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 87680 128 Update0171_1_checked index (by omega) (by omega)
  else
    if cut : index < 87936 then
      exact segment_sound _ 87808 128 Update0171_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 87936 128 Update0171_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
