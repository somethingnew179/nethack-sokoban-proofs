import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0202_0_checked : (List.range' 103424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0202_1_checked : (List.range' 103552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0202_2_checked : (List.range' 103680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0202_3_checked : (List.range' 103808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0202_range (index : Nat) (lower : 103424 ≤ index) (upper : index < 103936) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 103680 then
    if cut : index < 103552 then
      exact segment_sound _ 103424 128 Update0202_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 103552 128 Update0202_1_checked index (by omega) (by omega)
  else
    if cut : index < 103808 then
      exact segment_sound _ 103680 128 Update0202_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 103808 128 Update0202_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
