import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0179_0_checked : (List.range' 91648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0179_1_checked : (List.range' 91776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0179_2_checked : (List.range' 91904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0179_3_checked : (List.range' 92032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0179_range (index : Nat) (lower : 91648 ≤ index) (upper : index < 92160) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 91904 then
    if cut : index < 91776 then
      exact segment_sound _ 91648 128 Update0179_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 91776 128 Update0179_1_checked index (by omega) (by omega)
  else
    if cut : index < 92032 then
      exact segment_sound _ 91904 128 Update0179_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 92032 128 Update0179_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
