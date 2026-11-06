import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0017_0_checked : (List.range' 8704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0017_1_checked : (List.range' 8832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0017_2_checked : (List.range' 8960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0017_3_checked : (List.range' 9088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0017_range (index : Nat) (lower : 8704 ≤ index) (upper : index < 9216) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 8960 then
    if cut : index < 8832 then
      exact segment_sound _ 8704 128 Update0017_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 8832 128 Update0017_1_checked index (by omega) (by omega)
  else
    if cut : index < 9088 then
      exact segment_sound _ 8960 128 Update0017_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 9088 128 Update0017_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
