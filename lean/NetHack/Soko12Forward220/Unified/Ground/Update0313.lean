import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0313_0_checked : (List.range' 160256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0313_1_checked : (List.range' 160384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0313_2_checked : (List.range' 160512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0313_3_checked : (List.range' 160640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0313_range (index : Nat) (lower : 160256 ≤ index) (upper : index < 160768) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 160512 then
    if cut : index < 160384 then
      exact segment_sound _ 160256 128 Update0313_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 160384 128 Update0313_1_checked index (by omega) (by omega)
  else
    if cut : index < 160640 then
      exact segment_sound _ 160512 128 Update0313_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 160640 128 Update0313_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
