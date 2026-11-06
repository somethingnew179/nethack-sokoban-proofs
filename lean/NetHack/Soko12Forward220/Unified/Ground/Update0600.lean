import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0600_0_checked : (List.range' 307200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0600_1_checked : (List.range' 307328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0600_2_checked : (List.range' 307456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0600_3_checked : (List.range' 307584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0600_range (index : Nat) (lower : 307200 ≤ index) (upper : index < 307712) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 307456 then
    if cut : index < 307328 then
      exact segment_sound _ 307200 128 Update0600_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 307328 128 Update0600_1_checked index (by omega) (by omega)
  else
    if cut : index < 307584 then
      exact segment_sound _ 307456 128 Update0600_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 307584 128 Update0600_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
