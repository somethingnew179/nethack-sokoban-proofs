import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0046_0_checked : (List.range' 23552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0046_1_checked : (List.range' 23680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0046_2_checked : (List.range' 23808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0046_3_checked : (List.range' 23936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0046_range (index : Nat) (lower : 23552 ≤ index) (upper : index < 24064) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 23808 then
    if cut : index < 23680 then
      exact segment_sound _ 23552 128 Update0046_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 23680 128 Update0046_1_checked index (by omega) (by omega)
  else
    if cut : index < 23936 then
      exact segment_sound _ 23808 128 Update0046_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 23936 128 Update0046_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
