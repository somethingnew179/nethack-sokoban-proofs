import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0512_0_checked : (List.range' 262144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0512_1_checked : (List.range' 262272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0512_2_checked : (List.range' 262400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0512_3_checked : (List.range' 262528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0512_range (index : Nat) (lower : 262144 ≤ index) (upper : index < 262656) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 262400 then
    if cut : index < 262272 then
      exact segment_sound _ 262144 128 Update0512_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 262272 128 Update0512_1_checked index (by omega) (by omega)
  else
    if cut : index < 262528 then
      exact segment_sound _ 262400 128 Update0512_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 262528 128 Update0512_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
