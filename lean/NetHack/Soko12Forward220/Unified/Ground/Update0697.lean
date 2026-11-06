import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0697_0_checked : (List.range' 356864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0697_1_checked : (List.range' 356992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0697_2_checked : (List.range' 357120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0697_3_checked : (List.range' 357248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0697_range (index : Nat) (lower : 356864 ≤ index) (upper : index < 357376) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 357120 then
    if cut : index < 356992 then
      exact segment_sound _ 356864 128 Update0697_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 356992 128 Update0697_1_checked index (by omega) (by omega)
  else
    if cut : index < 357248 then
      exact segment_sound _ 357120 128 Update0697_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 357248 128 Update0697_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
