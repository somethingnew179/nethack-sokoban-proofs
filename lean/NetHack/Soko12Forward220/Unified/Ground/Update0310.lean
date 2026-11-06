import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0310_0_checked : (List.range' 158720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0310_1_checked : (List.range' 158848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0310_2_checked : (List.range' 158976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0310_3_checked : (List.range' 159104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0310_range (index : Nat) (lower : 158720 ≤ index) (upper : index < 159232) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 158976 then
    if cut : index < 158848 then
      exact segment_sound _ 158720 128 Update0310_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 158848 128 Update0310_1_checked index (by omega) (by omega)
  else
    if cut : index < 159104 then
      exact segment_sound _ 158976 128 Update0310_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 159104 128 Update0310_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
