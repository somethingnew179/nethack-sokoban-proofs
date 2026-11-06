import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0150_0_checked : (List.range' 76800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0150_1_checked : (List.range' 76928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0150_2_checked : (List.range' 77056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0150_3_checked : (List.range' 77184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0150_range (index : Nat) (lower : 76800 ≤ index) (upper : index < 77312) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 77056 then
    if cut : index < 76928 then
      exact segment_sound _ 76800 128 Update0150_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 76928 128 Update0150_1_checked index (by omega) (by omega)
  else
    if cut : index < 77184 then
      exact segment_sound _ 77056 128 Update0150_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 77184 128 Update0150_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
