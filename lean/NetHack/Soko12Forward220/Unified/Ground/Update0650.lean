import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0650_0_checked : (List.range' 332800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0650_1_checked : (List.range' 332928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0650_2_checked : (List.range' 333056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0650_3_checked : (List.range' 333184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0650_range (index : Nat) (lower : 332800 ≤ index) (upper : index < 333312) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 333056 then
    if cut : index < 332928 then
      exact segment_sound _ 332800 128 Update0650_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 332928 128 Update0650_1_checked index (by omega) (by omega)
  else
    if cut : index < 333184 then
      exact segment_sound _ 333056 128 Update0650_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 333184 128 Update0650_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
