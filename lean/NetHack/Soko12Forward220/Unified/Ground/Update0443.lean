import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0443_0_checked : (List.range' 226816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0443_1_checked : (List.range' 226944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0443_2_checked : (List.range' 227072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0443_3_checked : (List.range' 227200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0443_range (index : Nat) (lower : 226816 ≤ index) (upper : index < 227328) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 227072 then
    if cut : index < 226944 then
      exact segment_sound _ 226816 128 Update0443_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 226944 128 Update0443_1_checked index (by omega) (by omega)
  else
    if cut : index < 227200 then
      exact segment_sound _ 227072 128 Update0443_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 227200 128 Update0443_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
