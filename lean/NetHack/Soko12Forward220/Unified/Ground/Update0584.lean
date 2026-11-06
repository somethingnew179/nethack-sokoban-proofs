import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0584_0_checked : (List.range' 299008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0584_1_checked : (List.range' 299136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0584_2_checked : (List.range' 299264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0584_3_checked : (List.range' 299392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0584_range (index : Nat) (lower : 299008 ≤ index) (upper : index < 299520) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 299264 then
    if cut : index < 299136 then
      exact segment_sound _ 299008 128 Update0584_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 299136 128 Update0584_1_checked index (by omega) (by omega)
  else
    if cut : index < 299392 then
      exact segment_sound _ 299264 128 Update0584_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 299392 128 Update0584_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
