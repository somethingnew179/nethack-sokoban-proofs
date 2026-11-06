import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0178_0_checked : (List.range' 91136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0178_1_checked : (List.range' 91264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0178_2_checked : (List.range' 91392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0178_3_checked : (List.range' 91520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0178_range (index : Nat) (lower : 91136 ≤ index) (upper : index < 91648) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 91392 then
    if cut : index < 91264 then
      exact segment_sound _ 91136 128 Update0178_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 91264 128 Update0178_1_checked index (by omega) (by omega)
  else
    if cut : index < 91520 then
      exact segment_sound _ 91392 128 Update0178_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 91520 128 Update0178_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
