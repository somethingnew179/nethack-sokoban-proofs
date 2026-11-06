import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0363_0_checked : (List.range' 185856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0363_1_checked : (List.range' 185984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0363_2_checked : (List.range' 186112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0363_3_checked : (List.range' 186240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0363_range (index : Nat) (lower : 185856 ≤ index) (upper : index < 186368) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 186112 then
    if cut : index < 185984 then
      exact segment_sound _ 185856 128 Update0363_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 185984 128 Update0363_1_checked index (by omega) (by omega)
  else
    if cut : index < 186240 then
      exact segment_sound _ 186112 128 Update0363_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 186240 128 Update0363_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
