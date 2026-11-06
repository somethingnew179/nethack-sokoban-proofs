import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0296_0_checked : (List.range' 151552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0296_1_checked : (List.range' 151680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0296_2_checked : (List.range' 151808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0296_3_checked : (List.range' 151936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0296_range (index : Nat) (lower : 151552 ≤ index) (upper : index < 152064) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 151808 then
    if cut : index < 151680 then
      exact segment_sound _ 151552 128 Update0296_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 151680 128 Update0296_1_checked index (by omega) (by omega)
  else
    if cut : index < 151936 then
      exact segment_sound _ 151808 128 Update0296_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 151936 128 Update0296_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
