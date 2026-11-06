import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0482_0_checked : (List.range' 246784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0482_1_checked : (List.range' 246912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0482_2_checked : (List.range' 247040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0482_3_checked : (List.range' 247168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0482_range (index : Nat) (lower : 246784 ≤ index) (upper : index < 247296) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 247040 then
    if cut : index < 246912 then
      exact segment_sound _ 246784 128 Update0482_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 246912 128 Update0482_1_checked index (by omega) (by omega)
  else
    if cut : index < 247168 then
      exact segment_sound _ 247040 128 Update0482_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 247168 128 Update0482_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
