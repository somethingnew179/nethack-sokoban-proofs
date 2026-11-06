import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0435_0_checked : (List.range' 222720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0435_1_checked : (List.range' 222848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0435_2_checked : (List.range' 222976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0435_3_checked : (List.range' 223104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0435_range (index : Nat) (lower : 222720 ≤ index) (upper : index < 223232) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 222976 then
    if cut : index < 222848 then
      exact segment_sound _ 222720 128 Update0435_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 222848 128 Update0435_1_checked index (by omega) (by omega)
  else
    if cut : index < 223104 then
      exact segment_sound _ 222976 128 Update0435_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 223104 128 Update0435_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
