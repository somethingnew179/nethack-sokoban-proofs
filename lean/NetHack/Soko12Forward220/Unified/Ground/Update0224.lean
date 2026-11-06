import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0224_0_checked : (List.range' 114688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0224_1_checked : (List.range' 114816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0224_2_checked : (List.range' 114944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0224_3_checked : (List.range' 115072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0224_range (index : Nat) (lower : 114688 ≤ index) (upper : index < 115200) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 114944 then
    if cut : index < 114816 then
      exact segment_sound _ 114688 128 Update0224_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 114816 128 Update0224_1_checked index (by omega) (by omega)
  else
    if cut : index < 115072 then
      exact segment_sound _ 114944 128 Update0224_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 115072 128 Update0224_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
