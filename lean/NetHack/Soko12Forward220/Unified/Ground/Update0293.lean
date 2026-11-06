import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0293_0_checked : (List.range' 150016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0293_1_checked : (List.range' 150144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0293_2_checked : (List.range' 150272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0293_3_checked : (List.range' 150400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0293_range (index : Nat) (lower : 150016 ≤ index) (upper : index < 150528) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 150272 then
    if cut : index < 150144 then
      exact segment_sound _ 150016 128 Update0293_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 150144 128 Update0293_1_checked index (by omega) (by omega)
  else
    if cut : index < 150400 then
      exact segment_sound _ 150272 128 Update0293_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 150400 128 Update0293_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
