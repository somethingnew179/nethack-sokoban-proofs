import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2486_0_checked : (List.range' 1272832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2486_1_checked : (List.range' 1272960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2486_2_checked : (List.range' 1273088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2486_3_checked : (List.range' 1273216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2486_range (index : Nat) (lower : 1272832 ≤ index) (upper : index < 1273344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1273088 then
    if cut : index < 1272960 then
      exact segment_sound _ 1272832 128 Restriction2486_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1272960 128 Restriction2486_1_checked index (by omega) (by omega)
  else
    if cut : index < 1273216 then
      exact segment_sound _ 1273088 128 Restriction2486_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1273216 128 Restriction2486_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
