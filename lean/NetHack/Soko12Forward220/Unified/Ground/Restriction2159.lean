import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2159_0_checked : (List.range' 1105408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2159_1_checked : (List.range' 1105536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2159_2_checked : (List.range' 1105664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2159_3_checked : (List.range' 1105792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2159_range (index : Nat) (lower : 1105408 ≤ index) (upper : index < 1105920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1105664 then
    if cut : index < 1105536 then
      exact segment_sound _ 1105408 128 Restriction2159_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1105536 128 Restriction2159_1_checked index (by omega) (by omega)
  else
    if cut : index < 1105792 then
      exact segment_sound _ 1105664 128 Restriction2159_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1105792 128 Restriction2159_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
