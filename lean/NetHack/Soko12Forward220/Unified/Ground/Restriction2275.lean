import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2275_0_checked : (List.range' 1164800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2275_1_checked : (List.range' 1164928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2275_2_checked : (List.range' 1165056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2275_3_checked : (List.range' 1165184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2275_range (index : Nat) (lower : 1164800 ≤ index) (upper : index < 1165312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1165056 then
    if cut : index < 1164928 then
      exact segment_sound _ 1164800 128 Restriction2275_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1164928 128 Restriction2275_1_checked index (by omega) (by omega)
  else
    if cut : index < 1165184 then
      exact segment_sound _ 1165056 128 Restriction2275_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1165184 128 Restriction2275_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
