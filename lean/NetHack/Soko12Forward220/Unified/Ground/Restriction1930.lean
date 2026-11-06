import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1930_0_checked : (List.range' 988160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1930_1_checked : (List.range' 988288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1930_2_checked : (List.range' 988416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1930_3_checked : (List.range' 988544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1930_range (index : Nat) (lower : 988160 ≤ index) (upper : index < 988672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 988416 then
    if cut : index < 988288 then
      exact segment_sound _ 988160 128 Restriction1930_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 988288 128 Restriction1930_1_checked index (by omega) (by omega)
  else
    if cut : index < 988544 then
      exact segment_sound _ 988416 128 Restriction1930_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 988544 128 Restriction1930_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
