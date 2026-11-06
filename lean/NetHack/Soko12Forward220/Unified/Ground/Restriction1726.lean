import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1726_0_checked : (List.range' 883712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1726_1_checked : (List.range' 883840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1726_2_checked : (List.range' 883968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1726_3_checked : (List.range' 884096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1726_range (index : Nat) (lower : 883712 ≤ index) (upper : index < 884224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 883968 then
    if cut : index < 883840 then
      exact segment_sound _ 883712 128 Restriction1726_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 883840 128 Restriction1726_1_checked index (by omega) (by omega)
  else
    if cut : index < 884096 then
      exact segment_sound _ 883968 128 Restriction1726_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 884096 128 Restriction1726_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
