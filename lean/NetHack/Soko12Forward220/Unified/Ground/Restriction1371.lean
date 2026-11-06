import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1371_0_checked : (List.range' 701952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1371_1_checked : (List.range' 702080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1371_2_checked : (List.range' 702208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1371_3_checked : (List.range' 702336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1371_range (index : Nat) (lower : 701952 ≤ index) (upper : index < 702464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 702208 then
    if cut : index < 702080 then
      exact segment_sound _ 701952 128 Restriction1371_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 702080 128 Restriction1371_1_checked index (by omega) (by omega)
  else
    if cut : index < 702336 then
      exact segment_sound _ 702208 128 Restriction1371_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 702336 128 Restriction1371_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
