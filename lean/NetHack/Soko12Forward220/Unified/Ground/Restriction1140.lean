import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1140_0_checked : (List.range' 583680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1140_1_checked : (List.range' 583808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1140_2_checked : (List.range' 583936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1140_3_checked : (List.range' 584064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1140_range (index : Nat) (lower : 583680 ≤ index) (upper : index < 584192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 583936 then
    if cut : index < 583808 then
      exact segment_sound _ 583680 128 Restriction1140_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 583808 128 Restriction1140_1_checked index (by omega) (by omega)
  else
    if cut : index < 584064 then
      exact segment_sound _ 583936 128 Restriction1140_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 584064 128 Restriction1140_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
