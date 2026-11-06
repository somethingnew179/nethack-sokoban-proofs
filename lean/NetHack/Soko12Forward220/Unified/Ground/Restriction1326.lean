import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1326_0_checked : (List.range' 678912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1326_1_checked : (List.range' 679040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1326_2_checked : (List.range' 679168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1326_3_checked : (List.range' 679296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1326_range (index : Nat) (lower : 678912 ≤ index) (upper : index < 679424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 679168 then
    if cut : index < 679040 then
      exact segment_sound _ 678912 128 Restriction1326_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 679040 128 Restriction1326_1_checked index (by omega) (by omega)
  else
    if cut : index < 679296 then
      exact segment_sound _ 679168 128 Restriction1326_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 679296 128 Restriction1326_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
