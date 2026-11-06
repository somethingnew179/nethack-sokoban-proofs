import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1433_0_checked : (List.range' 733696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1433_1_checked : (List.range' 733824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1433_2_checked : (List.range' 733952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1433_3_checked : (List.range' 734080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1433_range (index : Nat) (lower : 733696 ≤ index) (upper : index < 734208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 733952 then
    if cut : index < 733824 then
      exact segment_sound _ 733696 128 Restriction1433_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 733824 128 Restriction1433_1_checked index (by omega) (by omega)
  else
    if cut : index < 734080 then
      exact segment_sound _ 733952 128 Restriction1433_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 734080 128 Restriction1433_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
