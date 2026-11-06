import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1324_0_checked : (List.range' 677888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1324_1_checked : (List.range' 678016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1324_2_checked : (List.range' 678144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1324_3_checked : (List.range' 678272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1324_range (index : Nat) (lower : 677888 ≤ index) (upper : index < 678400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 678144 then
    if cut : index < 678016 then
      exact segment_sound _ 677888 128 Restriction1324_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 678016 128 Restriction1324_1_checked index (by omega) (by omega)
  else
    if cut : index < 678272 then
      exact segment_sound _ 678144 128 Restriction1324_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 678272 128 Restriction1324_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
