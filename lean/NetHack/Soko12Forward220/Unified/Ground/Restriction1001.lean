import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1001_0_checked : (List.range' 512512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1001_1_checked : (List.range' 512640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1001_2_checked : (List.range' 512768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1001_3_checked : (List.range' 512896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1001_range (index : Nat) (lower : 512512 ≤ index) (upper : index < 513024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 512768 then
    if cut : index < 512640 then
      exact segment_sound _ 512512 128 Restriction1001_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 512640 128 Restriction1001_1_checked index (by omega) (by omega)
  else
    if cut : index < 512896 then
      exact segment_sound _ 512768 128 Restriction1001_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 512896 128 Restriction1001_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
