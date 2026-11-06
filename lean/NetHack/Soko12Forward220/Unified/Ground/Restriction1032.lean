import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1032_0_checked : (List.range' 528384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1032_1_checked : (List.range' 528512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1032_2_checked : (List.range' 528640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1032_3_checked : (List.range' 528768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1032_range (index : Nat) (lower : 528384 ≤ index) (upper : index < 528896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 528640 then
    if cut : index < 528512 then
      exact segment_sound _ 528384 128 Restriction1032_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 528512 128 Restriction1032_1_checked index (by omega) (by omega)
  else
    if cut : index < 528768 then
      exact segment_sound _ 528640 128 Restriction1032_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 528768 128 Restriction1032_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
