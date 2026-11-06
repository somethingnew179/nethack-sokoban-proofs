import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1373_0_checked : (List.range' 702976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1373_1_checked : (List.range' 703104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1373_2_checked : (List.range' 703232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1373_3_checked : (List.range' 703360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1373_range (index : Nat) (lower : 702976 ≤ index) (upper : index < 703488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 703232 then
    if cut : index < 703104 then
      exact segment_sound _ 702976 128 Restriction1373_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 703104 128 Restriction1373_1_checked index (by omega) (by omega)
  else
    if cut : index < 703360 then
      exact segment_sound _ 703232 128 Restriction1373_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 703360 128 Restriction1373_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
