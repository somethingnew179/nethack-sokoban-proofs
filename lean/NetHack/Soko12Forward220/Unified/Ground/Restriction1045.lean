import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1045_0_checked : (List.range' 535040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1045_1_checked : (List.range' 535168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1045_2_checked : (List.range' 535296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1045_3_checked : (List.range' 535424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1045_range (index : Nat) (lower : 535040 ≤ index) (upper : index < 535552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 535296 then
    if cut : index < 535168 then
      exact segment_sound _ 535040 128 Restriction1045_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 535168 128 Restriction1045_1_checked index (by omega) (by omega)
  else
    if cut : index < 535424 then
      exact segment_sound _ 535296 128 Restriction1045_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 535424 128 Restriction1045_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
