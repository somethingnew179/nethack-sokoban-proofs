import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1486_0_checked : (List.range' 760832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1486_1_checked : (List.range' 760960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1486_2_checked : (List.range' 761088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1486_3_checked : (List.range' 761216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1486_range (index : Nat) (lower : 760832 ≤ index) (upper : index < 761344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 761088 then
    if cut : index < 760960 then
      exact segment_sound _ 760832 128 Restriction1486_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 760960 128 Restriction1486_1_checked index (by omega) (by omega)
  else
    if cut : index < 761216 then
      exact segment_sound _ 761088 128 Restriction1486_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 761216 128 Restriction1486_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
