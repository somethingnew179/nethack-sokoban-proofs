import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1170_0_checked : (List.range' 599040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1170_1_checked : (List.range' 599168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1170_2_checked : (List.range' 599296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1170_3_checked : (List.range' 599424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1170_range (index : Nat) (lower : 599040 ≤ index) (upper : index < 599552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 599296 then
    if cut : index < 599168 then
      exact segment_sound _ 599040 128 Restriction1170_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 599168 128 Restriction1170_1_checked index (by omega) (by omega)
  else
    if cut : index < 599424 then
      exact segment_sound _ 599296 128 Restriction1170_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 599424 128 Restriction1170_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
