import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1753_0_checked : (List.range' 897536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1753_1_checked : (List.range' 897664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1753_2_checked : (List.range' 897792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1753_3_checked : (List.range' 897920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1753_range (index : Nat) (lower : 897536 ≤ index) (upper : index < 898048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 897792 then
    if cut : index < 897664 then
      exact segment_sound _ 897536 128 Restriction1753_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 897664 128 Restriction1753_1_checked index (by omega) (by omega)
  else
    if cut : index < 897920 then
      exact segment_sound _ 897792 128 Restriction1753_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 897920 128 Restriction1753_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
