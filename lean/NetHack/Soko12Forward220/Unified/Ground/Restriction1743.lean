import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1743_0_checked : (List.range' 892416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1743_1_checked : (List.range' 892544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1743_2_checked : (List.range' 892672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1743_3_checked : (List.range' 892800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1743_range (index : Nat) (lower : 892416 ≤ index) (upper : index < 892928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 892672 then
    if cut : index < 892544 then
      exact segment_sound _ 892416 128 Restriction1743_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 892544 128 Restriction1743_1_checked index (by omega) (by omega)
  else
    if cut : index < 892800 then
      exact segment_sound _ 892672 128 Restriction1743_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 892800 128 Restriction1743_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
