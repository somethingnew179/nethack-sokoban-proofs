import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1490_0_checked : (List.range' 762880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1490_1_checked : (List.range' 763008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1490_2_checked : (List.range' 763136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1490_3_checked : (List.range' 763264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1490_range (index : Nat) (lower : 762880 ≤ index) (upper : index < 763392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 763136 then
    if cut : index < 763008 then
      exact segment_sound _ 762880 128 Restriction1490_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 763008 128 Restriction1490_1_checked index (by omega) (by omega)
  else
    if cut : index < 763264 then
      exact segment_sound _ 763136 128 Restriction1490_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 763264 128 Restriction1490_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
