import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1386_0_checked : (List.range' 709632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1386_1_checked : (List.range' 709760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1386_2_checked : (List.range' 709888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1386_3_checked : (List.range' 710016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1386_range (index : Nat) (lower : 709632 ≤ index) (upper : index < 710144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 709888 then
    if cut : index < 709760 then
      exact segment_sound _ 709632 128 Restriction1386_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 709760 128 Restriction1386_1_checked index (by omega) (by omega)
  else
    if cut : index < 710016 then
      exact segment_sound _ 709888 128 Restriction1386_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 710016 128 Restriction1386_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
