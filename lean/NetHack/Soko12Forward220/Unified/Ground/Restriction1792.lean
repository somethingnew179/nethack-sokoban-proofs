import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1792_0_checked : (List.range' 917504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1792_1_checked : (List.range' 917632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1792_2_checked : (List.range' 917760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1792_3_checked : (List.range' 917888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1792_range (index : Nat) (lower : 917504 ≤ index) (upper : index < 918016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 917760 then
    if cut : index < 917632 then
      exact segment_sound _ 917504 128 Restriction1792_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 917632 128 Restriction1792_1_checked index (by omega) (by omega)
  else
    if cut : index < 917888 then
      exact segment_sound _ 917760 128 Restriction1792_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 917888 128 Restriction1792_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
