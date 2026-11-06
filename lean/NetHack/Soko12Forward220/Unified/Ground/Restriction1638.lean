import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1638_0_checked : (List.range' 838656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1638_1_checked : (List.range' 838784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1638_2_checked : (List.range' 838912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1638_3_checked : (List.range' 839040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1638_range (index : Nat) (lower : 838656 ≤ index) (upper : index < 839168) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 838912 then
    if cut : index < 838784 then
      exact segment_sound _ 838656 128 Restriction1638_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 838784 128 Restriction1638_1_checked index (by omega) (by omega)
  else
    if cut : index < 839040 then
      exact segment_sound _ 838912 128 Restriction1638_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 839040 128 Restriction1638_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
