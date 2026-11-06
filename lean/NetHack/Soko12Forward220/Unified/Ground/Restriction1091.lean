import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1091_0_checked : (List.range' 558592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1091_1_checked : (List.range' 558720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1091_2_checked : (List.range' 558848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1091_3_checked : (List.range' 558976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1091_range (index : Nat) (lower : 558592 ≤ index) (upper : index < 559104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 558848 then
    if cut : index < 558720 then
      exact segment_sound _ 558592 128 Restriction1091_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 558720 128 Restriction1091_1_checked index (by omega) (by omega)
  else
    if cut : index < 558976 then
      exact segment_sound _ 558848 128 Restriction1091_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 558976 128 Restriction1091_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
