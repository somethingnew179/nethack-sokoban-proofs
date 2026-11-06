import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1101_0_checked : (List.range' 563712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1101_1_checked : (List.range' 563840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1101_2_checked : (List.range' 563968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1101_3_checked : (List.range' 564096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1101_range (index : Nat) (lower : 563712 ≤ index) (upper : index < 564224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 563968 then
    if cut : index < 563840 then
      exact segment_sound _ 563712 128 Restriction1101_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 563840 128 Restriction1101_1_checked index (by omega) (by omega)
  else
    if cut : index < 564096 then
      exact segment_sound _ 563968 128 Restriction1101_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 564096 128 Restriction1101_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
