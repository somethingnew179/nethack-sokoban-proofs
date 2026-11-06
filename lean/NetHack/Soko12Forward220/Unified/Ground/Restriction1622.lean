import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1622_0_checked : (List.range' 830464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1622_1_checked : (List.range' 830592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1622_2_checked : (List.range' 830720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1622_3_checked : (List.range' 830848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1622_range (index : Nat) (lower : 830464 ≤ index) (upper : index < 830976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 830720 then
    if cut : index < 830592 then
      exact segment_sound _ 830464 128 Restriction1622_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 830592 128 Restriction1622_1_checked index (by omega) (by omega)
  else
    if cut : index < 830848 then
      exact segment_sound _ 830720 128 Restriction1622_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 830848 128 Restriction1622_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
