import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1479_0_checked : (List.range' 757248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1479_1_checked : (List.range' 757376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1479_2_checked : (List.range' 757504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1479_3_checked : (List.range' 757632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1479_range (index : Nat) (lower : 757248 ≤ index) (upper : index < 757760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 757504 then
    if cut : index < 757376 then
      exact segment_sound _ 757248 128 Restriction1479_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 757376 128 Restriction1479_1_checked index (by omega) (by omega)
  else
    if cut : index < 757632 then
      exact segment_sound _ 757504 128 Restriction1479_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 757632 128 Restriction1479_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
