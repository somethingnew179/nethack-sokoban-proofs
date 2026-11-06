import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1625_0_checked : (List.range' 832000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1625_1_checked : (List.range' 832128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1625_2_checked : (List.range' 832256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1625_3_checked : (List.range' 832384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1625_range (index : Nat) (lower : 832000 ≤ index) (upper : index < 832512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 832256 then
    if cut : index < 832128 then
      exact segment_sound _ 832000 128 Restriction1625_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 832128 128 Restriction1625_1_checked index (by omega) (by omega)
  else
    if cut : index < 832384 then
      exact segment_sound _ 832256 128 Restriction1625_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 832384 128 Restriction1625_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
