import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1478_0_checked : (List.range' 756736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1478_1_checked : (List.range' 756864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1478_2_checked : (List.range' 756992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1478_3_checked : (List.range' 757120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1478_range (index : Nat) (lower : 756736 ≤ index) (upper : index < 757248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 756992 then
    if cut : index < 756864 then
      exact segment_sound _ 756736 128 Restriction1478_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 756864 128 Restriction1478_1_checked index (by omega) (by omega)
  else
    if cut : index < 757120 then
      exact segment_sound _ 756992 128 Restriction1478_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 757120 128 Restriction1478_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
