import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1649_0_checked : (List.range' 844288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1649_1_checked : (List.range' 844416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1649_2_checked : (List.range' 844544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1649_3_checked : (List.range' 844672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1649_range (index : Nat) (lower : 844288 ≤ index) (upper : index < 844800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 844544 then
    if cut : index < 844416 then
      exact segment_sound _ 844288 128 Restriction1649_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 844416 128 Restriction1649_1_checked index (by omega) (by omega)
  else
    if cut : index < 844672 then
      exact segment_sound _ 844544 128 Restriction1649_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 844672 128 Restriction1649_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
