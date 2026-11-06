import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1403_0_checked : (List.range' 718336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1403_1_checked : (List.range' 718464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1403_2_checked : (List.range' 718592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1403_3_checked : (List.range' 718720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1403_range (index : Nat) (lower : 718336 ≤ index) (upper : index < 718848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 718592 then
    if cut : index < 718464 then
      exact segment_sound _ 718336 128 Restriction1403_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 718464 128 Restriction1403_1_checked index (by omega) (by omega)
  else
    if cut : index < 718720 then
      exact segment_sound _ 718592 128 Restriction1403_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 718720 128 Restriction1403_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
