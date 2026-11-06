import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1646_0_checked : (List.range' 842752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1646_1_checked : (List.range' 842880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1646_2_checked : (List.range' 843008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1646_3_checked : (List.range' 843136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1646_range (index : Nat) (lower : 842752 ≤ index) (upper : index < 843264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 843008 then
    if cut : index < 842880 then
      exact segment_sound _ 842752 128 Restriction1646_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 842880 128 Restriction1646_1_checked index (by omega) (by omega)
  else
    if cut : index < 843136 then
      exact segment_sound _ 843008 128 Restriction1646_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 843136 128 Restriction1646_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
