import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1802_0_checked : (List.range' 922624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1802_1_checked : (List.range' 922752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1802_2_checked : (List.range' 922880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1802_3_checked : (List.range' 923008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1802_range (index : Nat) (lower : 922624 ≤ index) (upper : index < 923136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 922880 then
    if cut : index < 922752 then
      exact segment_sound _ 922624 128 Restriction1802_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 922752 128 Restriction1802_1_checked index (by omega) (by omega)
  else
    if cut : index < 923008 then
      exact segment_sound _ 922880 128 Restriction1802_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 923008 128 Restriction1802_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
