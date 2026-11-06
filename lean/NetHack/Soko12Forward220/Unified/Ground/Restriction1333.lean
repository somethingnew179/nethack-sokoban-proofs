import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1333_0_checked : (List.range' 682496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1333_1_checked : (List.range' 682624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1333_2_checked : (List.range' 682752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1333_3_checked : (List.range' 682880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1333_range (index : Nat) (lower : 682496 ≤ index) (upper : index < 683008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 682752 then
    if cut : index < 682624 then
      exact segment_sound _ 682496 128 Restriction1333_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 682624 128 Restriction1333_1_checked index (by omega) (by omega)
  else
    if cut : index < 682880 then
      exact segment_sound _ 682752 128 Restriction1333_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 682880 128 Restriction1333_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
