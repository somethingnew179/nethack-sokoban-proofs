import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1720_0_checked : (List.range' 880640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1720_1_checked : (List.range' 880768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1720_2_checked : (List.range' 880896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1720_3_checked : (List.range' 881024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1720_range (index : Nat) (lower : 880640 ≤ index) (upper : index < 881152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 880896 then
    if cut : index < 880768 then
      exact segment_sound _ 880640 128 Restriction1720_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 880768 128 Restriction1720_1_checked index (by omega) (by omega)
  else
    if cut : index < 881024 then
      exact segment_sound _ 880896 128 Restriction1720_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 881024 128 Restriction1720_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
