import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1569_0_checked : (List.range' 803328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1569_1_checked : (List.range' 803456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1569_2_checked : (List.range' 803584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1569_3_checked : (List.range' 803712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1569_range (index : Nat) (lower : 803328 ≤ index) (upper : index < 803840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 803584 then
    if cut : index < 803456 then
      exact segment_sound _ 803328 128 Restriction1569_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 803456 128 Restriction1569_1_checked index (by omega) (by omega)
  else
    if cut : index < 803712 then
      exact segment_sound _ 803584 128 Restriction1569_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 803712 128 Restriction1569_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
