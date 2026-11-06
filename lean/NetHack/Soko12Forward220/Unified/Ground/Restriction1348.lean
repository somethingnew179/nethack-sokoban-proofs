import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1348_0_checked : (List.range' 690176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1348_1_checked : (List.range' 690304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1348_2_checked : (List.range' 690432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1348_3_checked : (List.range' 690560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1348_range (index : Nat) (lower : 690176 ≤ index) (upper : index < 690688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 690432 then
    if cut : index < 690304 then
      exact segment_sound _ 690176 128 Restriction1348_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 690304 128 Restriction1348_1_checked index (by omega) (by omega)
  else
    if cut : index < 690560 then
      exact segment_sound _ 690432 128 Restriction1348_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 690560 128 Restriction1348_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
