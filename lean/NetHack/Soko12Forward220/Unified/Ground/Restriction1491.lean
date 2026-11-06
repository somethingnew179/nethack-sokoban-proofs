import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1491_0_checked : (List.range' 763392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1491_1_checked : (List.range' 763520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1491_2_checked : (List.range' 763648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1491_3_checked : (List.range' 763776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1491_range (index : Nat) (lower : 763392 ≤ index) (upper : index < 763904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 763648 then
    if cut : index < 763520 then
      exact segment_sound _ 763392 128 Restriction1491_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 763520 128 Restriction1491_1_checked index (by omega) (by omega)
  else
    if cut : index < 763776 then
      exact segment_sound _ 763648 128 Restriction1491_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 763776 128 Restriction1491_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
