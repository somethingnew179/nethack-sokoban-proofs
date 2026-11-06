import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1585_0_checked : (List.range' 811520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1585_1_checked : (List.range' 811648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1585_2_checked : (List.range' 811776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1585_3_checked : (List.range' 811904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1585_range (index : Nat) (lower : 811520 ≤ index) (upper : index < 812032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 811776 then
    if cut : index < 811648 then
      exact segment_sound _ 811520 128 Restriction1585_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 811648 128 Restriction1585_1_checked index (by omega) (by omega)
  else
    if cut : index < 811904 then
      exact segment_sound _ 811776 128 Restriction1585_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 811904 128 Restriction1585_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
