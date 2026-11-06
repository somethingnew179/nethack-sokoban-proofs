import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1538_0_checked : (List.range' 787456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1538_1_checked : (List.range' 787584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1538_2_checked : (List.range' 787712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1538_3_checked : (List.range' 787840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1538_range (index : Nat) (lower : 787456 ≤ index) (upper : index < 787968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 787712 then
    if cut : index < 787584 then
      exact segment_sound _ 787456 128 Restriction1538_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 787584 128 Restriction1538_1_checked index (by omega) (by omega)
  else
    if cut : index < 787840 then
      exact segment_sound _ 787712 128 Restriction1538_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 787840 128 Restriction1538_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
