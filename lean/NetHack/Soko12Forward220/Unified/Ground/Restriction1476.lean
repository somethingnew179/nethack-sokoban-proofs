import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1476_0_checked : (List.range' 755712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1476_1_checked : (List.range' 755840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1476_2_checked : (List.range' 755968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1476_3_checked : (List.range' 756096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1476_range (index : Nat) (lower : 755712 ≤ index) (upper : index < 756224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 755968 then
    if cut : index < 755840 then
      exact segment_sound _ 755712 128 Restriction1476_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 755840 128 Restriction1476_1_checked index (by omega) (by omega)
  else
    if cut : index < 756096 then
      exact segment_sound _ 755968 128 Restriction1476_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 756096 128 Restriction1476_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
