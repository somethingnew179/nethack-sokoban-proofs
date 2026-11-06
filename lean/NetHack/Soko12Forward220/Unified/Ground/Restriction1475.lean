import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1475_0_checked : (List.range' 755200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1475_1_checked : (List.range' 755328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1475_2_checked : (List.range' 755456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1475_3_checked : (List.range' 755584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1475_range (index : Nat) (lower : 755200 ≤ index) (upper : index < 755712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 755456 then
    if cut : index < 755328 then
      exact segment_sound _ 755200 128 Restriction1475_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 755328 128 Restriction1475_1_checked index (by omega) (by omega)
  else
    if cut : index < 755584 then
      exact segment_sound _ 755456 128 Restriction1475_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 755584 128 Restriction1475_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
