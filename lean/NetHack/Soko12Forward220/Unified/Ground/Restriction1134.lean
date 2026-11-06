import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1134_0_checked : (List.range' 580608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1134_1_checked : (List.range' 580736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1134_2_checked : (List.range' 580864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1134_3_checked : (List.range' 580992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1134_range (index : Nat) (lower : 580608 ≤ index) (upper : index < 581120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 580864 then
    if cut : index < 580736 then
      exact segment_sound _ 580608 128 Restriction1134_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 580736 128 Restriction1134_1_checked index (by omega) (by omega)
  else
    if cut : index < 580992 then
      exact segment_sound _ 580864 128 Restriction1134_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 580992 128 Restriction1134_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
