import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1816_0_checked : (List.range' 929792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1816_1_checked : (List.range' 929920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1816_2_checked : (List.range' 930048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1816_3_checked : (List.range' 930176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1816_range (index : Nat) (lower : 929792 ≤ index) (upper : index < 930304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 930048 then
    if cut : index < 929920 then
      exact segment_sound _ 929792 128 Restriction1816_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 929920 128 Restriction1816_1_checked index (by omega) (by omega)
  else
    if cut : index < 930176 then
      exact segment_sound _ 930048 128 Restriction1816_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 930176 128 Restriction1816_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
