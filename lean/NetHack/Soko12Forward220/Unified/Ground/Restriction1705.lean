import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1705_0_checked : (List.range' 872960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1705_1_checked : (List.range' 873088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1705_2_checked : (List.range' 873216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1705_3_checked : (List.range' 873344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1705_range (index : Nat) (lower : 872960 ≤ index) (upper : index < 873472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 873216 then
    if cut : index < 873088 then
      exact segment_sound _ 872960 128 Restriction1705_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 873088 128 Restriction1705_1_checked index (by omega) (by omega)
  else
    if cut : index < 873344 then
      exact segment_sound _ 873216 128 Restriction1705_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 873344 128 Restriction1705_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
