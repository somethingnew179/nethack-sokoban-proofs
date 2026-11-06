import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1775_0_checked : (List.range' 908800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1775_1_checked : (List.range' 908928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1775_2_checked : (List.range' 909056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1775_3_checked : (List.range' 909184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1775_range (index : Nat) (lower : 908800 ≤ index) (upper : index < 909312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 909056 then
    if cut : index < 908928 then
      exact segment_sound _ 908800 128 Restriction1775_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 908928 128 Restriction1775_1_checked index (by omega) (by omega)
  else
    if cut : index < 909184 then
      exact segment_sound _ 909056 128 Restriction1775_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 909184 128 Restriction1775_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
