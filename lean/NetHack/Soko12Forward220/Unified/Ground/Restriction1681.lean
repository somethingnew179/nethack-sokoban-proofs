import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1681_0_checked : (List.range' 860672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1681_1_checked : (List.range' 860800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1681_2_checked : (List.range' 860928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1681_3_checked : (List.range' 861056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1681_range (index : Nat) (lower : 860672 ≤ index) (upper : index < 861184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 860928 then
    if cut : index < 860800 then
      exact segment_sound _ 860672 128 Restriction1681_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 860800 128 Restriction1681_1_checked index (by omega) (by omega)
  else
    if cut : index < 861056 then
      exact segment_sound _ 860928 128 Restriction1681_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 861056 128 Restriction1681_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
