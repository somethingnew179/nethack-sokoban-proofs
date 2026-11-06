import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1931_0_checked : (List.range' 988672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1931_1_checked : (List.range' 988800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1931_2_checked : (List.range' 988928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1931_3_checked : (List.range' 989056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1931_range (index : Nat) (lower : 988672 ≤ index) (upper : index < 989184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 988928 then
    if cut : index < 988800 then
      exact segment_sound _ 988672 128 Restriction1931_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 988800 128 Restriction1931_1_checked index (by omega) (by omega)
  else
    if cut : index < 989056 then
      exact segment_sound _ 988928 128 Restriction1931_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 989056 128 Restriction1931_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
