import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1953_0_checked : (List.range' 999936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1953_1_checked : (List.range' 1000064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1953_2_checked : (List.range' 1000192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1953_3_checked : (List.range' 1000320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1953_range (index : Nat) (lower : 999936 ≤ index) (upper : index < 1000448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1000192 then
    if cut : index < 1000064 then
      exact segment_sound _ 999936 128 Restriction1953_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1000064 128 Restriction1953_1_checked index (by omega) (by omega)
  else
    if cut : index < 1000320 then
      exact segment_sound _ 1000192 128 Restriction1953_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1000320 128 Restriction1953_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
