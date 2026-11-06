import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1127_0_checked : (List.range' 577024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1127_1_checked : (List.range' 577152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1127_2_checked : (List.range' 577280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1127_3_checked : (List.range' 577408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1127_range (index : Nat) (lower : 577024 ≤ index) (upper : index < 577536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 577280 then
    if cut : index < 577152 then
      exact segment_sound _ 577024 128 Restriction1127_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 577152 128 Restriction1127_1_checked index (by omega) (by omega)
  else
    if cut : index < 577408 then
      exact segment_sound _ 577280 128 Restriction1127_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 577408 128 Restriction1127_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
