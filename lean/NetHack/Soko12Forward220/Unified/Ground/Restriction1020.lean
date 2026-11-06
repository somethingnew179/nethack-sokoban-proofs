import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1020_0_checked : (List.range' 522240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1020_1_checked : (List.range' 522368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1020_2_checked : (List.range' 522496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1020_3_checked : (List.range' 522624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1020_range (index : Nat) (lower : 522240 ≤ index) (upper : index < 522752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 522496 then
    if cut : index < 522368 then
      exact segment_sound _ 522240 128 Restriction1020_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 522368 128 Restriction1020_1_checked index (by omega) (by omega)
  else
    if cut : index < 522624 then
      exact segment_sound _ 522496 128 Restriction1020_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 522624 128 Restriction1020_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
