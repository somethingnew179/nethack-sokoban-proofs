import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1160_0_checked : (List.range' 593920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1160_1_checked : (List.range' 594048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1160_2_checked : (List.range' 594176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1160_3_checked : (List.range' 594304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1160_range (index : Nat) (lower : 593920 ≤ index) (upper : index < 594432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 594176 then
    if cut : index < 594048 then
      exact segment_sound _ 593920 128 Restriction1160_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 594048 128 Restriction1160_1_checked index (by omega) (by omega)
  else
    if cut : index < 594304 then
      exact segment_sound _ 594176 128 Restriction1160_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 594304 128 Restriction1160_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
