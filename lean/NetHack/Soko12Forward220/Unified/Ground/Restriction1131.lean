import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1131_0_checked : (List.range' 579072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1131_1_checked : (List.range' 579200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1131_2_checked : (List.range' 579328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1131_3_checked : (List.range' 579456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1131_range (index : Nat) (lower : 579072 ≤ index) (upper : index < 579584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 579328 then
    if cut : index < 579200 then
      exact segment_sound _ 579072 128 Restriction1131_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 579200 128 Restriction1131_1_checked index (by omega) (by omega)
  else
    if cut : index < 579456 then
      exact segment_sound _ 579328 128 Restriction1131_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 579456 128 Restriction1131_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
