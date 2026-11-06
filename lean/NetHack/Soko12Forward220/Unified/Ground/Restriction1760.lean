import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1760_0_checked : (List.range' 901120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1760_1_checked : (List.range' 901248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1760_2_checked : (List.range' 901376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1760_3_checked : (List.range' 901504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1760_range (index : Nat) (lower : 901120 ≤ index) (upper : index < 901632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 901376 then
    if cut : index < 901248 then
      exact segment_sound _ 901120 128 Restriction1760_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 901248 128 Restriction1760_1_checked index (by omega) (by omega)
  else
    if cut : index < 901504 then
      exact segment_sound _ 901376 128 Restriction1760_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 901504 128 Restriction1760_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
