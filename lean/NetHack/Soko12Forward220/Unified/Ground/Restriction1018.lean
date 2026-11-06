import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1018_0_checked : (List.range' 521216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1018_1_checked : (List.range' 521344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1018_2_checked : (List.range' 521472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1018_3_checked : (List.range' 521600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1018_range (index : Nat) (lower : 521216 ≤ index) (upper : index < 521728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 521472 then
    if cut : index < 521344 then
      exact segment_sound _ 521216 128 Restriction1018_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 521344 128 Restriction1018_1_checked index (by omega) (by omega)
  else
    if cut : index < 521600 then
      exact segment_sound _ 521472 128 Restriction1018_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 521600 128 Restriction1018_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
