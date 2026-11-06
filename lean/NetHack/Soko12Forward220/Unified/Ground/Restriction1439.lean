import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1439_0_checked : (List.range' 736768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1439_1_checked : (List.range' 736896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1439_2_checked : (List.range' 737024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1439_3_checked : (List.range' 737152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1439_range (index : Nat) (lower : 736768 ≤ index) (upper : index < 737280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 737024 then
    if cut : index < 736896 then
      exact segment_sound _ 736768 128 Restriction1439_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 736896 128 Restriction1439_1_checked index (by omega) (by omega)
  else
    if cut : index < 737152 then
      exact segment_sound _ 737024 128 Restriction1439_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 737152 128 Restriction1439_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
