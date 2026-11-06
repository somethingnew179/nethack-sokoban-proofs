import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1881_0_checked : (List.range' 963072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1881_1_checked : (List.range' 963200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1881_2_checked : (List.range' 963328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1881_3_checked : (List.range' 963456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1881_range (index : Nat) (lower : 963072 ≤ index) (upper : index < 963584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 963328 then
    if cut : index < 963200 then
      exact segment_sound _ 963072 128 Restriction1881_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 963200 128 Restriction1881_1_checked index (by omega) (by omega)
  else
    if cut : index < 963456 then
      exact segment_sound _ 963328 128 Restriction1881_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 963456 128 Restriction1881_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
