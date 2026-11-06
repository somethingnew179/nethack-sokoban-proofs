import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2166_0_checked : (List.range' 1108992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2166_1_checked : (List.range' 1109120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2166_2_checked : (List.range' 1109248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2166_3_checked : (List.range' 1109376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2166_range (index : Nat) (lower : 1108992 ≤ index) (upper : index < 1109504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1109248 then
    if cut : index < 1109120 then
      exact segment_sound _ 1108992 128 Restriction2166_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1109120 128 Restriction2166_1_checked index (by omega) (by omega)
  else
    if cut : index < 1109376 then
      exact segment_sound _ 1109248 128 Restriction2166_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1109376 128 Restriction2166_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
