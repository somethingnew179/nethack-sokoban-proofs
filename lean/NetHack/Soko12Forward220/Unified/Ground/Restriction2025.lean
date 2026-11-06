import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2025_0_checked : (List.range' 1036800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2025_1_checked : (List.range' 1036928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2025_2_checked : (List.range' 1037056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2025_3_checked : (List.range' 1037184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2025_range (index : Nat) (lower : 1036800 ≤ index) (upper : index < 1037312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1037056 then
    if cut : index < 1036928 then
      exact segment_sound _ 1036800 128 Restriction2025_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1036928 128 Restriction2025_1_checked index (by omega) (by omega)
  else
    if cut : index < 1037184 then
      exact segment_sound _ 1037056 128 Restriction2025_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1037184 128 Restriction2025_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
