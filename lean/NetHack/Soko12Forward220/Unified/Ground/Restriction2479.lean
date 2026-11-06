import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2479_0_checked : (List.range' 1269248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2479_1_checked : (List.range' 1269376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2479_2_checked : (List.range' 1269504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2479_3_checked : (List.range' 1269632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2479_range (index : Nat) (lower : 1269248 ≤ index) (upper : index < 1269760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1269504 then
    if cut : index < 1269376 then
      exact segment_sound _ 1269248 128 Restriction2479_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1269376 128 Restriction2479_1_checked index (by omega) (by omega)
  else
    if cut : index < 1269632 then
      exact segment_sound _ 1269504 128 Restriction2479_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1269632 128 Restriction2479_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
