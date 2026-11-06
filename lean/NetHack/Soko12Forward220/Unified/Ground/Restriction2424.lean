import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2424_0_checked : (List.range' 1241088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2424_1_checked : (List.range' 1241216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2424_2_checked : (List.range' 1241344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2424_3_checked : (List.range' 1241472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2424_range (index : Nat) (lower : 1241088 ≤ index) (upper : index < 1241600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1241344 then
    if cut : index < 1241216 then
      exact segment_sound _ 1241088 128 Restriction2424_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1241216 128 Restriction2424_1_checked index (by omega) (by omega)
  else
    if cut : index < 1241472 then
      exact segment_sound _ 1241344 128 Restriction2424_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1241472 128 Restriction2424_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
