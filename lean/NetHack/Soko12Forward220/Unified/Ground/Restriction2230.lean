import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2230_0_checked : (List.range' 1141760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2230_1_checked : (List.range' 1141888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2230_2_checked : (List.range' 1142016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2230_3_checked : (List.range' 1142144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2230_range (index : Nat) (lower : 1141760 ≤ index) (upper : index < 1142272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1142016 then
    if cut : index < 1141888 then
      exact segment_sound _ 1141760 128 Restriction2230_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1141888 128 Restriction2230_1_checked index (by omega) (by omega)
  else
    if cut : index < 1142144 then
      exact segment_sound _ 1142016 128 Restriction2230_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1142144 128 Restriction2230_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
