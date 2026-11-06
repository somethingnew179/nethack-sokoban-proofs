import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2092_0_checked : (List.range' 1071104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2092_1_checked : (List.range' 1071232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2092_2_checked : (List.range' 1071360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2092_3_checked : (List.range' 1071488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2092_range (index : Nat) (lower : 1071104 ≤ index) (upper : index < 1071616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1071360 then
    if cut : index < 1071232 then
      exact segment_sound _ 1071104 128 Restriction2092_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1071232 128 Restriction2092_1_checked index (by omega) (by omega)
  else
    if cut : index < 1071488 then
      exact segment_sound _ 1071360 128 Restriction2092_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1071488 128 Restriction2092_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
