import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2262_0_checked : (List.range' 1158144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2262_1_checked : (List.range' 1158272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2262_2_checked : (List.range' 1158400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2262_3_checked : (List.range' 1158528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2262_range (index : Nat) (lower : 1158144 ≤ index) (upper : index < 1158656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1158400 then
    if cut : index < 1158272 then
      exact segment_sound _ 1158144 128 Restriction2262_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1158272 128 Restriction2262_1_checked index (by omega) (by omega)
  else
    if cut : index < 1158528 then
      exact segment_sound _ 1158400 128 Restriction2262_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1158528 128 Restriction2262_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
