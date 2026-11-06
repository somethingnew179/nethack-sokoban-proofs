import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2245_0_checked : (List.range' 1149440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2245_1_checked : (List.range' 1149568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2245_2_checked : (List.range' 1149696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2245_3_checked : (List.range' 1149824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2245_range (index : Nat) (lower : 1149440 ≤ index) (upper : index < 1149952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1149696 then
    if cut : index < 1149568 then
      exact segment_sound _ 1149440 128 Restriction2245_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1149568 128 Restriction2245_1_checked index (by omega) (by omega)
  else
    if cut : index < 1149824 then
      exact segment_sound _ 1149696 128 Restriction2245_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1149824 128 Restriction2245_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
