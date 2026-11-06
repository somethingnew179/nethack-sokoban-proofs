import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2495_0_checked : (List.range' 1277440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2495_1_checked : (List.range' 1277568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2495_2_checked : (List.range' 1277696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2495_3_checked : (List.range' 1277824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2495_range (index : Nat) (lower : 1277440 ≤ index) (upper : index < 1277952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1277696 then
    if cut : index < 1277568 then
      exact segment_sound _ 1277440 128 Restriction2495_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1277568 128 Restriction2495_1_checked index (by omega) (by omega)
  else
    if cut : index < 1277824 then
      exact segment_sound _ 1277696 128 Restriction2495_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1277824 128 Restriction2495_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
