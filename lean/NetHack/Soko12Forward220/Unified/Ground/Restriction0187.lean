import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0187_0_checked : (List.range' 95744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0187_1_checked : (List.range' 95872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0187_2_checked : (List.range' 96000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0187_3_checked : (List.range' 96128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0187_range (index : Nat) (lower : 95744 ≤ index) (upper : index < 96256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 96000 then
    if cut : index < 95872 then
      exact segment_sound _ 95744 128 Restriction0187_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 95872 128 Restriction0187_1_checked index (by omega) (by omega)
  else
    if cut : index < 96128 then
      exact segment_sound _ 96000 128 Restriction0187_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 96128 128 Restriction0187_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
