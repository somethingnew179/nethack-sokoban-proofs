import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2464_0_checked : (List.range' 1261568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2464_1_checked : (List.range' 1261696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2464_2_checked : (List.range' 1261824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2464_3_checked : (List.range' 1261952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2464_range (index : Nat) (lower : 1261568 ≤ index) (upper : index < 1262080) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1261824 then
    if cut : index < 1261696 then
      exact segment_sound _ 1261568 128 Restriction2464_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1261696 128 Restriction2464_1_checked index (by omega) (by omega)
  else
    if cut : index < 1261952 then
      exact segment_sound _ 1261824 128 Restriction2464_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1261952 128 Restriction2464_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
