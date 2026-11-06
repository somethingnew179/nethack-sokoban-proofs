import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2524_0_checked : (List.range' 1292288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2524_1_checked : (List.range' 1292416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2524_2_checked : (List.range' 1292544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2524_3_checked : (List.range' 1292672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2524_range (index : Nat) (lower : 1292288 ≤ index) (upper : index < 1292800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1292544 then
    if cut : index < 1292416 then
      exact segment_sound _ 1292288 128 Restriction2524_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1292416 128 Restriction2524_1_checked index (by omega) (by omega)
  else
    if cut : index < 1292672 then
      exact segment_sound _ 1292544 128 Restriction2524_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1292672 128 Restriction2524_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
