import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2415_0_checked : (List.range' 1236480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2415_1_checked : (List.range' 1236608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2415_2_checked : (List.range' 1236736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2415_3_checked : (List.range' 1236864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2415_range (index : Nat) (lower : 1236480 ≤ index) (upper : index < 1236992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1236736 then
    if cut : index < 1236608 then
      exact segment_sound _ 1236480 128 Restriction2415_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1236608 128 Restriction2415_1_checked index (by omega) (by omega)
  else
    if cut : index < 1236864 then
      exact segment_sound _ 1236736 128 Restriction2415_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1236864 128 Restriction2415_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
