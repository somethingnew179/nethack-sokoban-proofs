import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2487_0_checked : (List.range' 1273344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2487_1_checked : (List.range' 1273472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2487_2_checked : (List.range' 1273600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2487_3_checked : (List.range' 1273728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2487_range (index : Nat) (lower : 1273344 ≤ index) (upper : index < 1273856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1273600 then
    if cut : index < 1273472 then
      exact segment_sound _ 1273344 128 Restriction2487_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1273472 128 Restriction2487_1_checked index (by omega) (by omega)
  else
    if cut : index < 1273728 then
      exact segment_sound _ 1273600 128 Restriction2487_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1273728 128 Restriction2487_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
