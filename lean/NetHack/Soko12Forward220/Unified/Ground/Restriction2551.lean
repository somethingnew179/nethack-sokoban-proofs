import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2551_0_checked : (List.range' 1306112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2551_1_checked : (List.range' 1306240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2551_2_checked : (List.range' 1306368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2551_3_checked : (List.range' 1306496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2551_range (index : Nat) (lower : 1306112 ≤ index) (upper : index < 1306624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1306368 then
    if cut : index < 1306240 then
      exact segment_sound _ 1306112 128 Restriction2551_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1306240 128 Restriction2551_1_checked index (by omega) (by omega)
  else
    if cut : index < 1306496 then
      exact segment_sound _ 1306368 128 Restriction2551_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1306496 128 Restriction2551_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
