import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2253_0_checked : (List.range' 1153536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2253_1_checked : (List.range' 1153664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2253_2_checked : (List.range' 1153792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2253_3_checked : (List.range' 1153920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2253_range (index : Nat) (lower : 1153536 ≤ index) (upper : index < 1154048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1153792 then
    if cut : index < 1153664 then
      exact segment_sound _ 1153536 128 Restriction2253_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1153664 128 Restriction2253_1_checked index (by omega) (by omega)
  else
    if cut : index < 1153920 then
      exact segment_sound _ 1153792 128 Restriction2253_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1153920 128 Restriction2253_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
