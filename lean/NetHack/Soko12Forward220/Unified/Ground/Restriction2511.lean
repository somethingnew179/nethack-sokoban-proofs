import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2511_0_checked : (List.range' 1285632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2511_1_checked : (List.range' 1285760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2511_2_checked : (List.range' 1285888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2511_3_checked : (List.range' 1286016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2511_range (index : Nat) (lower : 1285632 ≤ index) (upper : index < 1286144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1285888 then
    if cut : index < 1285760 then
      exact segment_sound _ 1285632 128 Restriction2511_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1285760 128 Restriction2511_1_checked index (by omega) (by omega)
  else
    if cut : index < 1286016 then
      exact segment_sound _ 1285888 128 Restriction2511_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1286016 128 Restriction2511_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
