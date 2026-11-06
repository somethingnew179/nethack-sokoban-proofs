import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2186_0_checked : (List.range' 1119232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2186_1_checked : (List.range' 1119360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2186_2_checked : (List.range' 1119488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2186_3_checked : (List.range' 1119616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2186_range (index : Nat) (lower : 1119232 ≤ index) (upper : index < 1119744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1119488 then
    if cut : index < 1119360 then
      exact segment_sound _ 1119232 128 Restriction2186_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1119360 128 Restriction2186_1_checked index (by omega) (by omega)
  else
    if cut : index < 1119616 then
      exact segment_sound _ 1119488 128 Restriction2186_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1119616 128 Restriction2186_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
