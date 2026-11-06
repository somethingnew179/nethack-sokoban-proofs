import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2321_0_checked : (List.range' 1188352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2321_1_checked : (List.range' 1188480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2321_2_checked : (List.range' 1188608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2321_3_checked : (List.range' 1188736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2321_range (index : Nat) (lower : 1188352 ≤ index) (upper : index < 1188864) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1188608 then
    if cut : index < 1188480 then
      exact segment_sound _ 1188352 128 Restriction2321_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1188480 128 Restriction2321_1_checked index (by omega) (by omega)
  else
    if cut : index < 1188736 then
      exact segment_sound _ 1188608 128 Restriction2321_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1188736 128 Restriction2321_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
