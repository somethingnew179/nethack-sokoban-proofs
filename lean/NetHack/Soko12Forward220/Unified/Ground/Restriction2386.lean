import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2386_0_checked : (List.range' 1221632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2386_1_checked : (List.range' 1221760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2386_2_checked : (List.range' 1221888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2386_3_checked : (List.range' 1222016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2386_range (index : Nat) (lower : 1221632 ≤ index) (upper : index < 1222144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1221888 then
    if cut : index < 1221760 then
      exact segment_sound _ 1221632 128 Restriction2386_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1221760 128 Restriction2386_1_checked index (by omega) (by omega)
  else
    if cut : index < 1222016 then
      exact segment_sound _ 1221888 128 Restriction2386_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1222016 128 Restriction2386_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
