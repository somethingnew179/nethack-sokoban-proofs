import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2562_0_checked : (List.range' 1311744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2562_1_checked : (List.range' 1311872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2562_2_checked : (List.range' 1312000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2562_3_checked : (List.range' 1312128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2562_range (index : Nat) (lower : 1311744 ≤ index) (upper : index < 1312256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1312000 then
    if cut : index < 1311872 then
      exact segment_sound _ 1311744 128 Restriction2562_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1311872 128 Restriction2562_1_checked index (by omega) (by omega)
  else
    if cut : index < 1312128 then
      exact segment_sound _ 1312000 128 Restriction2562_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1312128 128 Restriction2562_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
