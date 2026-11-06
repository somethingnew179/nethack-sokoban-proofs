import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2274_0_checked : (List.range' 1164288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2274_1_checked : (List.range' 1164416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2274_2_checked : (List.range' 1164544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2274_3_checked : (List.range' 1164672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2274_range (index : Nat) (lower : 1164288 ≤ index) (upper : index < 1164800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1164544 then
    if cut : index < 1164416 then
      exact segment_sound _ 1164288 128 Restriction2274_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1164416 128 Restriction2274_1_checked index (by omega) (by omega)
  else
    if cut : index < 1164672 then
      exact segment_sound _ 1164544 128 Restriction2274_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1164672 128 Restriction2274_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
