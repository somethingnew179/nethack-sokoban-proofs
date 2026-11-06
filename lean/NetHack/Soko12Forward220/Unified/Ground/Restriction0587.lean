import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0587_0_checked : (List.range' 300544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0587_1_checked : (List.range' 300672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0587_2_checked : (List.range' 300800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0587_3_checked : (List.range' 300928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0587_range (index : Nat) (lower : 300544 ≤ index) (upper : index < 301056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 300800 then
    if cut : index < 300672 then
      exact segment_sound _ 300544 128 Restriction0587_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 300672 128 Restriction0587_1_checked index (by omega) (by omega)
  else
    if cut : index < 300928 then
      exact segment_sound _ 300800 128 Restriction0587_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 300928 128 Restriction0587_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
