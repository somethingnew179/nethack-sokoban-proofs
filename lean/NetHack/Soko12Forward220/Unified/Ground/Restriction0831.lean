import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0831_0_checked : (List.range' 425472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0831_1_checked : (List.range' 425600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0831_2_checked : (List.range' 425728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0831_3_checked : (List.range' 425856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0831_range (index : Nat) (lower : 425472 ≤ index) (upper : index < 425984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 425728 then
    if cut : index < 425600 then
      exact segment_sound _ 425472 128 Restriction0831_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 425600 128 Restriction0831_1_checked index (by omega) (by omega)
  else
    if cut : index < 425856 then
      exact segment_sound _ 425728 128 Restriction0831_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 425856 128 Restriction0831_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
