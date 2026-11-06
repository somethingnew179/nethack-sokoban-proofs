import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0312_0_checked : (List.range' 159744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0312_1_checked : (List.range' 159872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0312_2_checked : (List.range' 160000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0312_3_checked : (List.range' 160128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0312_range (index : Nat) (lower : 159744 ≤ index) (upper : index < 160256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 160000 then
    if cut : index < 159872 then
      exact segment_sound _ 159744 128 Restriction0312_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 159872 128 Restriction0312_1_checked index (by omega) (by omega)
  else
    if cut : index < 160128 then
      exact segment_sound _ 160000 128 Restriction0312_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 160128 128 Restriction0312_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
