import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0862_0_checked : (List.range' 441344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0862_1_checked : (List.range' 441472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0862_2_checked : (List.range' 441600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0862_3_checked : (List.range' 441728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0862_range (index : Nat) (lower : 441344 ≤ index) (upper : index < 441856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 441600 then
    if cut : index < 441472 then
      exact segment_sound _ 441344 128 Restriction0862_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 441472 128 Restriction0862_1_checked index (by omega) (by omega)
  else
    if cut : index < 441728 then
      exact segment_sound _ 441600 128 Restriction0862_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 441728 128 Restriction0862_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
