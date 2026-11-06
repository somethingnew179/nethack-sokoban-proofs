import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0816_0_checked : (List.range' 417792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0816_1_checked : (List.range' 417920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0816_2_checked : (List.range' 418048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0816_3_checked : (List.range' 418176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0816_range (index : Nat) (lower : 417792 ≤ index) (upper : index < 418304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 418048 then
    if cut : index < 417920 then
      exact segment_sound _ 417792 128 Restriction0816_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 417920 128 Restriction0816_1_checked index (by omega) (by omega)
  else
    if cut : index < 418176 then
      exact segment_sound _ 418048 128 Restriction0816_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 418176 128 Restriction0816_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
