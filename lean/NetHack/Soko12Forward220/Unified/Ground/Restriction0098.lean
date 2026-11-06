import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0098_0_checked : (List.range' 50176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0098_1_checked : (List.range' 50304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0098_2_checked : (List.range' 50432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0098_3_checked : (List.range' 50560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0098_range (index : Nat) (lower : 50176 ≤ index) (upper : index < 50688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 50432 then
    if cut : index < 50304 then
      exact segment_sound _ 50176 128 Restriction0098_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 50304 128 Restriction0098_1_checked index (by omega) (by omega)
  else
    if cut : index < 50560 then
      exact segment_sound _ 50432 128 Restriction0098_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 50560 128 Restriction0098_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
