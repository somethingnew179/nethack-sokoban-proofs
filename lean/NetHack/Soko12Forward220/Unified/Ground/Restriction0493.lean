import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0493_0_checked : (List.range' 252416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0493_1_checked : (List.range' 252544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0493_2_checked : (List.range' 252672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0493_3_checked : (List.range' 252800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0493_range (index : Nat) (lower : 252416 ≤ index) (upper : index < 252928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 252672 then
    if cut : index < 252544 then
      exact segment_sound _ 252416 128 Restriction0493_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 252544 128 Restriction0493_1_checked index (by omega) (by omega)
  else
    if cut : index < 252800 then
      exact segment_sound _ 252672 128 Restriction0493_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 252800 128 Restriction0493_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
