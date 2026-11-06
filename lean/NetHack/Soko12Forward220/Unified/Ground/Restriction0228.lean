import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0228_0_checked : (List.range' 116736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0228_1_checked : (List.range' 116864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0228_2_checked : (List.range' 116992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0228_3_checked : (List.range' 117120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0228_range (index : Nat) (lower : 116736 ≤ index) (upper : index < 117248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 116992 then
    if cut : index < 116864 then
      exact segment_sound _ 116736 128 Restriction0228_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 116864 128 Restriction0228_1_checked index (by omega) (by omega)
  else
    if cut : index < 117120 then
      exact segment_sound _ 116992 128 Restriction0228_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 117120 128 Restriction0228_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
