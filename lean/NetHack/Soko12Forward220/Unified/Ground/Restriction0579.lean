import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0579_0_checked : (List.range' 296448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0579_1_checked : (List.range' 296576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0579_2_checked : (List.range' 296704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0579_3_checked : (List.range' 296832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0579_range (index : Nat) (lower : 296448 ≤ index) (upper : index < 296960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 296704 then
    if cut : index < 296576 then
      exact segment_sound _ 296448 128 Restriction0579_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 296576 128 Restriction0579_1_checked index (by omega) (by omega)
  else
    if cut : index < 296832 then
      exact segment_sound _ 296704 128 Restriction0579_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 296832 128 Restriction0579_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
