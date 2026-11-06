import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0735_0_checked : (List.range' 376320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0735_1_checked : (List.range' 376448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0735_2_checked : (List.range' 376576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0735_3_checked : (List.range' 376704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0735_range (index : Nat) (lower : 376320 ≤ index) (upper : index < 376832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 376576 then
    if cut : index < 376448 then
      exact segment_sound _ 376320 128 Restriction0735_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 376448 128 Restriction0735_1_checked index (by omega) (by omega)
  else
    if cut : index < 376704 then
      exact segment_sound _ 376576 128 Restriction0735_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 376704 128 Restriction0735_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
