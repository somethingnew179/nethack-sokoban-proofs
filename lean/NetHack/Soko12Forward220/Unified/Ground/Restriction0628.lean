import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0628_0_checked : (List.range' 321536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0628_1_checked : (List.range' 321664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0628_2_checked : (List.range' 321792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0628_3_checked : (List.range' 321920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0628_range (index : Nat) (lower : 321536 ≤ index) (upper : index < 322048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 321792 then
    if cut : index < 321664 then
      exact segment_sound _ 321536 128 Restriction0628_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 321664 128 Restriction0628_1_checked index (by omega) (by omega)
  else
    if cut : index < 321920 then
      exact segment_sound _ 321792 128 Restriction0628_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 321920 128 Restriction0628_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
