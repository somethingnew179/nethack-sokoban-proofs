import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0036_0_checked : (List.range' 18432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0036_1_checked : (List.range' 18560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0036_2_checked : (List.range' 18688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0036_3_checked : (List.range' 18816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0036_range (index : Nat) (lower : 18432 ≤ index) (upper : index < 18944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 18688 then
    if cut : index < 18560 then
      exact segment_sound _ 18432 128 Restriction0036_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 18560 128 Restriction0036_1_checked index (by omega) (by omega)
  else
    if cut : index < 18816 then
      exact segment_sound _ 18688 128 Restriction0036_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 18816 128 Restriction0036_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
