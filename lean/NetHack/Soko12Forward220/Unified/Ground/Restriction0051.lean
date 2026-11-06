import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0051_0_checked : (List.range' 26112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0051_1_checked : (List.range' 26240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0051_2_checked : (List.range' 26368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0051_3_checked : (List.range' 26496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0051_range (index : Nat) (lower : 26112 ≤ index) (upper : index < 26624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 26368 then
    if cut : index < 26240 then
      exact segment_sound _ 26112 128 Restriction0051_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 26240 128 Restriction0051_1_checked index (by omega) (by omega)
  else
    if cut : index < 26496 then
      exact segment_sound _ 26368 128 Restriction0051_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 26496 128 Restriction0051_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
