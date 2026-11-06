import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0772_0_checked : (List.range' 395264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0772_1_checked : (List.range' 395392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0772_2_checked : (List.range' 395520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0772_3_checked : (List.range' 395648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0772_range (index : Nat) (lower : 395264 ≤ index) (upper : index < 395776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 395520 then
    if cut : index < 395392 then
      exact segment_sound _ 395264 128 Restriction0772_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 395392 128 Restriction0772_1_checked index (by omega) (by omega)
  else
    if cut : index < 395648 then
      exact segment_sound _ 395520 128 Restriction0772_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 395648 128 Restriction0772_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
