import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0805_0_checked : (List.range' 412160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0805_1_checked : (List.range' 412288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0805_2_checked : (List.range' 412416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0805_3_checked : (List.range' 412544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0805_range (index : Nat) (lower : 412160 ≤ index) (upper : index < 412672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 412416 then
    if cut : index < 412288 then
      exact segment_sound _ 412160 128 Restriction0805_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 412288 128 Restriction0805_1_checked index (by omega) (by omega)
  else
    if cut : index < 412544 then
      exact segment_sound _ 412416 128 Restriction0805_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 412544 128 Restriction0805_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
