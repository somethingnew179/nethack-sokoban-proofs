import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0924_0_checked : (List.range' 473088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0924_1_checked : (List.range' 473216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0924_2_checked : (List.range' 473344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0924_3_checked : (List.range' 473472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0924_range (index : Nat) (lower : 473088 ≤ index) (upper : index < 473600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 473344 then
    if cut : index < 473216 then
      exact segment_sound _ 473088 128 Restriction0924_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 473216 128 Restriction0924_1_checked index (by omega) (by omega)
  else
    if cut : index < 473472 then
      exact segment_sound _ 473344 128 Restriction0924_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 473472 128 Restriction0924_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
