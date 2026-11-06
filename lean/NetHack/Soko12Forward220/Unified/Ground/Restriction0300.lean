import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0300_0_checked : (List.range' 153600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0300_1_checked : (List.range' 153728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0300_2_checked : (List.range' 153856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0300_3_checked : (List.range' 153984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0300_range (index : Nat) (lower : 153600 ≤ index) (upper : index < 154112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 153856 then
    if cut : index < 153728 then
      exact segment_sound _ 153600 128 Restriction0300_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 153728 128 Restriction0300_1_checked index (by omega) (by omega)
  else
    if cut : index < 153984 then
      exact segment_sound _ 153856 128 Restriction0300_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 153984 128 Restriction0300_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
