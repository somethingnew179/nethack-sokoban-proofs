import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0306_0_checked : (List.range' 156672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0306_1_checked : (List.range' 156800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0306_2_checked : (List.range' 156928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0306_3_checked : (List.range' 157056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0306_range (index : Nat) (lower : 156672 ≤ index) (upper : index < 157184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 156928 then
    if cut : index < 156800 then
      exact segment_sound _ 156672 128 Restriction0306_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 156800 128 Restriction0306_1_checked index (by omega) (by omega)
  else
    if cut : index < 157056 then
      exact segment_sound _ 156928 128 Restriction0306_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 157056 128 Restriction0306_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
