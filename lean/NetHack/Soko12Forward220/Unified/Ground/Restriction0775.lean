import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0775_0_checked : (List.range' 396800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0775_1_checked : (List.range' 396928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0775_2_checked : (List.range' 397056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0775_3_checked : (List.range' 397184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0775_range (index : Nat) (lower : 396800 ≤ index) (upper : index < 397312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 397056 then
    if cut : index < 396928 then
      exact segment_sound _ 396800 128 Restriction0775_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 396928 128 Restriction0775_1_checked index (by omega) (by omega)
  else
    if cut : index < 397184 then
      exact segment_sound _ 397056 128 Restriction0775_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 397184 128 Restriction0775_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
