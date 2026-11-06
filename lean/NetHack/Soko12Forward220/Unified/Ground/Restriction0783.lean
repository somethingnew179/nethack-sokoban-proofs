import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0783_0_checked : (List.range' 400896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0783_1_checked : (List.range' 401024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0783_2_checked : (List.range' 401152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0783_3_checked : (List.range' 401280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0783_range (index : Nat) (lower : 400896 ≤ index) (upper : index < 401408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 401152 then
    if cut : index < 401024 then
      exact segment_sound _ 400896 128 Restriction0783_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 401024 128 Restriction0783_1_checked index (by omega) (by omega)
  else
    if cut : index < 401280 then
      exact segment_sound _ 401152 128 Restriction0783_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 401280 128 Restriction0783_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
