import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0033_0_checked : (List.range' 16896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0033_1_checked : (List.range' 17024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0033_2_checked : (List.range' 17152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0033_3_checked : (List.range' 17280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0033_range (index : Nat) (lower : 16896 ≤ index) (upper : index < 17408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 17152 then
    if cut : index < 17024 then
      exact segment_sound _ 16896 128 Restriction0033_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 17024 128 Restriction0033_1_checked index (by omega) (by omega)
  else
    if cut : index < 17280 then
      exact segment_sound _ 17152 128 Restriction0033_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 17280 128 Restriction0033_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
