import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0947_0_checked : (List.range' 484864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0947_1_checked : (List.range' 484992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0947_2_checked : (List.range' 485120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0947_3_checked : (List.range' 485248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0947_range (index : Nat) (lower : 484864 ≤ index) (upper : index < 485376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 485120 then
    if cut : index < 484992 then
      exact segment_sound _ 484864 128 Restriction0947_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 484992 128 Restriction0947_1_checked index (by omega) (by omega)
  else
    if cut : index < 485248 then
      exact segment_sound _ 485120 128 Restriction0947_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 485248 128 Restriction0947_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
