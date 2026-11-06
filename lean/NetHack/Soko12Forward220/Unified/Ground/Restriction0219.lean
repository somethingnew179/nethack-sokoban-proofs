import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0219_0_checked : (List.range' 112128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0219_1_checked : (List.range' 112256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0219_2_checked : (List.range' 112384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0219_3_checked : (List.range' 112512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0219_range (index : Nat) (lower : 112128 ≤ index) (upper : index < 112640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 112384 then
    if cut : index < 112256 then
      exact segment_sound _ 112128 128 Restriction0219_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 112256 128 Restriction0219_1_checked index (by omega) (by omega)
  else
    if cut : index < 112512 then
      exact segment_sound _ 112384 128 Restriction0219_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 112512 128 Restriction0219_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
