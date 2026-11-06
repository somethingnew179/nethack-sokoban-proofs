import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0289_0_checked : (List.range' 147968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0289_1_checked : (List.range' 148096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0289_2_checked : (List.range' 148224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0289_3_checked : (List.range' 148352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0289_range (index : Nat) (lower : 147968 ≤ index) (upper : index < 148480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 148224 then
    if cut : index < 148096 then
      exact segment_sound _ 147968 128 Restriction0289_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 148096 128 Restriction0289_1_checked index (by omega) (by omega)
  else
    if cut : index < 148352 then
      exact segment_sound _ 148224 128 Restriction0289_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 148352 128 Restriction0289_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
