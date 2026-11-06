import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0068_0_checked : (List.range' 34816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0068_1_checked : (List.range' 34944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0068_2_checked : (List.range' 35072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0068_3_checked : (List.range' 35200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0068_range (index : Nat) (lower : 34816 ≤ index) (upper : index < 35328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 35072 then
    if cut : index < 34944 then
      exact segment_sound _ 34816 128 Restriction0068_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 34944 128 Restriction0068_1_checked index (by omega) (by omega)
  else
    if cut : index < 35200 then
      exact segment_sound _ 35072 128 Restriction0068_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 35200 128 Restriction0068_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
