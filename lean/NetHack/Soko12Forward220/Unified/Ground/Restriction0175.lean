import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0175_0_checked : (List.range' 89600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0175_1_checked : (List.range' 89728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0175_2_checked : (List.range' 89856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0175_3_checked : (List.range' 89984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0175_range (index : Nat) (lower : 89600 ≤ index) (upper : index < 90112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 89856 then
    if cut : index < 89728 then
      exact segment_sound _ 89600 128 Restriction0175_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 89728 128 Restriction0175_1_checked index (by omega) (by omega)
  else
    if cut : index < 89984 then
      exact segment_sound _ 89856 128 Restriction0175_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 89984 128 Restriction0175_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
