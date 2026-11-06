import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0019_0_checked : (List.range' 9728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0019_1_checked : (List.range' 9856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0019_2_checked : (List.range' 9984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0019_3_checked : (List.range' 10112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0019_range (index : Nat) (lower : 9728 ≤ index) (upper : index < 10240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 9984 then
    if cut : index < 9856 then
      exact segment_sound _ 9728 128 Restriction0019_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 9856 128 Restriction0019_1_checked index (by omega) (by omega)
  else
    if cut : index < 10112 then
      exact segment_sound _ 9984 128 Restriction0019_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 10112 128 Restriction0019_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
