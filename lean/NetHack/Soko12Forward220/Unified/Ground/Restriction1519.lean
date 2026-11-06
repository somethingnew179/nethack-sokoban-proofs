import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1519_0_checked : (List.range' 777728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1519_1_checked : (List.range' 777856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1519_2_checked : (List.range' 777984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1519_3_checked : (List.range' 778112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1519_range (index : Nat) (lower : 777728 ≤ index) (upper : index < 778240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 777984 then
    if cut : index < 777856 then
      exact segment_sound _ 777728 128 Restriction1519_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 777856 128 Restriction1519_1_checked index (by omega) (by omega)
  else
    if cut : index < 778112 then
      exact segment_sound _ 777984 128 Restriction1519_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 778112 128 Restriction1519_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
