import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2302_0_checked : (List.range' 1178624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2302_1_checked : (List.range' 1178752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2302_2_checked : (List.range' 1178880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2302_3_checked : (List.range' 1179008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2302_range (index : Nat) (lower : 1178624 ≤ index) (upper : index < 1179136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1178880 then
    if cut : index < 1178752 then
      exact segment_sound _ 1178624 128 Restriction2302_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1178752 128 Restriction2302_1_checked index (by omega) (by omega)
  else
    if cut : index < 1179008 then
      exact segment_sound _ 1178880 128 Restriction2302_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1179008 128 Restriction2302_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
