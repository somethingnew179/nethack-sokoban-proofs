import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0802_0_checked : (List.range' 410624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0802_1_checked : (List.range' 410752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0802_2_checked : (List.range' 410880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0802_3_checked : (List.range' 411008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0802_range (index : Nat) (lower : 410624 ≤ index) (upper : index < 411136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 410880 then
    if cut : index < 410752 then
      exact segment_sound _ 410624 128 Restriction0802_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 410752 128 Restriction0802_1_checked index (by omega) (by omega)
  else
    if cut : index < 411008 then
      exact segment_sound _ 410880 128 Restriction0802_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 411008 128 Restriction0802_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
