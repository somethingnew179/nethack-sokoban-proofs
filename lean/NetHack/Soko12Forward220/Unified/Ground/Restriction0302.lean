import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0302_0_checked : (List.range' 154624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0302_1_checked : (List.range' 154752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0302_2_checked : (List.range' 154880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0302_3_checked : (List.range' 155008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0302_range (index : Nat) (lower : 154624 ≤ index) (upper : index < 155136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 154880 then
    if cut : index < 154752 then
      exact segment_sound _ 154624 128 Restriction0302_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 154752 128 Restriction0302_1_checked index (by omega) (by omega)
  else
    if cut : index < 155008 then
      exact segment_sound _ 154880 128 Restriction0302_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 155008 128 Restriction0302_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
