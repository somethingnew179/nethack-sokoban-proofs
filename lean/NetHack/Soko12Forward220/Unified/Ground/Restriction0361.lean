import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0361_0_checked : (List.range' 184832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0361_1_checked : (List.range' 184960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0361_2_checked : (List.range' 185088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0361_3_checked : (List.range' 185216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0361_range (index : Nat) (lower : 184832 ≤ index) (upper : index < 185344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 185088 then
    if cut : index < 184960 then
      exact segment_sound _ 184832 128 Restriction0361_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 184960 128 Restriction0361_1_checked index (by omega) (by omega)
  else
    if cut : index < 185216 then
      exact segment_sound _ 185088 128 Restriction0361_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 185216 128 Restriction0361_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
