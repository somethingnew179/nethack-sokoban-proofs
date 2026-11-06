import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0598_0_checked : (List.range' 306176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0598_1_checked : (List.range' 306304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0598_2_checked : (List.range' 306432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0598_3_checked : (List.range' 306560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0598_range (index : Nat) (lower : 306176 ≤ index) (upper : index < 306688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 306432 then
    if cut : index < 306304 then
      exact segment_sound _ 306176 128 Restriction0598_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 306304 128 Restriction0598_1_checked index (by omega) (by omega)
  else
    if cut : index < 306560 then
      exact segment_sound _ 306432 128 Restriction0598_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 306560 128 Restriction0598_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
