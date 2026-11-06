import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0902_0_checked : (List.range' 461824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0902_1_checked : (List.range' 461952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0902_2_checked : (List.range' 462080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0902_3_checked : (List.range' 462208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0902_range (index : Nat) (lower : 461824 ≤ index) (upper : index < 462336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 462080 then
    if cut : index < 461952 then
      exact segment_sound _ 461824 128 Restriction0902_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 461952 128 Restriction0902_1_checked index (by omega) (by omega)
  else
    if cut : index < 462208 then
      exact segment_sound _ 462080 128 Restriction0902_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 462208 128 Restriction0902_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
