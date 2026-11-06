import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0526_0_checked : (List.range' 269312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0526_1_checked : (List.range' 269440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0526_2_checked : (List.range' 269568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0526_3_checked : (List.range' 269696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0526_range (index : Nat) (lower : 269312 ≤ index) (upper : index < 269824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 269568 then
    if cut : index < 269440 then
      exact segment_sound _ 269312 128 Restriction0526_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 269440 128 Restriction0526_1_checked index (by omega) (by omega)
  else
    if cut : index < 269696 then
      exact segment_sound _ 269568 128 Restriction0526_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 269696 128 Restriction0526_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
