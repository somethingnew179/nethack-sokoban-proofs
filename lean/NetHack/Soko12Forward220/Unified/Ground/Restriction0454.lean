import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0454_0_checked : (List.range' 232448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0454_1_checked : (List.range' 232576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0454_2_checked : (List.range' 232704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0454_3_checked : (List.range' 232832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0454_range (index : Nat) (lower : 232448 ≤ index) (upper : index < 232960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 232704 then
    if cut : index < 232576 then
      exact segment_sound _ 232448 128 Restriction0454_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 232576 128 Restriction0454_1_checked index (by omega) (by omega)
  else
    if cut : index < 232832 then
      exact segment_sound _ 232704 128 Restriction0454_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 232832 128 Restriction0454_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
