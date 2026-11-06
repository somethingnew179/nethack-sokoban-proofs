import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0829_0_checked : (List.range' 424448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0829_1_checked : (List.range' 424576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0829_2_checked : (List.range' 424704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0829_3_checked : (List.range' 424832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0829_range (index : Nat) (lower : 424448 ≤ index) (upper : index < 424960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 424704 then
    if cut : index < 424576 then
      exact segment_sound _ 424448 128 Restriction0829_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 424576 128 Restriction0829_1_checked index (by omega) (by omega)
  else
    if cut : index < 424832 then
      exact segment_sound _ 424704 128 Restriction0829_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 424832 128 Restriction0829_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
