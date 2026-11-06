import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0198_0_checked : (List.range' 101376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0198_1_checked : (List.range' 101504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0198_2_checked : (List.range' 101632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0198_3_checked : (List.range' 101760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0198_range (index : Nat) (lower : 101376 ≤ index) (upper : index < 101888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 101632 then
    if cut : index < 101504 then
      exact segment_sound _ 101376 128 Restriction0198_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 101504 128 Restriction0198_1_checked index (by omega) (by omega)
  else
    if cut : index < 101760 then
      exact segment_sound _ 101632 128 Restriction0198_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 101760 128 Restriction0198_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
