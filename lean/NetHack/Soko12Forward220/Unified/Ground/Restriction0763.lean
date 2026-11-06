import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0763_0_checked : (List.range' 390656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0763_1_checked : (List.range' 390784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0763_2_checked : (List.range' 390912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0763_3_checked : (List.range' 391040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0763_range (index : Nat) (lower : 390656 ≤ index) (upper : index < 391168) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 390912 then
    if cut : index < 390784 then
      exact segment_sound _ 390656 128 Restriction0763_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 390784 128 Restriction0763_1_checked index (by omega) (by omega)
  else
    if cut : index < 391040 then
      exact segment_sound _ 390912 128 Restriction0763_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 391040 128 Restriction0763_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
