import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0532_0_checked : (List.range' 272384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0532_1_checked : (List.range' 272512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0532_2_checked : (List.range' 272640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0532_3_checked : (List.range' 272768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0532_range (index : Nat) (lower : 272384 ≤ index) (upper : index < 272896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 272640 then
    if cut : index < 272512 then
      exact segment_sound _ 272384 128 Restriction0532_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 272512 128 Restriction0532_1_checked index (by omega) (by omega)
  else
    if cut : index < 272768 then
      exact segment_sound _ 272640 128 Restriction0532_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 272768 128 Restriction0532_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
