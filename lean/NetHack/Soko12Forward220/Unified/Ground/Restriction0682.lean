import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0682_0_checked : (List.range' 349184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0682_1_checked : (List.range' 349312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0682_2_checked : (List.range' 349440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0682_3_checked : (List.range' 349568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0682_range (index : Nat) (lower : 349184 ≤ index) (upper : index < 349696) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 349440 then
    if cut : index < 349312 then
      exact segment_sound _ 349184 128 Restriction0682_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 349312 128 Restriction0682_1_checked index (by omega) (by omega)
  else
    if cut : index < 349568 then
      exact segment_sound _ 349440 128 Restriction0682_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 349568 128 Restriction0682_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
