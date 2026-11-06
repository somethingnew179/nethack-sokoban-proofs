import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2074_0_checked : (List.range' 1061888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2074_1_checked : (List.range' 1062016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2074_2_checked : (List.range' 1062144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2074_3_checked : (List.range' 1062272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2074_range (index : Nat) (lower : 1061888 ≤ index) (upper : index < 1062400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1062144 then
    if cut : index < 1062016 then
      exact segment_sound _ 1061888 128 Restriction2074_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1062016 128 Restriction2074_1_checked index (by omega) (by omega)
  else
    if cut : index < 1062272 then
      exact segment_sound _ 1062144 128 Restriction2074_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1062272 128 Restriction2074_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
