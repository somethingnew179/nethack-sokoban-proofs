import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1224_0_checked : (List.range' 626688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1224_1_checked : (List.range' 626816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1224_2_checked : (List.range' 626944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1224_3_checked : (List.range' 627072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1224_range (index : Nat) (lower : 626688 ≤ index) (upper : index < 627200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 626944 then
    if cut : index < 626816 then
      exact segment_sound _ 626688 128 Restriction1224_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 626816 128 Restriction1224_1_checked index (by omega) (by omega)
  else
    if cut : index < 627072 then
      exact segment_sound _ 626944 128 Restriction1224_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 627072 128 Restriction1224_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
