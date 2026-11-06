import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2427_0_checked : (List.range' 1242624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2427_1_checked : (List.range' 1242752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2427_2_checked : (List.range' 1242880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2427_3_checked : (List.range' 1243008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2427_range (index : Nat) (lower : 1242624 ≤ index) (upper : index < 1243136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1242880 then
    if cut : index < 1242752 then
      exact segment_sound _ 1242624 128 Restriction2427_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1242752 128 Restriction2427_1_checked index (by omega) (by omega)
  else
    if cut : index < 1243008 then
      exact segment_sound _ 1242880 128 Restriction2427_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1243008 128 Restriction2427_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
