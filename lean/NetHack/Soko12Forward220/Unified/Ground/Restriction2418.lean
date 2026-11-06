import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2418_0_checked : (List.range' 1238016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2418_1_checked : (List.range' 1238144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2418_2_checked : (List.range' 1238272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2418_3_checked : (List.range' 1238400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2418_range (index : Nat) (lower : 1238016 ≤ index) (upper : index < 1238528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1238272 then
    if cut : index < 1238144 then
      exact segment_sound _ 1238016 128 Restriction2418_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1238144 128 Restriction2418_1_checked index (by omega) (by omega)
  else
    if cut : index < 1238400 then
      exact segment_sound _ 1238272 128 Restriction2418_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1238400 128 Restriction2418_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
