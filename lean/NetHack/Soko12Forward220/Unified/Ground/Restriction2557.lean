import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2557_0_checked : (List.range' 1309184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2557_1_checked : (List.range' 1309312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2557_2_checked : (List.range' 1309440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2557_3_checked : (List.range' 1309568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2557_range (index : Nat) (lower : 1309184 ≤ index) (upper : index < 1309696) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1309440 then
    if cut : index < 1309312 then
      exact segment_sound _ 1309184 128 Restriction2557_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1309312 128 Restriction2557_1_checked index (by omega) (by omega)
  else
    if cut : index < 1309568 then
      exact segment_sound _ 1309440 128 Restriction2557_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1309568 128 Restriction2557_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
