import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2410_0_checked : (List.range' 1233920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2410_1_checked : (List.range' 1234048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2410_2_checked : (List.range' 1234176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2410_3_checked : (List.range' 1234304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2410_range (index : Nat) (lower : 1233920 ≤ index) (upper : index < 1234432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1234176 then
    if cut : index < 1234048 then
      exact segment_sound _ 1233920 128 Restriction2410_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1234048 128 Restriction2410_1_checked index (by omega) (by omega)
  else
    if cut : index < 1234304 then
      exact segment_sound _ 1234176 128 Restriction2410_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1234304 128 Restriction2410_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
