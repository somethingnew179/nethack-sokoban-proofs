import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2572_0_checked : (List.range' 1316864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2572_1_checked : (List.range' 1316992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2572_2_checked : (List.range' 1317120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2572_3_checked : (List.range' 1317248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2572_range (index : Nat) (lower : 1316864 ≤ index) (upper : index < 1317376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1317120 then
    if cut : index < 1316992 then
      exact segment_sound _ 1316864 128 Restriction2572_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1316992 128 Restriction2572_1_checked index (by omega) (by omega)
  else
    if cut : index < 1317248 then
      exact segment_sound _ 1317120 128 Restriction2572_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1317248 128 Restriction2572_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
