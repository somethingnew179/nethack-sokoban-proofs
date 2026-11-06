import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2325_0_checked : (List.range' 1190400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2325_1_checked : (List.range' 1190528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2325_2_checked : (List.range' 1190656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2325_3_checked : (List.range' 1190784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2325_range (index : Nat) (lower : 1190400 ≤ index) (upper : index < 1190912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1190656 then
    if cut : index < 1190528 then
      exact segment_sound _ 1190400 128 Restriction2325_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1190528 128 Restriction2325_1_checked index (by omega) (by omega)
  else
    if cut : index < 1190784 then
      exact segment_sound _ 1190656 128 Restriction2325_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1190784 128 Restriction2325_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
