import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2016_0_checked : (List.range' 1032192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2016_1_checked : (List.range' 1032320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2016_2_checked : (List.range' 1032448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2016_3_checked : (List.range' 1032576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2016_range (index : Nat) (lower : 1032192 ≤ index) (upper : index < 1032704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1032448 then
    if cut : index < 1032320 then
      exact segment_sound _ 1032192 128 Restriction2016_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1032320 128 Restriction2016_1_checked index (by omega) (by omega)
  else
    if cut : index < 1032576 then
      exact segment_sound _ 1032448 128 Restriction2016_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1032576 128 Restriction2016_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
