import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2286_0_checked : (List.range' 1170432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2286_1_checked : (List.range' 1170560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2286_2_checked : (List.range' 1170688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2286_3_checked : (List.range' 1170816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2286_range (index : Nat) (lower : 1170432 ≤ index) (upper : index < 1170944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1170688 then
    if cut : index < 1170560 then
      exact segment_sound _ 1170432 128 Restriction2286_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1170560 128 Restriction2286_1_checked index (by omega) (by omega)
  else
    if cut : index < 1170816 then
      exact segment_sound _ 1170688 128 Restriction2286_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1170816 128 Restriction2286_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
