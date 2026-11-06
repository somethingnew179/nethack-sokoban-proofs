import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2363_0_checked : (List.range' 1209856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2363_1_checked : (List.range' 1209984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2363_2_checked : (List.range' 1210112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2363_3_checked : (List.range' 1210240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2363_range (index : Nat) (lower : 1209856 ≤ index) (upper : index < 1210368) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1210112 then
    if cut : index < 1209984 then
      exact segment_sound _ 1209856 128 Restriction2363_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1209984 128 Restriction2363_1_checked index (by omega) (by omega)
  else
    if cut : index < 1210240 then
      exact segment_sound _ 1210112 128 Restriction2363_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1210240 128 Restriction2363_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
