import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2242_0_checked : (List.range' 1147904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2242_1_checked : (List.range' 1148032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2242_2_checked : (List.range' 1148160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2242_3_checked : (List.range' 1148288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2242_range (index : Nat) (lower : 1147904 ≤ index) (upper : index < 1148416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1148160 then
    if cut : index < 1148032 then
      exact segment_sound _ 1147904 128 Restriction2242_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1148032 128 Restriction2242_1_checked index (by omega) (by omega)
  else
    if cut : index < 1148288 then
      exact segment_sound _ 1148160 128 Restriction2242_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1148288 128 Restriction2242_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
