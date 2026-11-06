import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2509_0_checked : (List.range' 1284608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2509_1_checked : (List.range' 1284736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2509_2_checked : (List.range' 1284864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2509_3_checked : (List.range' 1284992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2509_range (index : Nat) (lower : 1284608 ≤ index) (upper : index < 1285120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1284864 then
    if cut : index < 1284736 then
      exact segment_sound _ 1284608 128 Restriction2509_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1284736 128 Restriction2509_1_checked index (by omega) (by omega)
  else
    if cut : index < 1284992 then
      exact segment_sound _ 1284864 128 Restriction2509_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1284992 128 Restriction2509_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
