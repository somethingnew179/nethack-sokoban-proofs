import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2420_0_checked : (List.range' 1239040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2420_1_checked : (List.range' 1239168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2420_2_checked : (List.range' 1239296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2420_3_checked : (List.range' 1239424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2420_range (index : Nat) (lower : 1239040 ≤ index) (upper : index < 1239552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1239296 then
    if cut : index < 1239168 then
      exact segment_sound _ 1239040 128 Restriction2420_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1239168 128 Restriction2420_1_checked index (by omega) (by omega)
  else
    if cut : index < 1239424 then
      exact segment_sound _ 1239296 128 Restriction2420_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1239424 128 Restriction2420_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
