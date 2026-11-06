import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2008_0_checked : (List.range' 1028096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2008_1_checked : (List.range' 1028224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2008_2_checked : (List.range' 1028352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2008_3_checked : (List.range' 1028480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2008_range (index : Nat) (lower : 1028096 ≤ index) (upper : index < 1028608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1028352 then
    if cut : index < 1028224 then
      exact segment_sound _ 1028096 128 Restriction2008_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1028224 128 Restriction2008_1_checked index (by omega) (by omega)
  else
    if cut : index < 1028480 then
      exact segment_sound _ 1028352 128 Restriction2008_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1028480 128 Restriction2008_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
