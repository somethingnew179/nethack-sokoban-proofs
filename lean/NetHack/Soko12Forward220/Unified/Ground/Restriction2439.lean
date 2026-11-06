import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2439_0_checked : (List.range' 1248768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2439_1_checked : (List.range' 1248896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2439_2_checked : (List.range' 1249024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2439_3_checked : (List.range' 1249152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2439_range (index : Nat) (lower : 1248768 ≤ index) (upper : index < 1249280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1249024 then
    if cut : index < 1248896 then
      exact segment_sound _ 1248768 128 Restriction2439_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1248896 128 Restriction2439_1_checked index (by omega) (by omega)
  else
    if cut : index < 1249152 then
      exact segment_sound _ 1249024 128 Restriction2439_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1249152 128 Restriction2439_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
