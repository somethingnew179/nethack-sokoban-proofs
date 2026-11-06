import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2440_0_checked : (List.range' 1249280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2440_1_checked : (List.range' 1249408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2440_2_checked : (List.range' 1249536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2440_3_checked : (List.range' 1249664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2440_range (index : Nat) (lower : 1249280 ≤ index) (upper : index < 1249792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1249536 then
    if cut : index < 1249408 then
      exact segment_sound _ 1249280 128 Restriction2440_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1249408 128 Restriction2440_1_checked index (by omega) (by omega)
  else
    if cut : index < 1249664 then
      exact segment_sound _ 1249536 128 Restriction2440_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1249664 128 Restriction2440_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
