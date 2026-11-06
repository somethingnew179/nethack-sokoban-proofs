import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2421_0_checked : (List.range' 1239552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2421_1_checked : (List.range' 1239680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2421_2_checked : (List.range' 1239808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2421_3_checked : (List.range' 1239936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2421_range (index : Nat) (lower : 1239552 ≤ index) (upper : index < 1240064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1239808 then
    if cut : index < 1239680 then
      exact segment_sound _ 1239552 128 Restriction2421_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1239680 128 Restriction2421_1_checked index (by omega) (by omega)
  else
    if cut : index < 1239936 then
      exact segment_sound _ 1239808 128 Restriction2421_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1239936 128 Restriction2421_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
