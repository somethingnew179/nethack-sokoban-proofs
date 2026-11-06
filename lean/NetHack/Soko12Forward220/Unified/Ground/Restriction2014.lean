import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2014_0_checked : (List.range' 1031168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2014_1_checked : (List.range' 1031296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2014_2_checked : (List.range' 1031424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2014_3_checked : (List.range' 1031552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2014_range (index : Nat) (lower : 1031168 ≤ index) (upper : index < 1031680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1031424 then
    if cut : index < 1031296 then
      exact segment_sound _ 1031168 128 Restriction2014_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1031296 128 Restriction2014_1_checked index (by omega) (by omega)
  else
    if cut : index < 1031552 then
      exact segment_sound _ 1031424 128 Restriction2014_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1031552 128 Restriction2014_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
