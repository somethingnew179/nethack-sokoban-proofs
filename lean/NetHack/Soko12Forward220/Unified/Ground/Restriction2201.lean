import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2201_0_checked : (List.range' 1126912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2201_1_checked : (List.range' 1127040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2201_2_checked : (List.range' 1127168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2201_3_checked : (List.range' 1127296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2201_range (index : Nat) (lower : 1126912 ≤ index) (upper : index < 1127424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1127168 then
    if cut : index < 1127040 then
      exact segment_sound _ 1126912 128 Restriction2201_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1127040 128 Restriction2201_1_checked index (by omega) (by omega)
  else
    if cut : index < 1127296 then
      exact segment_sound _ 1127168 128 Restriction2201_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1127296 128 Restriction2201_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
