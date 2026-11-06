import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1952_0_checked : (List.range' 999424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1952_1_checked : (List.range' 999552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1952_2_checked : (List.range' 999680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1952_3_checked : (List.range' 999808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1952_range (index : Nat) (lower : 999424 ≤ index) (upper : index < 999936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 999680 then
    if cut : index < 999552 then
      exact segment_sound _ 999424 128 Restriction1952_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 999552 128 Restriction1952_1_checked index (by omega) (by omega)
  else
    if cut : index < 999808 then
      exact segment_sound _ 999680 128 Restriction1952_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 999808 128 Restriction1952_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
