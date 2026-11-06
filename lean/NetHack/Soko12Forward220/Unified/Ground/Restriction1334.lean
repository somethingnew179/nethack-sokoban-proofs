import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1334_0_checked : (List.range' 683008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1334_1_checked : (List.range' 683136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1334_2_checked : (List.range' 683264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1334_3_checked : (List.range' 683392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1334_range (index : Nat) (lower : 683008 ≤ index) (upper : index < 683520) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 683264 then
    if cut : index < 683136 then
      exact segment_sound _ 683008 128 Restriction1334_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 683136 128 Restriction1334_1_checked index (by omega) (by omega)
  else
    if cut : index < 683392 then
      exact segment_sound _ 683264 128 Restriction1334_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 683392 128 Restriction1334_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
