import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1799_0_checked : (List.range' 921088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1799_1_checked : (List.range' 921216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1799_2_checked : (List.range' 921344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1799_3_checked : (List.range' 921472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1799_range (index : Nat) (lower : 921088 ≤ index) (upper : index < 921600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 921344 then
    if cut : index < 921216 then
      exact segment_sound _ 921088 128 Restriction1799_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 921216 128 Restriction1799_1_checked index (by omega) (by omega)
  else
    if cut : index < 921472 then
      exact segment_sound _ 921344 128 Restriction1799_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 921472 128 Restriction1799_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
