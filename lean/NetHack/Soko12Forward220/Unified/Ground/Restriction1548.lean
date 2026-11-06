import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1548_0_checked : (List.range' 792576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1548_1_checked : (List.range' 792704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1548_2_checked : (List.range' 792832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1548_3_checked : (List.range' 792960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1548_range (index : Nat) (lower : 792576 ≤ index) (upper : index < 793088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 792832 then
    if cut : index < 792704 then
      exact segment_sound _ 792576 128 Restriction1548_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 792704 128 Restriction1548_1_checked index (by omega) (by omega)
  else
    if cut : index < 792960 then
      exact segment_sound _ 792832 128 Restriction1548_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 792960 128 Restriction1548_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
