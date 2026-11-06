import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1492_0_checked : (List.range' 763904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1492_1_checked : (List.range' 764032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1492_2_checked : (List.range' 764160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1492_3_checked : (List.range' 764288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1492_range (index : Nat) (lower : 763904 ≤ index) (upper : index < 764416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 764160 then
    if cut : index < 764032 then
      exact segment_sound _ 763904 128 Restriction1492_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 764032 128 Restriction1492_1_checked index (by omega) (by omega)
  else
    if cut : index < 764288 then
      exact segment_sound _ 764160 128 Restriction1492_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 764288 128 Restriction1492_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
