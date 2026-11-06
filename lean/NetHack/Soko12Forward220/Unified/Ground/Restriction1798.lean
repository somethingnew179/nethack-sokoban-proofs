import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1798_0_checked : (List.range' 920576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1798_1_checked : (List.range' 920704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1798_2_checked : (List.range' 920832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1798_3_checked : (List.range' 920960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1798_range (index : Nat) (lower : 920576 ≤ index) (upper : index < 921088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 920832 then
    if cut : index < 920704 then
      exact segment_sound _ 920576 128 Restriction1798_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 920704 128 Restriction1798_1_checked index (by omega) (by omega)
  else
    if cut : index < 920960 then
      exact segment_sound _ 920832 128 Restriction1798_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 920960 128 Restriction1798_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
