import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1723_0_checked : (List.range' 882176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1723_1_checked : (List.range' 882304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1723_2_checked : (List.range' 882432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1723_3_checked : (List.range' 882560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1723_range (index : Nat) (lower : 882176 ≤ index) (upper : index < 882688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 882432 then
    if cut : index < 882304 then
      exact segment_sound _ 882176 128 Restriction1723_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 882304 128 Restriction1723_1_checked index (by omega) (by omega)
  else
    if cut : index < 882560 then
      exact segment_sound _ 882432 128 Restriction1723_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 882560 128 Restriction1723_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
