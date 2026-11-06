import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1015_0_checked : (List.range' 519680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1015_1_checked : (List.range' 519808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1015_2_checked : (List.range' 519936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1015_3_checked : (List.range' 520064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1015_range (index : Nat) (lower : 519680 ≤ index) (upper : index < 520192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 519936 then
    if cut : index < 519808 then
      exact segment_sound _ 519680 128 Restriction1015_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 519808 128 Restriction1015_1_checked index (by omega) (by omega)
  else
    if cut : index < 520064 then
      exact segment_sound _ 519936 128 Restriction1015_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 520064 128 Restriction1015_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
