import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1036_0_checked : (List.range' 530432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1036_1_checked : (List.range' 530560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1036_2_checked : (List.range' 530688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1036_3_checked : (List.range' 530816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1036_range (index : Nat) (lower : 530432 ≤ index) (upper : index < 530944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 530688 then
    if cut : index < 530560 then
      exact segment_sound _ 530432 128 Restriction1036_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 530560 128 Restriction1036_1_checked index (by omega) (by omega)
  else
    if cut : index < 530816 then
      exact segment_sound _ 530688 128 Restriction1036_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 530816 128 Restriction1036_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
