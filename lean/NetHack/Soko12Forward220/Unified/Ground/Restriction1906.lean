import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1906_0_checked : (List.range' 975872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1906_1_checked : (List.range' 976000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1906_2_checked : (List.range' 976128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1906_3_checked : (List.range' 976256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1906_range (index : Nat) (lower : 975872 ≤ index) (upper : index < 976384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 976128 then
    if cut : index < 976000 then
      exact segment_sound _ 975872 128 Restriction1906_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 976000 128 Restriction1906_1_checked index (by omega) (by omega)
  else
    if cut : index < 976256 then
      exact segment_sound _ 976128 128 Restriction1906_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 976256 128 Restriction1906_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
