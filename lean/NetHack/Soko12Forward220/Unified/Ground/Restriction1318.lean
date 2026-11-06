import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1318_0_checked : (List.range' 674816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1318_1_checked : (List.range' 674944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1318_2_checked : (List.range' 675072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1318_3_checked : (List.range' 675200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1318_range (index : Nat) (lower : 674816 ≤ index) (upper : index < 675328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 675072 then
    if cut : index < 674944 then
      exact segment_sound _ 674816 128 Restriction1318_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 674944 128 Restriction1318_1_checked index (by omega) (by omega)
  else
    if cut : index < 675200 then
      exact segment_sound _ 675072 128 Restriction1318_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 675200 128 Restriction1318_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
