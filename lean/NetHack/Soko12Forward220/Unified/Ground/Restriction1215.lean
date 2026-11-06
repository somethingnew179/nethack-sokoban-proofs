import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1215_0_checked : (List.range' 622080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1215_1_checked : (List.range' 622208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1215_2_checked : (List.range' 622336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1215_3_checked : (List.range' 622464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1215_range (index : Nat) (lower : 622080 ≤ index) (upper : index < 622592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 622336 then
    if cut : index < 622208 then
      exact segment_sound _ 622080 128 Restriction1215_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 622208 128 Restriction1215_1_checked index (by omega) (by omega)
  else
    if cut : index < 622464 then
      exact segment_sound _ 622336 128 Restriction1215_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 622464 128 Restriction1215_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
