import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2344_0_checked : (List.range' 1200128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2344_1_checked : (List.range' 1200256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2344_2_checked : (List.range' 1200384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2344_3_checked : (List.range' 1200512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2344_range (index : Nat) (lower : 1200128 ≤ index) (upper : index < 1200640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1200384 then
    if cut : index < 1200256 then
      exact segment_sound _ 1200128 128 Restriction2344_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1200256 128 Restriction2344_1_checked index (by omega) (by omega)
  else
    if cut : index < 1200512 then
      exact segment_sound _ 1200384 128 Restriction2344_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1200512 128 Restriction2344_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
