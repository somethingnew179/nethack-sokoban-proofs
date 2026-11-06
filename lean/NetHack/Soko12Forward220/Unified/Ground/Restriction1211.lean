import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1211_0_checked : (List.range' 620032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1211_1_checked : (List.range' 620160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1211_2_checked : (List.range' 620288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1211_3_checked : (List.range' 620416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1211_range (index : Nat) (lower : 620032 ≤ index) (upper : index < 620544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 620288 then
    if cut : index < 620160 then
      exact segment_sound _ 620032 128 Restriction1211_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 620160 128 Restriction1211_1_checked index (by omega) (by omega)
  else
    if cut : index < 620416 then
      exact segment_sound _ 620288 128 Restriction1211_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 620416 128 Restriction1211_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
