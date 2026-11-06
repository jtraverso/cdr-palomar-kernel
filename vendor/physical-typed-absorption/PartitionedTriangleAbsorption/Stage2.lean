/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption
public import PartitionedTriangleAbsorption.ReturnedBridge
public import PartitionedTriangleAbsorption.ConeBoundary
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! Verified support and cone-boundary checks. The unfinished absorption
existence theorem is deliberately not imported. -/
