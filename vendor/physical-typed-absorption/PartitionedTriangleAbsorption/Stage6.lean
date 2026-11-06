/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Stage5
public import PartitionedTriangleAbsorption.RefinerAssembly
public import PartitionedTriangleAbsorption.ReserveBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! The universal composition contract is closed. Existence of a bounded
physical refiner and its private absorbers remains open. -/
