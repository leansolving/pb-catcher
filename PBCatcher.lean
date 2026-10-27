/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
-- Kernel + Tests
import PBCatcherKernel

-- Applications (trusted encodings)
import PBCatcher.IndependentSet
import PBCatcher.Langford
import PBCatcher.Schur
import PBCatcher.VanDerWaerden
import PBCatcher.Ramsey
import PBCatcher.EquitableColoring
import PBCatcher.BinPacking
import PBCatcher.VertexCover
import PBCatcher.Chromatic

/-!
# VeriPB: Verified Pseudo-Boolean Proof Checking

This is the root import file for the VeriPB library, which provides
kernel-verified checking of VeriPB pseudo-Boolean proofs in Lean 4.
-/
