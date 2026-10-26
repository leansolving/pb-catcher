/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.Reflect

/-!
Checker-only timing of `checkProofBool` (parse + check, and parse alone) on
the Paley decision proofs (`paley/`), and of `proofClaim?` on the Paley
optimization proofs (`paley_mis/`, `conclusion BOUNDS`; the claim is printed). The checker modules are precompiled, so this must be
run with the checker library loaded, exactly as `lake build` does; otherwise
the checker runs in the IR interpreter (about 20x slower):

    lake env lean --load-dynlib=.lake/build/lib/libveripb_VeriPBReflect.dylib \
      applications/timing.lean

(`.so` on Linux). `applications/benchmark.py` measures the end-to-end
`veripb_reflect` command, which adds Lean startup, the compilation of the
constraint array inside `nativeEqTrue`, and the kernel check.
-/

namespace VeriPB.Timing

/-- Opaque barrier: keeps the compiler from sinking a pure computation past
the surrounding timestamps. -/
@[noinline] def force (b : Bool) : IO Bool := pure b
@[noinline] def forceN (n : Nat) : IO Nat := pure n

def timeOne (p : Nat) : IO Unit := do
  let opbStr ← IO.FS.readFile s!"applications/paley/Paley_{p}.opb"
  let proofStr ← IO.FS.readFile s!"applications/paley/Paley_{p}_kernel.pbp"
  let (numVars, constrs) ← match VeriPB.parseOPB opbStr with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let t0 ← IO.monoMsNow
  let ok ← force (VeriPB.Reflect.checkProofBool constrs numVars [] [] proofStr)
  let t1 ← IO.monoMsNow
  let n ← forceN (match VeriPB.parseVeriPBProof proofStr with
    | .ok d => d.steps.size | .error _ => 0)
  let t2 ← IO.monoMsNow
  IO.println s!"Paley({p}): {n} steps, checkProofBool = {ok} in {t1 - t0} ms \
    (parse alone {t2 - t1} ms)"

@[noinline] def forceC (c : Option VeriPB.Reflect.Claim) :
    IO (Option VeriPB.Reflect.Claim) := pure c

def showClaim : Option VeriPB.Reflect.Claim → String
  | some .unsat => "unsat"
  | some .sat => "sat"
  | some (.bounds lb ub) =>
    let b : Option Int → String := fun | none => "INF" | some v => toString v
    s!"bounds [{b lb}, {b ub}]"
  | none => "none (rejected)"

def timeOneMis (p : Nat) : IO Unit := do
  let opbStr ← IO.FS.readFile s!"applications/paley_mis/Paley_{p}_mis.opb"
  let proofStr ← IO.FS.readFile s!"applications/paley_mis/Paley_{p}_mis_kernel.pbp"
  let inst ← match VeriPB.parseOPBNamed opbStr with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let (obj, off) := match inst.objective with
    | some o => (o.terms, o.offset) | none => ([], 0)
  let t0 ← IO.monoMsNow
  let c ← forceC (VeriPB.Reflect.proofClaim? inst.constrs inst.numVars obj off
    inst.names proofStr)
  let t1 ← IO.monoMsNow
  let n ← forceN (match VeriPB.parseVeriPBProofWith
      (VeriPB.VarTable.ofList inst.names inst.numVars) proofStr with
    | .ok d => d.steps.size | .error _ => 0)
  let t2 ← IO.monoMsNow
  IO.println s!"Paley({p}) MIS: {n} steps, proofClaim? = {showClaim c} in {t1 - t0} ms \
    (parse alone {t2 - t1} ms)"

end VeriPB.Timing

#eval show IO Unit from do
  for p in [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101] do
    VeriPB.Timing.timeOne p

#eval show IO Unit from do
  for p in [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101] do
    VeriPB.Timing.timeOneMis p
