/-
Axiom audit for the whole project.

Run after `lake build`:

    lake env lean scripts/Axioms.lean

Every theorem of the project may depend only on `propext`, `Classical.choice`,
`Quot.sound` and the per-use `_native.*.ax_N` axioms that `Lean.Meta.nativeEqTrue`
introduces for native evaluation of the checker. Anything else (in particular
`sorryAx`) fails the run with a nonzero exit code.
-/
import VeriPB

open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `nativeEqTrue` axioms are named `_private.<Module>.0._native.<cmd>.ax_N` or
`<thm>._native.native_decide.ax_N`. -/
def isNative (ax : Name) : Bool :=
  ax.components.contains `_native

def isAllowed (ax : Name) : Bool :=
  allowed.contains ax || isNative ax

def isProjectModule (m : Name) : Bool :=
  m.getRoot == `VeriPB || m == `VeriPBKernel

run_cmd do
  let env ← getEnv
  let mut theorems := 0
  let mut native := 0
  let mut bad : Array (Name × Name) := #[]
  for (modName, modData) in env.header.moduleNames.zip env.header.moduleData do
    unless isProjectModule modName do continue
    for c in modData.constNames do
      match env.find? c with
      | some (.thmInfo _) =>
        theorems := theorems + 1
        let axs ← collectAxioms c
        for ax in axs do
          if isNative ax then native := native + 1
          unless isAllowed ax do bad := bad.push (c, ax)
      | _ => pure ()
  logInfo m!"axiom audit: {theorems} theorems, {native} nativeEqTrue uses, {bad.size} disallowed axioms"
  unless bad.isEmpty do
    throwError m!"disallowed axioms: {bad.toList}"
