/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.ReflectFast
import VeriPB.Tactic.Sat.Tests.Normalize

/-!
# Fast constraint operations: exactness test

The fast checker (`VeriPB.Reflect.Fast`) keeps structural knowledge about
each constraint (`FConstr.split`: a normalized block, or two blocks) and
uses it to pick cheaper exact normalization paths. This test applies random
sequences of the pol operations (add, multiply, divide, saturate, weaken,
the cuts `c`/`n`/`m`, negate, normalize) to random constraints, once through the fast
`FConstr` operations and once through the verified `Constr` operations with
the verbatim reference normalizer from `Tests/Normalize.lean`, and requires
identical results (terms in order and degree) after every operation. It
also compares the verified and the fast `rup` check on random databases
(`runRup`), checks the cuts `k c`, `k n`, `k m` for soundness by brute force
(`runCuts`), and checks their results against CakePB and VeriPB on the
cases of `Tests/data/polcut/parity.tsv` (`runParity`).
-/

namespace VeriPB.Tests.FastConstr

open Sat.PB VeriPB.Reflect.Fast VeriPB.Tests.Normalize

/-- Reference: the verified data-level operations, with the verbatim copy of
the verified normalizer. -/
def refNormalize (c : Constr) : Constr := normalizeConstrRef c

def refNegate (c : Constr) : Constr := c.negate

/-- A random operation applied to a pair (fast, reference); `pool` supplies
operands for `add`. Weakening (like division and saturation) normalizes
first, as in the checkers; the variable may be absent from the constraint
or have a coefficient above the degree. -/
def step (r : Rng) (pool : Array (Constr × FConstr)) (f : FConstr) (c : Constr) :
    Option (FConstr × Constr) × Rng := Id.run do
  let (op, r1) := r.below 10
  let mut r := r1
  match op with
  | 0 =>
    let (k, r2) := r.below pool.size; r := r2
    let (pc, pf) := pool[k]!
    return (some (addFConstrs f pf, VeriPB.addConstrs c pc), r)
  | 1 =>
    let (k, r2) := r.below 4; r := r2
    return (some (mulFConstr f k, VeriPB.mulConstr c k), r)
  | 2 =>
    let (k, r2) := r.below 3; r := r2
    let k := k + 1
    return (some (divFConstr (normalizeFConstr f) k,
      VeriPB.divConstr (refNormalize c) k), r)
  | 3 =>
    return (some (saturateFConstr (normalizeFConstr f),
      VeriPB.saturateConstr (refNormalize c)), r)
  | 4 =>
    let (v, r2) := r.below 5; r := r2
    return (some (weakenFConstr (normalizeFConstr f) v,
      VeriPB.weakenConstr (refNormalize c) v), r)
  | 5 =>
    return (some (f.negate, refNegate c), r)
  | 7 | 8 | 9 =>
    let (k, r2) := r.below 5; r := r2
    let k := k + 1
    let nf := normalizeFConstr f
    let nc := refNormalize c
    if op == 7 then return (some (cgDivFConstr nf k, Sat.PB.cgDivConstr nc k), r)
    else if op == 8 then return (some (mirFConstr nf k, Sat.PB.mirConstr nc k), r)
    else return (some (mirVarFConstr nf k, Sat.PB.mirVarConstr nc k), r)
  | _ =>
    return (some (normalizeFConstr f, refNormalize c), r)

def runSeq (seed : UInt64) (rounds len : Nat) : IO Unit := do
  let mut r : Rng := ⟨seed⟩
  let mut checked := 0
  for _ in [:rounds] do
    -- a pool of random constraints, some normalized (blocks), some raw
    let mut pool : Array (Constr × FConstr) := #[]
    for k in [:4] do
      let (c, r') := randConstr r 3 4 6 6
      r := r'
      let f := toFConstr c
      if k % 2 == 0 then pool := pool.push (c, f)
      else pool := pool.push (refNormalize c, normalizeFConstr f)
    let (c0, r0) := randConstr r 3 4 6 6
    r := r0
    let mut f := toFConstr c0
    let mut c := c0
    for _ in [:len] do
      let (res, r') := step r pool f c
      r := r'
      match res with
      | none => pure ()
      | some (f', c') =>
        f := f'
        c := c'
        checked := checked + 1
        if !eqConstr (fromFConstr f) c then
          throw <| IO.userError
            s!"fast/verified mismatch (seed {seed}): fast {repr (fromFConstr f)} \
              (split {f.split}), verified {repr c}"
        -- the structural flag must be truthful
        if f.split > f.coeffs.size then
          throw <| IO.userError
            s!"split {f.split} exceeds size (seed {seed}): {repr (fromFConstr f)}"
        if f.split != 0 && f.split != f.coeffs.size then
          if !(isBlock (f.coeffs.extract 0 f.split) (f.lits.extract 0 f.split) &&
              isBlock (f.coeffs.extract f.split f.coeffs.size)
                (f.lits.extract f.split f.lits.size)) then
            throw <| IO.userError s!"two-block flag wrong (seed {seed}): {repr (fromFConstr f)}"
        else if f.split != 0 && !isBlock f.coeffs f.lits then
          throw <| IO.userError s!"block flag wrong (seed {seed}): {repr (fromFConstr f)}"
  IO.println s!"fast constraint ops: seed {seed}, {checked} operations OK"

/-- Random `rup` checks: a random database (raw constraints with repeated
literals, complementary pairs and zero coefficients), a random target and
random hints (ids, `~` at any position and possibly repeated, unknown ids,
or none). The verified `verifyRupBool` and the fast `verifyFRupBool` must
agree (`numVars`, unused by both, varies). Soundness: every accepted target
is checked by brute force (each valuation satisfying the whole database
satisfies the target). Completeness control: a target of degree `0` with
`~` among resolvable hints must be accepted (its negation conflicts when the
pass reaches it); this case must occur. The count of brute-force implied
targets is printed next to the accepted count (one pass over the given hints
accepts far fewer). -/
def runRup (seed : UInt64) (rounds : Nat) : IO Unit := do
  let mut r : Rng := ⟨seed⟩
  let mut acc := 0
  let mut implied := 0
  let mut deg0 := 0
  let nv := 5
  for _ in [:rounds] do
    let (m, r1) := r.below 6; r := r1
    let mut db : Std.HashMap Nat Constr := {}
    let mut fdb : Std.HashMap Nat FConstr := {}
    for i in [:m + 1] do
      let (c, r') := randConstr r nv 3 4 4
      r := r'
      db := db.insert (i + 1) c
      fdb := fdb.insert (i + 1) (toFConstr c)
    let (t, r2) := randConstr r nv 3 3 3; r := r2
    let (nh, r3) := r.below 6; r := r3
    let mut hints : List VeriPB.RupHint := []
    for _ in [:nh] do
      let (k, r') := r.below (m + 3); r := r'
      hints := (if k == 0 then .negC else .id k) :: hints
    let (nvSel, r4) := r.below 3; r := r4
    let numVars := if nvSel == 0 then 2 else nv
    let ok := VeriPB.Reflect.verifyRupBool (VeriPB.Reflect.rupNegate t) hints db numVars
    let okF := verifyFRupBool (rupNegateF (toFConstr t)) hints fdb numVars
    if ok != okF then
      throw <| IO.userError s!"rup mismatch (seed {seed}): verified {ok}, fast {okF}, \
        target {repr t}, hints {hints.length}, db {repr db.toList}"
    let hasNeg := hints.any fun h => match h with | .negC => true | .id _ => false
    let resolvable := hints.all fun h => match h with
      | .negC => true
      | .id k => db.contains k
    if t.degree == 0 && hasNeg && resolvable then
      deg0 := deg0 + 1
      if !ok then
        throw <| IO.userError s!"incomplete rup (seed {seed}): degree-0 target \
          {repr t} with `~` rejected"
    let mut isImplied := true
    for bits in [:2 ^ nv] do
      let v : Valuation := fun i => (bits >>> i) % 2 == 1
      let sat (c : Constr) : Bool := decide (c.degree ≤ evalSum v c.terms)
      if db.toList.all (fun (_, c) => sat c) && !sat t then
        isImplied := false
    if isImplied then implied := implied + 1
    if ok then
      acc := acc + 1
      if !isImplied then
        throw <| IO.userError s!"unsound rup (seed {seed}): target {repr t}"
  if deg0 == 0 then
    throw <| IO.userError s!"rup completeness control never hit (seed {seed})"
  IO.println s!"rup propagation: seed {seed}, {rounds} checks, {acc} accepted, \
    {implied} implied (brute force), {deg0} degree-0 controls accepted, \
    verified = fast, accepted targets implied"

/-- The `pol` cuts `k c`, `k n`, `k m` through the verified executor
(`execPolRPNBool`) and the fast one (`execFPolRPNBool`) on random raw
constraints (repeated literals, complementary pairs, zero coefficients;
both executors normalize first). The two must agree, and every result must
be implied by its operand: each valuation of the variables satisfying the
operand satisfies the result (brute force). `k = 0` must be rejected by both. -/
def runCuts (seed : UInt64) (rounds : Nat) : IO Unit := do
  let mut r : Rng := ⟨seed⟩
  let nv := 5
  let mut nonTrivial := 0
  for _ in [:rounds] do
    let (c, r1) := randConstr r nv 9 20 6; r := r1
    let (k0, r2) := r.below 9; r := r2
    let (opSel, r3) := r.below 3; r := r3
    let op : VeriPB.PolOp :=
      if opSel == 0 then .divVar else if opSel == 1 then .mir else .mirVar
    let db : Std.HashMap Nat Constr := ({} : Std.HashMap Nat Constr).insert 1 c
    let fdb : Std.HashMap Nat FConstr := ({} : Std.HashMap Nat FConstr).insert 1 (toFConstr c)
    -- k = 0 is rejected
    if (VeriPB.Reflect.execPolRPNBool [.pushId 1, .pushNat 0, op] db).isSome ||
        (execFPolRPNBool [.pushId 1, .pushNat 0, op] fdb).isSome then
      throw <| IO.userError s!"cut with k = 0 accepted (seed {seed})"
    let ops : List VeriPB.PolOp := [.pushId 1, .pushNat (k0 + 1), op]
    match VeriPB.Reflect.execPolRPNBool ops db, execFPolRPNBool ops fdb with
    | some rc, some fc =>
      if !eqConstr rc (fromFConstr fc) then
        throw <| IO.userError s!"cut mismatch (seed {seed}, k {k0 + 1}, {repr op}): \
          operand {repr c}, verified {repr rc}, fast {repr (fromFConstr fc)}"
      for bits in [:2 ^ nv] do
        let v : Valuation := fun i => (bits >>> i) % 2 == 1
        if c.degree ≤ evalSum v c.terms && !(rc.degree ≤ evalSum v rc.terms) then
          throw <| IO.userError s!"unsound cut (seed {seed}, k {k0 + 1}, {repr op}): \
            operand {repr c}, result {repr rc}"
      if rc.degree > 0 then nonTrivial := nonTrivial + 1
    | _, _ => throw <| IO.userError s!"cut rejected (seed {seed}): {repr c}"
  IO.println s!"pol cuts c/n/m: seed {seed}, {rounds} cuts, verified = fast, all implied \
    (brute force), {nonTrivial} with positive degree"

/-- Parse `a1 v1 a2 v2 ...` (`v > 0`: `x_v`, `v < 0`: `~x_v`, 1-based). -/
def parseTerms (s : String) : Except String (List Term) := do
  let toks := (s.splitOn " ").filter (· != "")
  let rec go : List String → Except String (List Term)
    | [] => pure []
    | a :: v :: rest => do
      let some a := a.toNat? | throw s!"bad coefficient {a}"
      let some v := v.toInt? | throw s!"bad literal {v}"
      let lit : Literal := if v > 0 then .pos (v.toNat - 1) else .neg ((-v).toNat - 1)
      return (a, lit) :: (← go rest)
    | [x] => throw s!"dangling token {x}"
  go toks

/-- The cases of `Tests/data/polcut/parity.tsv`: random normalized constraints
and divisors whose results under `k c`, `k n`, `k m` were computed from
CakePB's definitions (`var_divide`, `mir`, `var_mir`) and validated by
VeriPB 3.0.1 and CakePB with an exact equality step (`e`); see
`testcampaign/t3b/parity.py`. The verified and the fast executor must give
exactly these terms in this order, with CakePB's integer degree truncated
at `0`. -/
def runParity (path : String) : IO Unit := do
  let txt ← IO.FS.readFile path
  let mut n := 0
  let mut clamped := 0
  for line in txt.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let fail (msg : String) : IO Unit := throw (IO.userError s!"parity {line}: {msg}")
    match line.splitOn " ; " with
    | [opk, ts, d, ets, ed] =>
      let (op, k) ← match opk.splitOn " " with
        | [o, k] =>
          let op : Option VeriPB.PolOp :=
            if o == "c" then some .divVar else if o == "n" then some .mir
            else if o == "m" then some .mirVar else none
          match op, k.toNat? with
          | some op, some k => pure (op, k)
          | _, _ => throw (IO.userError s!"parity: bad operator {opk}")
        | _ => throw (IO.userError s!"parity: bad operator {opk}")
      let (some d, some ed) := (d.toNat?, ed.toInt?)
        | throw (IO.userError s!"parity: bad degree in {line}")
      let (.ok ts, .ok ets) := (parseTerms ts, parseTerms ets)
        | throw (IO.userError s!"parity: bad terms in {line}")
      let c : Constr := ⟨ts, d⟩
      let expected : Constr := ⟨ets, ed.toNat⟩
      if ed < 0 then clamped := clamped + 1
      let db : Std.HashMap Nat Constr := ({} : Std.HashMap Nat Constr).insert 1 c
      let fdb : Std.HashMap Nat FConstr := ({} : Std.HashMap Nat FConstr).insert 1 (toFConstr c)
      let ops : List VeriPB.PolOp := [.pushId 1, .pushNat k, op]
      match VeriPB.Reflect.execPolRPNBool ops db, execFPolRPNBool ops fdb with
      | some rc, some fc =>
        if !eqConstr rc expected then fail s!"verified {repr rc}"
        if !eqConstr (fromFConstr fc) expected then fail s!"fast {repr (fromFConstr fc)}"
        if !eqConstr (VeriPB.normalizeConstr rc) rc then fail "result not normalized"
      | _, _ => fail "rejected"
      n := n + 1
    | _ => fail "malformed line"
  if n == 0 then throw (IO.userError s!"parity: no cases in {path}")
  IO.println s!"pol cuts c/n/m: {n} reference cases equal to CakePB/VeriPB \
    ({clamped} with a negative CakePB degree, truncated to 0)"

end VeriPB.Tests.FastConstr

open VeriPB.Tests.FastConstr in
#eval show IO Unit from do
  runSeq 11 800 12
  runSeq 12 800 20
  runSeq 13 500 30
  runRup 21 20000
  runRup 22 20000
  runCuts 31 10000
  runCuts 32 10000
  runParity "VeriPB/Tactic/Sat/Tests/data/polcut/parity.tsv"
