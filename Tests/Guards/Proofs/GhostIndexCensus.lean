/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Production.StreamAccum

/-!
# The ghost-index census (DOCS item 331)

Row 12's two open forks (items 320 and 325) were both priced as a choice between
widening a park's alternative with a proof-side disjunct and restating a field.
Read together they are one question: **which indices of the accumulation
invariant are proof-side data standing in for scanner state?**  That is the
question Blueprint Rule 8 answers for the future, and this file counts for the
present.

## The classes

Every binder the invariant's carriers introduce — a parameter, an index, a
constructor field, or a quantifier inside a field's statement — is one of:

| class | what it is | ghost? |
|---|---|---|
| `surface` | a `SurfPos`, or a predicate on positions | no — the correspondence is the theorem |
| `state` | the `ScannerState` the carrier is about | no |
| `prop` | a `Prop` binder — a continuation, a route, a fact about the state | no — obligations are the induction hypothesis |
| `scalar` | a `Nat`, `Int`, `Bool`, `Char`, context, token array … | not counted as ghost here: most are grammar parameters (`n`, `c`) or pinned to the state by an inequality |
| `snapshot` | an `Option ScannerState` — a whole scanner state carried as an index | **yes** |
| `ghost` | a `List Nat` (the frame lists and value-line chains), an `Array Bool` (the kinds and the key mask), a `FrameTail` | **yes** unless pinned to a projection of the state |

The last two columns are the rule's subject.  A snapshot or a ghost datum
either (a) is proved equal to a projection `f sc` of the live state — the kinds
index already is (`sc.flowStack`, 9b(i)) — or (b) names state the scanner does
not have, in which case the scanner is incomplete and the field is added to
`ScannerState` (item 299's `docStartLine`, item 48's `explicitKeyCol`, the
`definedAnchors` argument in DOCS.md).  What the rule forbids is the third
option the two forks offered: a new proof-side disjunct or index carried beside
the data the scanner already holds.

## What the census is and is not

It is a reading of TYPES, taken from the environment: the carriers' telescopes,
their constructors' fields, and every `∃`/`∀` binder inside those fields'
statements (that is where the `List Nat` chains live — `∃ ns : List Nat, ∀ nv ∈
ns, …`).  It does not read proofs, and it does not decide which ghost row is a
projection and which is a missing field: that is each row's own item, priced by
a probe (item 325's `1001`/`1002` pattern).  The pin below is the list to shrink;
a row leaves it when its carrier is re-indexed by a projection or a field, and
nothing may join it (Rule 8).
-/

namespace Tests.Guards.GhostIndexCensus

set_option autoImplicit false

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs L4YAML.Proofs.StreamAccum

/-! ## §1  The instrument -/

inductive Class where
  | surface | state | prop | scalar | snapshot | ghost
deriving BEq, Repr, Inhabited, DecidableEq

def Class.key : Class → String
  | .surface => "surface" | .state => "state" | .prop => "prop"
  | .scalar => "scalar" | .snapshot => "snapshot" | .ghost => "ghost"

/-- One binder, where it stands. -/
structure Row where
  carrier : String
  site : String
  name : String
  ty : String
  cls : Class
deriving Inhabited

/-- The class of a binder TYPE. -/
def classify (t : Expr) : MetaM Class := do
  let t ← instantiateMVars t
  if t.isSort then return .scalar
  if ← isProp t then return .prop
  if t.isForall then
    return ← forallTelescope t fun xs b => do
      let onPos ← xs.allM fun x => do pure ((← inferType x).isConstOf ``SurfPos)
      if (← isProp b) && onPos then pure .surface else pure .scalar
  match t.getAppFn.constName? with
  | some ``SurfPos => return .surface
  | some ``ScannerState => return .state
  | some ``Option =>
      if t.getAppNumArgs == 1 && t.appArg!.isConstOf ``ScannerState then return .snapshot
      else return .scalar
  | some ``List =>
      if t.getAppNumArgs == 1 && t.appArg!.isConstOf ``Nat then return .ghost else return .scalar
  | some ``Array =>
      if t.getAppNumArgs == 1 && t.appArg!.isConstOf ``Bool then return .ghost else return .scalar
  | some ``FrameTail => return .ghost
  | _ => return .scalar

def shown (n : Name) : String :=
  let n := n.eraseMacroScopes
  if n.isAnonymous then "_" else n.toString

/-- Walk a statement, recording every binder it introduces: `∀`, `∃`, and the
    lambdas a matcher alternative binds.  A `Prop` binder's own type is walked
    too — that is where a field's `∃ ns : List Nat` sits. -/
partial def walk (carrier site : String) : Expr → StateT (Array Row) MetaM Unit
  | e => do
    let e := e.consumeMData
    match e with
    | .forallE n t b bi => do
        let c ← classify t
        modify (·.push { carrier, site, name := shown n, ty := toString (← ppExpr t), cls := c })
        if c == .prop then walk carrier site t
        withLocalDecl n bi t fun x => walk carrier site (b.instantiate1 x)
    | .lam n t b bi => do
        let c ← classify t
        modify (·.push { carrier, site, name := shown n, ty := toString (← ppExpr t), cls := c })
        withLocalDecl n bi t fun x => walk carrier site (b.instantiate1 x)
    | .letE _ _ v b _ => do walk carrier site v; walk carrier site b
    | .proj _ _ s => walk carrier site s
    | .app .. =>
        if e.isAppOfArity ``Exists 2 then
          match e.appArg! with
          | .lam n t b bi => do
              let c ← classify t
              modify (·.push { carrier, site, name := shown n, ty := toString (← ppExpr t), cls := c })
              withLocalDecl n bi t fun x => walk carrier site (b.instantiate1 x)
          | lam => walk carrier site lam
        else
          e.withApp fun f args => do
            if f.isLambda then walk carrier site f
            for a in args do walk carrier site a
    | _ => pure ()

/-- Every binder of one carrier: its type's telescope (`type`), each
    constructor's fields past the shared parameters (the constructor's name),
    or a definition's body (`body`). -/
def carrierRows (c : Name) : MetaM (Array Row) := do
  let env ← getEnv
  let some ci := env.find? c | throwError "the census names no constant {c}"
  let carrier := c.getString!
  let (_, rows) ← (do
    walk carrier "type" ci.type
    match ci with
    | .inductInfo ind =>
        for ctor in ind.ctors do
          let some cci := env.find? ctor | continue
          forallBoundedTelescope cci.type (some ind.numParams) fun _ body =>
            walk carrier ctor.getString! body
    | .defnInfo d =>
        forallTelescope d.type fun xs _ => do
          let body := (d.value.beta xs).headBeta
          walk carrier "body" body
    | _ => pure ()).run #[]
  return rows

/-- The carriers: every type the accumulation invariant is stated with, from
    `PendingNode` and the flow stacks down to the packs' own predicates. -/
def carriers : List Name :=
  [ ``PendingNode, ``FlowStackB, ``FlowOpenStack, ``FlowStackK, ``FlowBaseRoutes,
    ``FlowBaseAnchor, ``GateOf, ``ParkCore, ``ParkAnchor, ``ParkSlot, ``ParkChoice,
    ``ParkFloor, ``KmSound, ``KeyFloor, ``FlowOpenHeld, ``RestoreLayout, ``InteriorGap,
    ``SeqFrame, ``MapFrame, ``ResumeFrames, ``KeyFrames, ``ExplValueLine, ``SeqEntryTail,
    ``ImplicitKeyPack, ``PropsKeyPack, ``KeyPackPunt, ``ExplicitValueRefused, ``PackAlt,
    ``PackAltG, ``BareLandingFacts, ``L4YAML.Proofs.CouplingBridge.ScannerSurfCorr ]

def tallyLine (carrier : String) (rows : Array Row) : String :=
  let count (k : Class) := (rows.filter (·.cls == k)).size
  s!"{carrier}: surface={count .surface} state={count .state} prop={count .prop} \
scalar={count .scalar} snapshot={count .snapshot} ghost={count .ghost}"

def ghostLine (r : Row) : String := s!"{r.carrier}.{r.site} {r.name} : {r.ty}"

/-! ## §2  The pins

Regenerated from the guard's own output; a change is recorded with a dated note
like every other census in this directory.  `expectedGhost` is Rule 8's list:
it may only shrink. -/

/-- 31 carriers, 9 snapshot indices and 68 ghost data binders on 2026-10-21
    (item 331), the day the census was taken — Rule 8's baseline. -/
def expectedSummary : String := "carriers=31 snapshot=9 ghost=68"

def expectedTally : List String :=
  [ "PendingNode: surface=122 state=1 prop=235 scalar=58 snapshot=0 ghost=22",
    "FlowStackB: surface=6 state=0 prop=1 scalar=4 snapshot=1 ghost=7",
    "FlowOpenStack: surface=31 state=0 prop=28 scalar=9 snapshot=1 ghost=11",
    "FlowStackK: surface=5 state=1 prop=4 scalar=3 snapshot=1 ghost=3",
    "FlowBaseRoutes: surface=21 state=0 prop=26 scalar=8 snapshot=1 ghost=4",
    "FlowBaseAnchor: surface=0 state=5 prop=0 scalar=4 snapshot=2 ghost=0",
    "GateOf: surface=0 state=1 prop=0 scalar=1 snapshot=2 ghost=0",
    "ParkCore: surface=0 state=2 prop=5 scalar=6 snapshot=0 ghost=1",
    "ParkAnchor: surface=0 state=2 prop=3 scalar=4 snapshot=0 ghost=0",
    "ParkSlot: surface=0 state=2 prop=3 scalar=7 snapshot=0 ghost=0",
    "ParkChoice: surface=0 state=2 prop=0 scalar=1 snapshot=0 ghost=0",
    "ParkFloor: surface=0 state=2 prop=4 scalar=4 snapshot=0 ghost=0",
    "KmSound: surface=0 state=1 prop=9 scalar=21 snapshot=0 ghost=3",
    "KeyFloor: surface=0 state=0 prop=1 scalar=7 snapshot=0 ghost=0",
    "FlowOpenHeld: surface=0 state=0 prop=0 scalar=3 snapshot=0 ghost=2",
    "RestoreLayout: surface=0 state=1 prop=0 scalar=4 snapshot=0 ghost=0",
    "InteriorGap: surface=3 state=1 prop=14 scalar=7 snapshot=0 ghost=1",
    "SeqFrame: surface=40 state=0 prop=30 scalar=2 snapshot=0 ghost=1",
    "MapFrame: surface=40 state=0 prop=30 scalar=2 snapshot=0 ghost=1",
    "ResumeFrames: surface=4 state=0 prop=5 scalar=3 snapshot=0 ghost=2",
    "KeyFrames: surface=6 state=0 prop=9 scalar=5 snapshot=0 ghost=3",
    "ExplValueLine: surface=5 state=0 prop=3 scalar=1 snapshot=0 ghost=0",
    "SeqEntryTail: surface=3 state=0 prop=1 scalar=1 snapshot=0 ghost=0",
    "ImplicitKeyPack: surface=16 state=1 prop=16 scalar=9 snapshot=0 ghost=4",
    "PropsKeyPack: surface=13 state=1 prop=13 scalar=7 snapshot=0 ghost=3",
    "KeyPackPunt: surface=0 state=1 prop=9 scalar=0 snapshot=0 ghost=0",
    "ExplicitValueRefused: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0",
    "PackAlt: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0",
    "PackAltG: surface=0 state=0 prop=0 scalar=0 snapshot=1 ghost=0",
    "BareLandingFacts: surface=0 state=2 prop=0 scalar=1 snapshot=0 ghost=0",
    "ScannerSurfCorr: surface=1 state=1 prop=7 scalar=4 snapshot=0 ghost=0" ]

/-- The list to shrink.  Read with the header's caveat: `FlowOpenHeld`'s `S` (and
    `ParkCore`'s, which holds it) is a list of TOKEN INDICES, a projection of
    `tokens` already; `KmSound.body xs` is the array the mask's `[i]` reads.  The
    rest are the frame lists, the value-line chains, the kinds and the mask, the
    frame tail, and the open-time snapshot `g`. -/
def expectedGhost : List String :=
  [ "PendingNode.pendingContent ns : List Nat",
    "PendingNode.pendingContent ks : List Nat",
    "PendingNode.pendingContent ks : List Nat",
    "PendingNode.pendingContent ks : List Nat",
    "PendingNode.pendingProps ns : List Nat",
    "PendingNode.pendingProps ks : List Nat",
    "PendingNode.pendingProps ks : List Nat",
    "PendingNode.pendingProps ks : List Nat",
    "PendingNode.pendingProps ks : List Nat",
    "PendingNode.pendingBlockContent ks : List Nat",
    "PendingNode.pendingBlockContent ns : List Nat",
    "PendingNode.pendingBlockContent ks : List Nat",
    "PendingNode.pendingBlock ks : List Nat",
    "PendingNode.pendingBlock ns : List Nat",
    "PendingNode.pendingBlock ks : List Nat",
    "PendingNode.pendingMapValue ns : List Nat",
    "PendingNode.pendingMapValue ks : List Nat",
    "PendingNode.pendingMapValue ks : List Nat",
    "PendingNode.pendingMapValue ks : List Nat",
    "PendingNode.pendingMapValue ks : List Nat",
    "PendingNode.pendingMapValue ks : List Nat",
    "PendingNode.pendingMapValue ns : List Nat",
    "FlowStackB.type g : Option ScannerState",
    "FlowStackB.type a : Array Bool",
    "FlowStackB.type a : Array Bool",
    "FlowStackB.type a : FrameTail",
    "FlowStackB.nil tl : FrameTail",
    "FlowStackB.open ks : Array Bool",
    "FlowStackB.open km : Array Bool",
    "FlowStackB.open tl : FrameTail",
    "FlowOpenStack.type g : Option ScannerState",
    "FlowOpenStack.type a : Array Bool",
    "FlowOpenStack.type a : Array Bool",
    "FlowOpenStack.type a : FrameTail",
    "FlowOpenStack.seqBase tl : FrameTail",
    "FlowOpenStack.mapBase tl : FrameTail",
    "FlowOpenStack.seqNest ks : Array Bool",
    "FlowOpenStack.seqNest km : Array Bool",
    "FlowOpenStack.seqNest tl : FrameTail",
    "FlowOpenStack.mapNest ks : Array Bool",
    "FlowOpenStack.mapNest km : Array Bool",
    "FlowOpenStack.mapNest tl : FrameTail",
    "FlowStackK.type ks : Array Bool",
    "FlowStackK.type tl : FrameTail",
    "FlowStackK.body km : Array Bool",
    "FlowStackK.body g : Option ScannerState",
    "FlowBaseRoutes.type g : Option ScannerState",
    "FlowBaseRoutes.mk ns : List Nat",
    "FlowBaseRoutes.mk ks : List Nat",
    "FlowBaseRoutes.mk ks : List Nat",
    "FlowBaseRoutes.mk ns : List Nat",
    "FlowBaseAnchor.type a : Option ScannerState",
    "FlowBaseAnchor.body x : Option ScannerState",
    "GateOf.type a : Option ScannerState",
    "GateOf.body x : Option ScannerState",
    "ParkCore.mk S : List Nat",
    "KmSound.type km : Array Bool",
    "KmSound.body xs : Array Bool",
    "KmSound.body xs : Array Bool",
    "FlowOpenHeld.type S : List Nat",
    "FlowOpenHeld.body T : List Nat",
    "InteriorGap.type tl : FrameTail",
    "SeqFrame.type a : FrameTail",
    "MapFrame.type a : FrameTail",
    "ResumeFrames.type a : List Nat",
    "ResumeFrames.level ks : List Nat",
    "KeyFrames.type a : List Nat",
    "KeyFrames.mapLevel ks : List Nat",
    "KeyFrames.seqLevel ks : List Nat",
    "ImplicitKeyPack.body ns : List Nat",
    "ImplicitKeyPack.body ks : List Nat",
    "ImplicitKeyPack.body ks : List Nat",
    "ImplicitKeyPack.body ks : List Nat",
    "PropsKeyPack.body ns : List Nat",
    "PropsKeyPack.body ks : List Nat",
    "PropsKeyPack.body ks : List Nat",
    "PackAltG.type _g : Option ScannerState" ]

run_cmd liftTermElabM do
  let mut tally : Array String := #[]
  let mut ghost : Array String := #[]
  let mut nSnap := 0
  let mut nGhost := 0
  for c in carriers do
    let rows ← carrierRows c
    tally := tally.push (tallyLine c.getString! rows)
    for r in rows do
      if r.cls == .snapshot || r.cls == .ghost then
        ghost := ghost.push (ghostLine r)
        if r.cls == .snapshot then nSnap := nSnap + 1 else nGhost := nGhost + 1
  let summary := s!"carriers={carriers.length} snapshot={nSnap} ghost={nGhost}"
  -- One report for all three pins, so a re-pin round reads everything at once.
  let mut moved : Array String := #[]
  if summary != expectedSummary then
    moved := moved.push s!"the ghost-index SUMMARY moved.\nexpected: {expectedSummary}\ngot:      {summary}"
  if tally.toList != expectedTally then
    moved := moved.push s!"the per-carrier TALLY moved.\ngot:\n{
      String.intercalate "\n" tally.toList}"
  if ghost.toList != expectedGhost then
    moved := moved.push s!"Rule 8's GHOST LIST moved.\nexpected ({expectedGhost.length}), got ({ghost.size}):\n{
      String.intercalate "\n" ghost.toList}"
  unless moved.isEmpty do
    throwError (String.intercalate "\n\n" moved.toList)

end Tests.Guards.GhostIndexCensus
