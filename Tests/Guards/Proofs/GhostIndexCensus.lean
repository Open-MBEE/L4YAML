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
| `ghost` | a `List FrameLevel` (the frame lists — a mirror of `sc.indents` until `Covered` is an equality, item 332), a `List Nat` (the value-line chains), an `Array Bool` (the kinds and the key mask), a `FrameTail` | **yes** unless pinned to a projection of the state |

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
      if t.getAppNumArgs == 1 && (t.appArg!.isConstOf ``Nat ||
          t.appArg!.isConstOf ``L4YAML.Proofs.IndentStackCover.FrameLevel) then return .ghost
      else return .scalar
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

/-- The carriers are READ OFF THE ENVIRONMENT, not listed: every `Prop`-valued
    definition, structure or inductive that `StreamAccum` declares (a route, a
    pack, a park, a frame stack, a context such as `ResumeKeyCtx`), plus the
    correspondence from `CouplingBridge`.  Devin Review on the first cut caught
    why a hand list is the wrong instrument: `ResumeKeyCtx` binds `List Nat`
    frame lists and enters the accumulation lemmas through `h_resumectx`, and a
    list that named thirty-one carriers would never have noticed a ghost added to
    it.  Lemmas (`thmInfo`), constructors, recursors, matchers and the other
    generated auxiliaries are excluded; the module's authored `Prop` vocabulary
    is what remains. -/
def extraCarriers : List Name := [ ``L4YAML.Proofs.CouplingBridge.ScannerSurfCorr ]

/-- Does the constant's type end in `Prop` (a predicate, after its parameters)? -/
def endsInProp (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun _ b => pure b.isProp

def carriersOf : MetaM (Array Name) := do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``PendingNode
  let mut out : Array Name := #[]
  for (nm, ci) in env.constants.toList do
    -- Filter on the USER name: the module system privatises generated
    -- auxiliaries, and an authored `private def LocalCtx … : Prop` is mangled
    -- the same way (`_private.<module>.0.<name>`).  Both keep their user name
    -- under `StreamAccum`, so the namespace and the generated-name tests read
    -- `un`; the environment is read at the real `nm`.  (Devin Review's second
    -- finding on PR #26: a `private` predicate must not escape the gate.)
    let un := Lean.privateToUserName nm
    if un.isInternal || un.isInternalDetail then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if env.isProjectionFn nm || isCtorName env nm || isRecCore env nm then continue
    if isAuxRecursor env nm || isNoConfusion env nm || isGenerated un then continue
    if (`L4YAML.Proofs.StreamAccum).isPrefixOf un == false then continue
    match ci with
    | .defnInfo _ | .inductInfo _ =>
        if ← endsInProp ci.type then out := out.push nm
    | _ => pure ()
  let sorted := out.qsort (fun a b => a.toString < b.toString)
  return sorted ++ extraCarriers.toArray
where
  isCtorName (env : Environment) (n : Name) : Bool :=
    match env.find? n with | some (.ctorInfo _) => true | _ => false
  isRecCore (env : Environment) (n : Name) : Bool :=
    match env.find? n with | some (.recInfo _) => true | _ => false
  /-- The structural-recursion and injectivity auxiliaries an inductive
      generates under its own namespace (`X.below`, `X.ibelow`, `X.brecOn`,
      `X.inj`, …): `Prop`-valued, authored by nobody. -/
  isGenerated (n : Name) : Bool :=
    match n with
    | .str _ s => s ∈ ["below", "ibelow", "brecOn", "binductionOn", "casesOn", "recOn",
        "noConfusion", "noConfusionType", "inj", "injEq", "sizeOf_spec", "ctorIdx", "ctorElim"]
    | _ => false

def tallyLine (carrier : String) (rows : Array Row) : String :=
  let count (k : Class) := (rows.filter (·.cls == k)).size
  s!"{carrier}: surface={count .surface} state={count .state} prop={count .prop} \
scalar={count .scalar} snapshot={count .snapshot} ghost={count .ghost}"

def ghostLine (r : Row) : String := s!"{r.carrier}.{r.site} {r.name} : {r.ty}"

/-! ## §2  The pins

Regenerated from the guard's own output; a change is recorded with a dated note
like every other census in this directory.  `expectedGhost` is Rule 8's list:
it may only shrink. -/

/-- 52 carriers, 9 snapshot indices and 73 ghost data binders on
    2026-10-21 (item 331), the day the census was taken — Rule 8's baseline; the
    carriers are every `Prop`-valued declaration of `StreamAccum` (see `carriersOf`). -/
def expectedSummary : String := "carriers=52 snapshot=9 ghost=72"

def expectedTally : List String :=
  [ "BareLandingFacts: surface=0 state=2 prop=0 scalar=1 snapshot=0 ghost=0",
    "BlockStack: surface=2 state=0 prop=0 scalar=0 snapshot=0 ghost=0",
    "CommentStop: surface=0 state=0 prop=0 scalar=1 snapshot=0 ghost=0",
    "CompletedTail: surface=0 state=1 prop=0 scalar=1 snapshot=0 ghost=0",
    "ContentRouteGate: surface=0 state=1 prop=0 scalar=1 snapshot=0 ghost=0",
    "DanglingPred: surface=0 state=0 prop=0 scalar=6 snapshot=0 ghost=0",
    "ExplValueLine: surface=5 state=0 prop=3 scalar=1 snapshot=0 ghost=0",
    "ExplicitValueRefused: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0",
    "FlowBaseAnchor: surface=0 state=5 prop=0 scalar=4 snapshot=2 ghost=0",
    "FlowBaseRoutes: surface=21 state=0 prop=26 scalar=8 snapshot=1 ghost=4",
    "FlowOpenHeld: surface=0 state=0 prop=0 scalar=3 snapshot=0 ghost=2",
    "FlowOpenStack: surface=31 state=0 prop=28 scalar=9 snapshot=1 ghost=11",
    "FlowStack: surface=2 state=0 prop=0 scalar=0 snapshot=0 ghost=0",
    "FlowStackB: surface=6 state=0 prop=1 scalar=4 snapshot=1 ghost=7",
    "FlowStackK: surface=5 state=1 prop=4 scalar=3 snapshot=1 ghost=3",
    "GateOf: surface=0 state=1 prop=0 scalar=1 snapshot=2 ghost=0",
    "ImplicitKeyHead: surface=2 state=0 prop=2 scalar=0 snapshot=0 ghost=0",
    "ImplicitKeyPack: surface=16 state=1 prop=16 scalar=9 snapshot=0 ghost=4",
    "InlineResidue: surface=2 state=0 prop=0 scalar=1 snapshot=0 ghost=0",
    "InteriorGap: surface=3 state=1 prop=14 scalar=7 snapshot=0 ghost=1",
    "KeyFloor: surface=0 state=0 prop=1 scalar=7 snapshot=0 ghost=0",
    "KeyFrames: surface=4 state=0 prop=5 scalar=3 snapshot=0 ghost=2",
    "KeyPackPunt: surface=0 state=1 prop=9 scalar=0 snapshot=0 ghost=0",
    "KmSound: surface=0 state=1 prop=9 scalar=21 snapshot=0 ghost=3",
    "MapFrame: surface=40 state=0 prop=30 scalar=2 snapshot=0 ghost=1",
    "MarkerNodeRoute: surface=4 state=0 prop=1 scalar=0 snapshot=0 ghost=0",
    "OfferPred: surface=0 state=0 prop=0 scalar=4 snapshot=0 ghost=0",
    "OpenSeqEntry: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0",
    "PackAlt: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0",
    "PackAltG: surface=0 state=0 prop=0 scalar=0 snapshot=1 ghost=0",
    "ParkAnchor: surface=0 state=2 prop=3 scalar=4 snapshot=0 ghost=0",
    "ParkChoice: surface=0 state=2 prop=0 scalar=1 snapshot=0 ghost=0",
    "ParkCore: surface=0 state=2 prop=5 scalar=6 snapshot=0 ghost=1",
    "ParkFloor: surface=0 state=2 prop=4 scalar=4 snapshot=0 ghost=0",
    "ParkSlot: surface=0 state=2 prop=3 scalar=7 snapshot=0 ghost=0",
    "PendingNode: surface=122 state=1 prop=235 scalar=58 snapshot=0 ghost=22",
    "PropsKeyPack: surface=13 state=1 prop=13 scalar=7 snapshot=0 ghost=3",
    "PropsNodeRoute: surface=6 state=0 prop=1 scalar=0 snapshot=0 ghost=0",
    "PropsRideRoute: surface=7 state=0 prop=1 scalar=0 snapshot=0 ghost=0",
    "PropsRun: surface=14 state=0 prop=8 scalar=4 snapshot=0 ghost=0",
    "RestoreLayout: surface=0 state=1 prop=0 scalar=4 snapshot=0 ghost=0",
    "ResumeFrames: surface=4 state=0 prop=5 scalar=3 snapshot=0 ghost=2",
    "ResumeKeyCtx: surface=6 state=1 prop=6 scalar=8 snapshot=0 ghost=3",
    "ResumeWidths: surface=0 state=0 prop=0 scalar=2 snapshot=0 ghost=2",
    "SeqEntryTail: surface=3 state=0 prop=1 scalar=1 snapshot=0 ghost=0",
    "SeqFrame: surface=40 state=0 prop=30 scalar=2 snapshot=0 ghost=1",
    "SlotFace: surface=0 state=0 prop=0 scalar=4 snapshot=0 ghost=0",
    "SlotGateAt: surface=0 state=2 prop=7 scalar=1 snapshot=0 ghost=0",
    "StaleNodeTail: surface=0 state=1 prop=0 scalar=1 snapshot=0 ghost=0",
    "StalePark: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0",
    "SuffixRun: surface=4 state=0 prop=0 scalar=0 snapshot=0 ghost=0",
    "ScannerSurfCorr: surface=1 state=1 prop=7 scalar=4 snapshot=0 ghost=0" ]

/-- The list to shrink.  Read with the header's caveat: `FlowOpenHeld`'s `S` (and
    `ParkCore`'s, which holds it) is a list of TOKEN INDICES, a projection of
    `tokens` already; `KmSound.body xs` is the array the mask's `[i]` reads.  The
    rest are the frame lists, the value-line chains, the kinds and the mask, the
    frame tail, and the open-time snapshot `g`. -/
def expectedGhost : List String :=
  [ "FlowBaseAnchor.type a : Option ScannerState",
    "FlowBaseAnchor.body x : Option ScannerState",
    "FlowBaseRoutes.type g : Option ScannerState",
    "FlowBaseRoutes.mk ns : List Nat",
    "FlowBaseRoutes.mk ks : List IndentStackCover.FrameLevel",
    "FlowBaseRoutes.mk ks : List IndentStackCover.FrameLevel",
    "FlowBaseRoutes.mk ns : List Nat",
    "FlowOpenHeld.type S : List Nat",
    "FlowOpenHeld.body T : List Nat",
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
    "FlowStackB.type g : Option ScannerState",
    "FlowStackB.type a : Array Bool",
    "FlowStackB.type a : Array Bool",
    "FlowStackB.type a : FrameTail",
    "FlowStackB.nil tl : FrameTail",
    "FlowStackB.open ks : Array Bool",
    "FlowStackB.open km : Array Bool",
    "FlowStackB.open tl : FrameTail",
    "FlowStackK.type ks : Array Bool",
    "FlowStackK.type tl : FrameTail",
    "FlowStackK.body km : Array Bool",
    "FlowStackK.body g : Option ScannerState",
    "GateOf.type a : Option ScannerState",
    "GateOf.body x : Option ScannerState",
    "ImplicitKeyPack.body ns : List Nat",
    "ImplicitKeyPack.body ks : List IndentStackCover.FrameLevel",
    "ImplicitKeyPack.body ks : List IndentStackCover.FrameLevel",
    "ImplicitKeyPack.body ks : List IndentStackCover.FrameLevel",
    "InteriorGap.type tl : FrameTail",
    "KeyFrames.type a : List IndentStackCover.FrameLevel",
    "KeyFrames.level ks : List IndentStackCover.FrameLevel",
    "KmSound.type km : Array Bool",
    "KmSound.body xs : Array Bool",
    "KmSound.body xs : Array Bool",
    "MapFrame.type a : FrameTail",
    "PackAltG.type _g : Option ScannerState",
    "ParkCore.mk S : List Nat",
    "PendingNode.pendingContent ns : List Nat",
    "PendingNode.pendingContent ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingContent ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingContent ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingProps ns : List Nat",
    "PendingNode.pendingProps ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingProps ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingProps ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingProps ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingBlockContent ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingBlockContent ns : List Nat",
    "PendingNode.pendingBlockContent ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingBlock ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingBlock ns : List Nat",
    "PendingNode.pendingBlock ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue ns : List Nat",
    "PendingNode.pendingMapValue ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue ns : List Nat",
    "PropsKeyPack.body ns : List Nat",
    "PropsKeyPack.body ks : List IndentStackCover.FrameLevel",
    "PropsKeyPack.body ks : List IndentStackCover.FrameLevel",
    "ResumeFrames.type a : List IndentStackCover.FrameLevel",
    "ResumeFrames.level ks : List IndentStackCover.FrameLevel",
    "ResumeKeyCtx.body ks : List IndentStackCover.FrameLevel",
    "ResumeKeyCtx.body ksv : List IndentStackCover.FrameLevel",
    "ResumeKeyCtx.body ksq : List IndentStackCover.FrameLevel",
    "ResumeWidths.type ks : List IndentStackCover.FrameLevel",
    "ResumeWidths.type ks' : List IndentStackCover.FrameLevel",
    "SeqFrame.type a : FrameTail" ]

run_cmd liftTermElabM do
  let mut tally : Array String := #[]
  let mut ghost : Array String := #[]
  let mut nSnap := 0
  let mut nGhost := 0
  let carriers ← carriersOf
  for c in carriers do
    let rows ← carrierRows c
    tally := tally.push (tallyLine c.getString! rows)
    for r in rows do
      if r.cls == .snapshot || r.cls == .ghost then
        ghost := ghost.push (ghostLine r)
        if r.cls == .snapshot then nSnap := nSnap + 1 else nGhost := nGhost + 1
  let summary := s!"carriers={carriers.size} snapshot={nSnap} ghost={nGhost}"
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
