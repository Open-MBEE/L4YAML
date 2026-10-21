/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Spec.Types
public import L4YAML.Token.Token
public import L4YAML.Scanner.Scanner
public import L4YAML.Parser.IndexedComposition
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section Blanket

/-!
# Parser Security: Limits and Tag Validation

  YAML 1.2.2 §3.1 — Processes: The Load step (Parse + Compose) must be
  safe against adversarial input.  This module implements configurable
  limits that prevent:

  1. **Denial-of-Service (DoS)**: Billion-laugh alias expansion,
     excessive nesting, oversized scalars/collections.
  2. **Arbitrary Code Execution (ACE)**: Language-specific tags
     (`!!python/object`, `!!ruby/object`, etc.) that downstream
     consumers might deserialize unsafely.

  ## Usage

  ```lean
  -- Safe mode (recommended for untrusted input):
  parseYamlSafe input                -- default limits
  parseYamlSafe input .strict        -- strict limits

  -- Unlimited mode (backward-compatible, trusted input only):
  parseYaml input                    -- unchanged, no limits
  ```

  See `DOCS.md` ("Security limits and tag validation") for threat model
  and design rationale.
-/


namespace L4YAML

/-! ## Limit Configuration Types -/

/-- Limits on alias (anchor/`*ref`) resolution.
    Prevents billion-laugh exponential expansion and cyclic references. -/
structure AliasLimits where
  /-- Maximum depth of alias resolution chains.
      Example: `a: &a *b, b: &b *c, c: "x"` → depth 3.
      Default: 50 -/
  maxAliasDepth : Nat := 50
  /-- Maximum total alias substitution steps per document.
      Each `.alias` → value replacement counts as one.
      Default: 10,000 -/
  maxAliasExpansions : Nat := 10_000
  /-- Maximum total nodes in the resolved tree.
      Default: 100,000 -/
  maxResolvedNodes : Nat := 100_000
  /-- Detect and reject cyclic aliases (`a: &a [*a]`).
      This is a policy of ours, not a spec requirement: YAML 1.2.2 §3.2.1
      explicitly permits cycles in the representation graph ("Note that the
      YAML graph may include cycles"). What forces a *presented* graph to be
      acyclic is §7.1, which resolves an alias to the "most recent preceding
      node" — so a cycle is unreachable from a stream, but not from the graph
      a program builds and asks us to serialize.
      Default: true -/
  rejectCycles : Bool := true
  deriving Repr, BEq, Inhabited

/-- Limits on tree structure (depth, collection sizes, scalar sizes). -/
structure StructuralLimits where
  /-- Maximum nesting depth of collections.
      Default: 100 -/
  maxDepth : Nat := 100
  /-- Maximum elements in a single sequence.
      Default: 100,000 -/
  maxSequenceLength : Nat := 100_000
  /-- Maximum key-value pairs in a single mapping.
      Default: 100,000 -/
  maxMappingSize : Nat := 100_000
  /-- Maximum scalar value length in bytes.
      Default: 10 MB -/
  maxScalarBytes : Nat := 10_485_760
  /-- Maximum total nodes across all documents.
      Default: 1,000,000 -/
  maxTotalNodes : Nat := 1_000_000
  deriving Repr, BEq, Inhabited

/-- Limits on the document stream. -/
structure DocumentLimits where
  /-- Maximum documents in a stream.
      Default: 100 -/
  maxDocuments : Nat := 100
  /-- Maximum anchors per document.
      Default: 10,000 -/
  maxAnchors : Nat := 10_000
  /-- Maximum input size in bytes.
      Default: 100 MB -/
  maxInputBytes : Nat := 104_857_600
  deriving Repr, BEq, Inhabited

/-- Tag validation policy. -/
inductive TagPolicy where
  /-- Accept all tags (**UNSAFE** — only for trusted input). -/
  | allowAll
  /-- Reject all explicit tags; only implicit typing allowed. -/
  | rejectAll
  /-- Only accept tags in the `allowed` list. -/
  | whitelist (allowed : List String)
  /-- Reject tags whose prefix matches the `forbidden` list. -/
  | blacklist (forbidden : List String)
  /-- Only YAML 1.2 Core Schema tags. -/
  | coreSchemaOnly
  deriving Repr, BEq, Inhabited

/-- Tag security limits. -/
structure TagLimits where
  /-- Tag validation policy.  Default: `coreSchemaOnly`. -/
  policy : TagPolicy := .coreSchemaOnly
  /-- Reject language-specific tags (`!!python/*`, etc.).
      Default: true -/
  rejectLanguageTags : Bool := true
  /-- Maximum tag string length in bytes.  Default: 1024 -/
  maxTagLength : Nat := 1_024
  /-- Maximum unique tags per document.  Default: 100 -/
  maxUniqueTags : Nat := 100
  /-- Reject custom `%TAG` handles.  Default: false -/
  rejectCustomHandles : Bool := false
  /-- Maximum `%TAG` handle prefix length in bytes.  Default: 256 -/
  maxHandlePrefixLength : Nat := 256
  deriving Repr, BEq, Inhabited

/-- Combined parser limits. -/
structure ParserLimits where
  alias : AliasLimits := {}
  structural : StructuralLimits := {}
  document : DocumentLimits := {}
  tag : TagLimits := {}
  /-- Master switch — `false` disables all checks.  Default: true -/
  enabled : Bool := true
  deriving Repr, BEq, Inhabited

namespace ParserLimits

/-- Conservative limits for untrusted input (web APIs, user uploads). -/
def strict : ParserLimits := {
  alias := { maxAliasDepth := 20, maxAliasExpansions := 1_000,
             maxResolvedNodes := 10_000 }
  structural := { maxDepth := 50, maxSequenceLength := 10_000,
                  maxMappingSize := 10_000, maxScalarBytes := 1_048_576,
                  maxTotalNodes := 100_000 }
  document := { maxDocuments := 10, maxAnchors := 1_000,
                maxInputBytes := 10_485_760 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 256, maxUniqueTags := 20,
           rejectCustomHandles := true }
}

/-- Permissive limits for trusted internal use. -/
def permissive : ParserLimits := {
  alias := { maxAliasDepth := 500, maxAliasExpansions := 1_000_000,
             maxResolvedNodes := 10_000_000 }
  structural := { maxDepth := 1000, maxSequenceLength := 10_000_000,
                  maxMappingSize := 10_000_000, maxScalarBytes := 1_073_741_824,
                  maxTotalNodes := 100_000_000 }
  document := { maxDocuments := 10_000, maxAnchors := 1_000_000,
                maxInputBytes := 10_737_418_240 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 1024, maxUniqueTags := 1000,
           rejectCustomHandles := false }
}

/-- All checks disabled.  **Do not use with untrusted input.** -/
def unlimited : ParserLimits := { enabled := false }

/-- No resource limits but strict tag validation. -/
def safeTagsOnly : ParserLimits := {
  enabled := true
  alias := { maxAliasDepth := 10_000, maxAliasExpansions := 10_000_000,
             maxResolvedNodes := 100_000_000, rejectCycles := true }
  structural := { maxDepth := 10_000, maxSequenceLength := 100_000_000,
                  maxMappingSize := 100_000_000, maxScalarBytes := 10_737_418_240,
                  maxTotalNodes := 1_000_000_000 }
  document := { maxDocuments := 100_000, maxAnchors := 10_000_000,
                maxInputBytes := 10_737_418_240 }
  tag := { policy := .coreSchemaOnly, rejectLanguageTags := true,
           maxTagLength := 256, maxUniqueTags := 100,
           rejectCustomHandles := true }
}

end ParserLimits

/-! ## Error Types -/

/-- Errors during alias resolution. -/
inductive AliasLimitError where
  | cyclicAlias (name : String) (path : List String)
  | depthExceeded (depth : Nat) (limit : Nat) (aliasName : String)
  | expansionCountExceeded (count : Nat) (limit : Nat)
  | nodeCountExceeded (count : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

def AliasLimitError.toString : AliasLimitError → String
  | .cyclicAlias name path =>
    s!"Cyclic alias detected: '{name}' (resolution path: {" → ".intercalate path})"
  | .depthExceeded depth limit aliasName =>
    s!"Alias resolution depth exceeded: {depth} > {limit} (resolving '{aliasName}')"
  | .expansionCountExceeded count limit =>
    s!"Alias expansion count exceeded: {count} > {limit}"
  | .nodeCountExceeded count limit =>
    s!"Resolved node count exceeded: {count} > {limit}"

instance : ToString AliasLimitError where toString := AliasLimitError.toString

/-- Errors for structural limits. -/
inductive StructuralLimitError where
  | depthExceeded (depth : Nat) (limit : Nat) (path : YamlPath)
  | sequenceTooLarge (length : Nat) (limit : Nat) (path : YamlPath)
  | mappingTooLarge (size : Nat) (limit : Nat) (path : YamlPath)
  | scalarTooLarge (bytes : Nat) (limit : Nat) (path : YamlPath)
  | totalNodesExceeded (count : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

def pathToString (path : YamlPath) : String :=
  if path.size == 0 then "root"
  else path.foldl (fun acc seg =>
    match seg with
    | .index i => s!"{acc}[{i}]"
    | .key k => s!"{acc}.{k}") ""

def StructuralLimitError.toString : StructuralLimitError → String
  | .depthExceeded depth limit path =>
    s!"Nesting depth exceeded: {depth} > {limit} at {pathToString path}"
  | .sequenceTooLarge length limit path =>
    s!"Sequence too large: {length} elements > {limit} at {pathToString path}"
  | .mappingTooLarge size limit path =>
    s!"Mapping too large: {size} pairs > {limit} at {pathToString path}"
  | .scalarTooLarge bytes limit path =>
    s!"Scalar too large: {bytes} bytes > {limit} at {pathToString path}"
  | .totalNodesExceeded count limit =>
    s!"Total node count exceeded: {count} > {limit}"

instance : ToString StructuralLimitError where toString := StructuralLimitError.toString

/-- Errors for document-level limits. -/
inductive DocumentLimitError where
  | tooManyDocuments (count : Nat) (limit : Nat)
  | tooManyAnchors (count : Nat) (limit : Nat) (docIndex : Nat)
  | inputTooLarge (bytes : Nat) (limit : Nat)
  deriving Repr, BEq, Inhabited

def DocumentLimitError.toString : DocumentLimitError → String
  | .tooManyDocuments count limit =>
    s!"Too many documents in stream: {count} > {limit}"
  | .tooManyAnchors count limit docIndex =>
    s!"Too many anchors in document {docIndex}: {count} > {limit}"
  | .inputTooLarge bytes limit =>
    s!"Input too large: {bytes} bytes > {limit}"

instance : ToString DocumentLimitError where toString := DocumentLimitError.toString

/-- Tag security errors — may indicate an attack attempt. -/
inductive TagSecurityError where
  | forbiddenTag (tag : String) (reason : String)
  | dangerousLanguageTag (tag : String) (language : String)
  | tagTooLong (bytes : Nat) (limit : Nat) (tag : String)
  | tooManyUniqueTags (count : Nat) (limit : Nat)
  | customHandleRejected (handle : String) (tagPrefix : String)
  | handlePrefixTooLong (bytes : Nat) (limit : Nat) (tagPrefix : String)
  | nonCoreSchemaTag (tag : String)
  deriving Repr, BEq, Inhabited

def TagSecurityError.extractLanguage (tag : String) : String :=
  if tag.startsWith "tag:yaml.org,2002:python/" || tag.startsWith "!!python/" then "Python"
  else if tag.startsWith "tag:yaml.org,2002:java/" || tag.startsWith "!!java/" then "Java"
  else if tag.startsWith "tag:yaml.org,2002:ruby/" || tag.startsWith "!!ruby/" then "Ruby"
  else if tag.startsWith "tag:yaml.org,2002:php/" || tag.startsWith "!!php/" then "PHP"
  else if tag.startsWith "tag:yaml.org,2002:perl/" || tag.startsWith "!!perl/" then "Perl"
  else "unknown"

def TagSecurityError.toString : TagSecurityError → String
  | .forbiddenTag tag reason =>
    s!"SECURITY: Forbidden tag '{tag}': {reason}"
  | .dangerousLanguageTag tag language =>
    s!"SECURITY: Dangerous {language} tag '{tag}' — potential code execution"
  | .tagTooLong bytes limit tag =>
    s!"SECURITY: Tag too long: {bytes} bytes > {limit} (tag: {tag.take 50}…)"
  | .tooManyUniqueTags count limit =>
    s!"SECURITY: Too many unique tags: {count} > {limit}"
  | .customHandleRejected handle tagPrefix =>
    s!"SECURITY: Custom tag handle rejected: {handle} → {tagPrefix}"
  | .handlePrefixTooLong bytes limit tagPrefix =>
    s!"SECURITY: Tag handle prefix too long: {bytes} bytes > {limit} (prefix: {tagPrefix.take 50}…)"
  | .nonCoreSchemaTag tag =>
    s!"SECURITY: Non-Core-Schema tag '{tag}'"

instance : ToString TagSecurityError where toString := TagSecurityError.toString

/-- Top-level error for all limit violations. -/
inductive LimitError where
  | aliasLimit (err : AliasLimitError)
  | structuralLimit (err : StructuralLimitError)
  | documentLimit (err : DocumentLimitError)
  | tagSecurity (err : TagSecurityError)
  deriving Repr, BEq, Inhabited

def LimitError.toString : LimitError → String
  | .aliasLimit err => s!"Alias limit violation: {err}"
  | .structuralLimit err => s!"Structural limit violation: {err}"
  | .documentLimit err => s!"Document limit violation: {err}"
  | .tagSecurity err => s!"{err}"

instance : ToString LimitError where toString := LimitError.toString

/-- Unified parse error: syntax errors *or* limit violations. -/
inductive ParseError where
  | scanError (err : ScanError)
  | limitError (err : LimitError)
  deriving Repr, BEq, Inhabited

def ParseError.toString : ParseError → String
  | .scanError err => s!"{err}"
  | .limitError err => s!"{err}"

instance : ToString ParseError where toString := ParseError.toString

/-! ## Tag Validation -/

/-- YAML 1.2 Core Schema safe tags (both full URI and shorthand forms). -/
def coreSchemaWhitelist : List String :=
  [ "tag:yaml.org,2002:str",   "!!str"
  , "tag:yaml.org,2002:int",   "!!int"
  , "tag:yaml.org,2002:float", "!!float"
  , "tag:yaml.org,2002:bool",  "!!bool"
  , "tag:yaml.org,2002:null",  "!!null"
  , "tag:yaml.org,2002:seq",   "!!seq"
  , "tag:yaml.org,2002:map",   "!!map"
  , "tag:yaml.org,2002:binary", "!!binary"
  , "tag:yaml.org,2002:timestamp", "!!timestamp"
  ]

/-- Known dangerous tag prefixes (language-specific deserialization). -/
def dangerousTagPrefixes : List String :=
  [ "tag:yaml.org,2002:python/", "!!python/"
  , "tag:yaml.org,2002:java/",   "!!java/"
  , "tag:yaml.org,2002:ruby/",   "!!ruby/"
  , "tag:yaml.org,2002:php/",    "!!php/"
  , "tag:yaml.org,2002:perl/",   "!!perl/"
  ]

/-- Check a single tag against the tag limits.  Returns `unit` or a
    `TagSecurityError`. -/
def validateTag (tag : String) (limits : TagLimits) : Except TagSecurityError Unit := do
  -- Length check
  if tag.utf8ByteSize > limits.maxTagLength then
    throw (.tagTooLong tag.utf8ByteSize limits.maxTagLength tag)
  -- Language-specific tag check
  if limits.rejectLanguageTags then
    if dangerousTagPrefixes.any (fun pfx => tag.startsWith pfx) then
      throw (.dangerousLanguageTag tag (TagSecurityError.extractLanguage tag))
  -- Policy check
  match limits.policy with
  | .allowAll => pure ()
  | .rejectAll => throw (.forbiddenTag tag "all explicit tags rejected")
  | .whitelist allowed =>
    if allowed.contains tag then pure ()
    else throw (.forbiddenTag tag "not in whitelist")
  | .blacklist forbidden =>
    if forbidden.any (fun pfx => tag.startsWith pfx) then
      throw (.forbiddenTag tag "matches blacklist pattern")
    else pure ()
  | .coreSchemaOnly =>
    if coreSchemaWhitelist.contains tag then pure ()
    else throw (.nonCoreSchemaTag tag)

/-- Validate `%TAG` directives against tag limits. -/
def validateDirectives (directives : Array Directive) (limits : TagLimits)
    : Except TagSecurityError Unit := do
  for d in directives do
    match d with
    | .tag handle tagPrefix =>
      if limits.rejectCustomHandles then
        throw (.customHandleRejected handle tagPrefix)
      if tagPrefix.utf8ByteSize > limits.maxHandlePrefixLength then
        throw (.handlePrefixTooLong tagPrefix.utf8ByteSize limits.maxHandlePrefixLength tagPrefix)
    | .yaml _ => pure ()

/-! ## Collecting Tags from a Value Tree -/

/-- Extract the tag from a `YamlValue`, if present. -/
def getNodeTag : YamlValue → Option String
  | .scalar s => s.tag
  | .sequence _ _ tag _ => tag
  | .mapping _ _ tag _ => tag
  | .alias _ => none

/-- Distinct tags seen so far.  `validateTag` runs once per distinct tag, on
    first sight, and `note` fails as soon as the number of distinct tags
    passes `maxUniqueTags` — so a tag-dense document costs O(occurrences)
    hash lookups and never more than `maxUniqueTags + 1` validations. -/
structure TagCensus where
  seen : Std.HashSet String := {}

/-- Record one tag occurrence (a `none` tag is a no-op). -/
def TagCensus.note (c : TagCensus) (tag : Option String) (limits : TagLimits)
    : Except TagSecurityError TagCensus := do
  match tag with
  | none => return c
  | some t =>
    if c.seen.contains t then return c
    let seen := c.seen.insert t
    if seen.size > limits.maxUniqueTags then
      throw (.tooManyUniqueTags seen.size limits.maxUniqueTags)
    validateTag t limits
    return { seen }

/-- Collect all explicit tags in a value tree (unique, first occurrence
    first, document order). -/
partial def collectTags (v : YamlValue) : List String :=
  (go v ({}, #[])).2.toList
where
  go : YamlValue → Std.HashSet String × Array String → Std.HashSet String × Array String
    | .scalar s, acc => noteTag s.tag acc
    | .sequence _ items tag _, acc =>
      items.foldl (fun a item => go item a) (noteTag tag acc)
    | .mapping _ pairs tag _, acc =>
      pairs.foldl (fun a (k, v) => go v (go k a)) (noteTag tag acc)
    | .alias _, acc => acc
  noteTag (tag : Option String) (acc : Std.HashSet String × Array String) :=
    match tag with
    | some t => if acc.1.contains t then acc else (acc.1.insert t, acc.2.push t)
    | none => acc

/-- Validate all tags in a value tree against tag limits, stopping at the
    first offending tag or as soon as `maxUniqueTags` is passed. -/
partial def validateValueTags (v : YamlValue) (limits : TagLimits) : Except TagSecurityError Unit := do
  let _ ← go v {}
where
  go : YamlValue → TagCensus → Except TagSecurityError TagCensus
    | .scalar s, c => c.note s.tag limits
    | .sequence _ items tag _, c => do
      items.foldlM (fun a item => go item a) (← c.note tag limits)
    | .mapping _ pairs tag _, c => do
      pairs.foldlM (fun a (k, v) => do go v (← go k a)) (← c.note tag limits)
    | .alias _, c => return c

/-! ## Structural Validation -/

/-- Count total nodes in a value tree. -/
partial def countNodes (v : YamlValue) : Nat :=
  match v with
  | .scalar _ => 1
  | .sequence _ items _ _ =>
    1 + items.foldl (fun acc item => acc + countNodes item) 0
  | .mapping _ pairs _ _ =>
    1 + pairs.foldl (fun acc (k, v) => acc + countNodes k + countNodes v) 0
  | .alias _ => 1

/-- Count nodes, giving up as soon as the running total passes `cap`
    (the result is then some number above `cap`, not the exact count). -/
partial def countNodesCapped (v : YamlValue) (cap : Nat) (acc : Nat := 0) : Nat :=
  if acc > cap then acc else
  match v with
  | .scalar _ => acc + 1
  | .sequence _ items _ _ =>
    items.foldl (fun a item => countNodesCapped item cap a) (acc + 1)
  | .mapping _ pairs _ _ =>
    pairs.foldl (fun a (k, v) => countNodesCapped v cap (countNodesCapped k cap a)) (acc + 1)
  | .alias _ => acc + 1

/-- Validate structural limits on a resolved value tree and count its nodes
    in the same walk.  The path is threaded as a reversed segment list and
    materialised only for an error. -/
partial def validateStructureCounting (v : YamlValue) (limits : StructuralLimits)
    (path : YamlPath := #[]) (depth : Nat := 0) : Except StructuralLimitError Nat :=
  go v limits path.toList.reverse depth 0
where
  go (v : YamlValue) (limits : StructuralLimits) (rpath : List PathSegment) (depth : Nat)
      (count : Nat) : Except StructuralLimitError Nat := do
    let count := count + 1
    match v with
    | .scalar s =>
      if s.content.utf8ByteSize > limits.maxScalarBytes then
        throw (.scalarTooLarge s.content.utf8ByteSize limits.maxScalarBytes rpath.reverse.toArray)
      return count
    | .sequence _ items _ _ =>
      if depth > limits.maxDepth then
        throw (.depthExceeded depth limits.maxDepth rpath.reverse.toArray)
      if items.size > limits.maxSequenceLength then
        throw (.sequenceTooLarge items.size limits.maxSequenceLength rpath.reverse.toArray)
      let mut count := count
      for h : idx in [:items.size] do
        count ← go items[idx] limits (.index idx :: rpath) (depth + 1) count
      return count
    | .mapping _ pairs _ _ =>
      if depth > limits.maxDepth then
        throw (.depthExceeded depth limits.maxDepth rpath.reverse.toArray)
      if pairs.size > limits.maxMappingSize then
        throw (.mappingTooLarge pairs.size limits.maxMappingSize rpath.reverse.toArray)
      let mut count := count
      for h : idx in [:pairs.size] do
        let (k, v) := pairs[idx]
        let keyStr := match k with | .scalar s => s.content | _ => s!"[{idx}]"
        count ← go k limits (.key keyStr :: rpath) (depth + 1) count
        count ← go v limits (.key keyStr :: rpath) (depth + 1) count
      return count
    | .alias _ => return count

/-- Validate structural limits on a resolved value tree. -/
def validateStructure (v : YamlValue) (limits : StructuralLimits) (path : YamlPath := #[])
    (depth : Nat := 0) : Except StructuralLimitError Unit := do
  let _ ← validateStructureCounting v limits path depth

/-! ## Limited Compose Walk -/

/-- Bindings made so far in document order, anchor name → cleaned value.
    Binding is `insert`, so a lookup answers "most recent preceding
    definition" (§7.1) in O(1). -/
abbrev AnchorEnv := Std.HashMap String YamlValue

/-- One composed node.  `value` has aliases substituted and anchors
    stripped.  `adapted` is `value.adaptForFlowContext` when that differs
    from `value` (some plain scalar below carries a flow indicator) and the
    caller asked for it; `none` means the adapted form *is* `value`, so the
    common case shares one tree instead of building a second. -/
structure ComposedNode where
  value : YamlValue
  adapted : Option YamlValue := none

/-- The flow-adapted form of a composed node. -/
@[inline] def ComposedNode.cleaned (c : ComposedNode) : YamlValue :=
  c.adapted.getD c.value

/-- Counters threaded through the compose walk. -/
structure ComposeState where
  expansions : Nat := 0
  nodeCount : Nat := 0
  tags : TagCensus := {}

/-- Resolve aliases, strip anchors, validate tags and enforce alias limits
    in **one** walk of the value tree.

    Resolution is **order-aware**, mirroring `YamlValue.resolveAliasesOrdered`:
    the walk threads an environment of bindings made so far (bound after the
    node's own content, cleaned like `ParseState.addAnchor`), so each alias
    binds to the most recent *preceding* definition of its anchor name (§7.1).
    Aliases with no preceding in-tree definition fall back to the parse-time
    `anchors` table with the original first-match lookup.

    What used to be separate passes — `countNodes`, `collectTags` on the raw
    and on the resolved tree, `stripAnchors`, and the per-anchored-node
    `stripAnchors.adaptForFlowContext` re-walk — happen here as the nodes are
    built.  A node is visited once; its flow-adapted twin is only
    materialised below an anchor *and* where adaptation changes something.
    Every tag of the raw tree is a tag of the resolved tree, so one census
    covers both.

    Fails with the first limit violation met in document order. -/
partial def composeValueLimited (v : YamlValue) (anchors : Array (String × YamlValue))
    (limits : ParserLimits) : Except LimitError YamlValue := do
  let table : AnchorEnv := anchors.foldl (fun m (n, val) => m.insertIfNew n val) {}
  let (c, _, _) ← go table v 0 [] {} {} false
  return c.value
where
  go (table : AnchorEnv) (v : YamlValue) (depth : Nat) (visiting : List String)
     (st : ComposeState) (env : AnchorEnv) (wantAdapted : Bool)
     : Except LimitError (ComposedNode × ComposeState × AnchorEnv) := do
    let st := { st with nodeCount := st.nodeCount + 1 }
    if st.nodeCount > limits.alias.maxResolvedNodes then
      throw (.aliasLimit (.nodeCountExceeded st.nodeCount limits.alias.maxResolvedNodes))
    match v with
    | .scalar s =>
      let st ← noteTag st s.tag
      let value := if s.anchor.isNone then v else YamlValue.scalar { s with anchor := none }
      let want := wantAdapted || s.anchor.isSome
      let adapted :=
        if want && s.style == .plain && hasFlowIndicator s.content.toList then
          some value.adaptForFlowContext
        else none
      let c : ComposedNode := { value, adapted }
      return (keep c wantAdapted, st, bind env s.anchor c)
    | .sequence style items tag anchor =>
      let mut st ← noteTag st tag
      let mut env := env
      let want := wantAdapted || anchor.isSome
      let mut out : Array YamlValue := Array.mkEmpty items.size
      let mut outAdapted : Option (Array YamlValue) := none
      for item in items do
        let (c, st', env') ← go table item depth visiting st env want
        st := st'
        env := env'
        outAdapted := pushAdapted outAdapted out c
        out := out.push c.value
      let c : ComposedNode := { value := YamlValue.sequence style out tag none
                                adapted := outAdapted.map (YamlValue.sequence style · tag none) }
      return (keep c wantAdapted, st, bind env anchor c)
    | .mapping style pairs tag anchor =>
      let mut st ← noteTag st tag
      let mut env := env
      let want := wantAdapted || anchor.isSome
      let mut out : Array (YamlValue × YamlValue) := Array.mkEmpty pairs.size
      let mut outAdapted : Option (Array (YamlValue × YamlValue)) := none
      for (k, val) in pairs do
        let (ck, st', env') ← go table k depth visiting st env want
        let (cv, st'', env'') ← go table val depth visiting st' env' want
        st := st''
        env := env''
        outAdapted := pushAdaptedPair outAdapted out ck cv
        out := out.push (ck.value, cv.value)
      let c : ComposedNode := { value := YamlValue.mapping style out tag none
                                adapted := outAdapted.map (YamlValue.mapping style · tag none) }
      return (keep c wantAdapted, st, bind env anchor c)
    | .alias name =>
      -- Cycle detection
      if limits.alias.rejectCycles && visiting.contains name then
        throw (.aliasLimit (.cyclicAlias name visiting))
      -- Depth check
      if depth ≥ limits.alias.maxAliasDepth then
        throw (.aliasLimit (.depthExceeded depth limits.alias.maxAliasDepth name))
      -- Expansion count
      let st := { st with expansions := st.expansions + 1 }
      if st.expansions > limits.alias.maxAliasExpansions then
        throw (.aliasLimit (.expansionCountExceeded st.expansions limits.alias.maxAliasExpansions))
      -- Most recent preceding in-tree binding first, then the parse-time
      -- table.  Recursing into the bound value keeps the node-count and
      -- cycle accounting; bindings made inside it are discarded on return.
      match env[name]?.orElse (fun _ => table[name]?) with
      | some val =>
        let (c, st, _) ← go table val (depth + 1) (name :: visiting) st env wantAdapted
        return (c, st, env)
      | none =>
        -- unresolved alias: preserve as-is
        return ({ value := v }, st, env)
  noteTag (st : ComposeState) (tag : Option String) : Except LimitError ComposeState :=
    match tag with
    | none => .ok st
    | some _ =>
      match st.tags.note tag limits.tag with
      | .ok tags => .ok { st with tags }
      | .error e => .error (.tagSecurity e)
  /-- Drop the adapted twin once no anchored ancestor can need it. -/
  keep (c : ComposedNode) (wantAdapted : Bool) : ComposedNode :=
    if wantAdapted then c else { c with adapted := none }
  bind (env : AnchorEnv) (anchor : Option String) (c : ComposedNode) : AnchorEnv :=
    match anchor with
    | some a => env.insert a c.cleaned
    | none => env
  /-- Extend the adapted items, starting a separate array only at the first
      item whose adapted form differs (copying the identical prefix once). -/
  pushAdapted (acc : Option (Array YamlValue)) (prefix_ : Array YamlValue) (c : ComposedNode)
      : Option (Array YamlValue) :=
    match acc, c.adapted with
    | some arr, _ => some (arr.push c.cleaned)
    | none, some a => some (prefix_.push a)
    | none, none => none
  pushAdaptedPair (acc : Option (Array (YamlValue × YamlValue)))
      (prefix_ : Array (YamlValue × YamlValue)) (ck cv : ComposedNode)
      : Option (Array (YamlValue × YamlValue)) :=
    match acc, ck.adapted, cv.adapted with
    | some arr, _, _ => some (arr.push (ck.cleaned, cv.cleaned))
    | none, none, none => none
    | none, _, _ => some (prefix_.push (ck.cleaned, cv.cleaned))

/-! ## Limited Compose -/

/-- Compose a document (resolve aliases + strip anchors) with limit enforcement.

    This is the safe counterpart of `YamlDocument.compose`.  Two walks:
    `composeValueLimited` (alias limits, tag security, anchor stripping) and
    `validateStructureCounting` (structural limits, total node count). -/
def composeLimited (doc : YamlDocument) (limits : ParserLimits) (docIndex : Nat := 0)
    : Except LimitError YamlDocument := do
  if !limits.enabled then
    return { doc with
      value := (doc.value.resolveAliases doc.anchors).stripAnchors
      anchors := #[] }
  -- Anchor count
  if doc.anchors.size > limits.document.maxAnchors then
    throw (.documentLimit (.tooManyAnchors doc.anchors.size limits.document.maxAnchors docIndex))
  -- Anchor value node count (catches billion-laugh expanded during parsing)
  let anchorNodes := doc.anchors.foldl (fun acc (_, v) =>
    countNodesCapped v limits.alias.maxResolvedNodes acc) 0
  if anchorNodes > limits.alias.maxResolvedNodes then
    throw (.aliasLimit (.nodeCountExceeded anchorNodes limits.alias.maxResolvedNodes))
  -- Directive validation (tag handles)
  match validateDirectives doc.directives limits.tag with
  | .ok () => pure ()
  | .error e => throw (.tagSecurity e)
  -- Resolve aliases, strip anchors, validate tags
  let resolved ← composeValueLimited doc.value doc.anchors limits
  -- Structural validation and total node count on the resolved tree
  match validateStructureCounting resolved limits.structural with
  | .ok nodeCount =>
    if nodeCount > limits.structural.maxTotalNodes then
      throw (.structuralLimit (.totalNodesExceeded nodeCount limits.structural.maxTotalNodes))
  | .error e => throw (.structuralLimit e)
  return { doc with value := resolved, anchors := #[] }

/-! ## Safe Parsing API -/

/-- Parse YAML with limit enforcement (**representation graph**).

    This is the safe counterpart of `TokenParser.parseYaml`.  All limit
    categories (input size, document count, alias expansion, structural,
    tag security) are enforced.

    ```lean
    -- Use default limits (suitable for most untrusted input):
    parseYamlSafe input
    -- Use strict limits (web APIs, user uploads):
    parseYamlSafe input .strict
    -- Disable limits (testing only):
    parseYamlSafe input .unlimited
    ``` -/
def parseYamlSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError (Array YamlDocument) := do
  -- Input size check
  if limits.enabled && input.utf8ByteSize > limits.document.maxInputBytes then
    throw (.limitError (.documentLimit (.inputTooLarge input.utf8ByteSize limits.document.maxInputBytes)))
  -- Parse (scan + grammar)
  let docs ← match TokenParser.Indexed.parseYamlRawIx input with
    | .ok docs => pure docs
    | .error e => throw (.scanError e)
  -- Document count check
  if limits.enabled && docs.size > limits.document.maxDocuments then
    throw (.limitError (.documentLimit (.tooManyDocuments docs.size limits.document.maxDocuments)))
  -- Compose each document with limits
  let results ← docs.foldlM (init := (#[] : Array YamlDocument)) fun acc doc =>
    match composeLimited doc limits acc.size with
    | .ok d => pure (acc.push d)
    | .error e => throw (.limitError e)
  return results

/-- Parse YAML expecting one document, with limit enforcement.

    Safe counterpart of `TokenParser.parseYamlSingle`. -/
def parseYamlSingleSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError YamlValue := do
  let docs ← parseYamlSafe input limits
  if docs.size == 0 then return YamlValue.null
  else if docs.size == 1 then return docs[0]!.value
  else throw (.scanError (.multipleDocuments docs.size))

/-- Parse YAML expecting one document, returning the raw document with limits.

    Safe counterpart of `TokenParser.parseYamlSingleRaw`. -/
def parseYamlSingleRawSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError YamlDocument := do
  let docs ← parseYamlSafe input limits
  if docs.size == 0 then return { value := YamlValue.null }
  else if docs.size == 1 then return docs[0]!
  else throw (.scanError (.multipleDocuments docs.size))

end L4YAML

end Blanket
