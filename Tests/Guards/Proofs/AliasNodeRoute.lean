module

public import L4YAML.Proofs.Parser.ParserGrammableBase
public import L4YAML.Proofs.Parser.ParserScannableBase
public import L4YAML.Proofs.Parser.ParserWfaScannable
public import L4YAML.Proofs.Parser.ParserSoundness
public import L4YAML.Output.Dump
public meta import L4YAML.Output.Dump
public import L4YAML.Output.Emitter
public meta import L4YAML.Output.Emitter
public import L4YAML.Parser.Composition

public meta import L4YAML.Parser.Composition
public meta import L4YAML.Spec.Types
@[expose] public section Blanket

/-!
# `[104] c-ns-alias-node` — the route is inhabited

A definition nothing has instantiated is not yet evidence, so this file spends
the alias route on the one input it exists for: `&x [*x]`, an anchored sequence
whose only item is an alias to its own anchor.  YAML 1.2.2 permits it — §3.2.1.3
legislates the *equality* of a node that "has itself as a descendant (via an
alias)" and nowhere forbids one, and §3.2.2.2 binds an alias to the most recent
*event* carrying the anchor, which the anchored collection's start supplies.

`YamlValue` expresses sharing by substitution and nothing else, so composing
this shape leaves a `.alias` in the result.  `Grammable` has no alias
constructor, so the chain ends in `Scannable` and reaches `ValidNode` through
`scannableValue_has_witness`.  The last lemma below is the conclusion of the
capstone `parseStream_respects_grammar_unconditional`, discharged for this
input.

The `#guard`s record what the runtime does with the same shape today: `compose`
maps the anchored and unanchored trees to the same value, and the style-aware
writer loses the `&x` while keeping the `*x`.  Both are properties of `compose`,
not of the proofs above, and they are what plan row 5a(v)'s load-side edit
addresses.
-/

namespace L4YAML.Tests.Guards.AliasNodeRoute

open L4YAML
open L4YAML.Grammar
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.ParserSoundness
open L4YAML.TokenParser

/-- `&x [*x]` as a document: the self-descendant shape. -/
def boundDoc : YamlDocument := { value := .sequence .flow #[.alias "x"] none (some "x") }

lemma boundDoc_scannable : Scannable boundDoc.value false :=
  .sequence _ _ _ _ _ (fun i => by match i with | ⟨0, _⟩ => exact .alias _ _)

/-- The composed value of `&x [*x]` is `Scannable` — which `Grammable` cannot be,
    since it has no alias constructor.  `compose_scannable` asks nothing about
    the anchor table: resolution reads only the ordered environment (§3.2.2.2). -/
lemma boundDoc_compose_scannable : Scannable boundDoc.compose.value false :=
  compose_scannable boundDoc boundDoc_scannable

/-- **The capstone's own conclusion, for the input the pipeline currently
    refuses**: a `ValidNode` witness for the composed value of `&x [*x]`.

    The `Grammable` route cannot reach this: `compose_grammable` requires
    `AliasFree boundDoc.value`, and this value is not alias-free. -/
lemma boundDoc_has_witness :
    ∃ n : ValidNode,
      stripAnnotations (toYamlValue n) = stripAnnotations boundDoc.compose.value :=
  scannableValue_has_witness _ false boundDoc_compose_scannable

/-! ## What `compose` does with the same shape

`compose` is `(resolveAliasesOrdered …).fst.stripAnchors`, and `stripAnchors`
clears `anchor` on every collection while leaving `.alias` untouched.  So the
binder does not survive and the alias does: the anchored and unanchored trees
compose to the same value, and `Dump` writes an alias naming an anchor the
document no longer declares. -/

/-- `[*x]` — the same tree with no binder at all. -/
def unboundDoc : YamlDocument := { value := .sequence .flow #[.alias "x"] none none }

-- `compose` does not distinguish the bound shape from the unbound one.
#guard boundDoc.compose.value == unboundDoc.compose.value

-- The style-aware writer shows both halves: `&x` before composition, gone
-- after; `*x` throughout.
#guard Dump.dump boundDoc.value == "&x [*x]"
#guard Dump.dump boundDoc.compose.value == "[*x]"

-- The canonical emitter sees neither — it writes no anchor for any value and
-- routes `.alias` through `emitScalar`, which double-quotes unconditionally.
#guard Emit.emit boundDoc.value == "[\"*x\"]"
#guard Emit.emit boundDoc.value == Emit.emit unboundDoc.value

/-! ## §3.2.2.2 resolution, with no whole-document table

`resolveAliasesOrdered` resolves an alias against the ordered environment and
nothing else, which is what §3.2.2.2 specifies: *the most recent preceding
node carrying the anchor*.  The rows below pin that on every legitimate shape
the environment has to cover — an earlier sibling, a completed subtree, a
closed collection, a rebound anchor, a chain, and a second document.

The rebound rows are the ones that distinguish the two readings: a whole-document
first-match lookup answers `"a"` for *both* aliases in `[&x a, *x, &x b, *x]`,
and §3.2.2.2 requires `"b"` for the second. -/

/-- Load `src` and emit each document's composed value, `" | "`-separated. -/
def shot (src : String) : String :=
  match parseYaml src with
  | Except.ok docs =>
      String.intercalate " | " (docs.toList.map (fun d => Emit.emit (d : YamlDocument).value))
  | Except.error e => "ERR " ++ toString (repr e)

-- an earlier sibling in the same collection
#guard shot "[&x a, *x]"            == "[\"a\", \"a\"]"
#guard shot "{a: &x 1, b: *x}"      == "{\"a\": \"1\", \"b\": \"1\"}"
#guard shot "- &x a\n- *x\n"        == "[\"a\", \"a\"]"

-- an anchor inside a subtree that has already closed
#guard shot "[[&x a], *x]"          == "[[\"a\"], \"a\"]"
#guard shot "{k: {j: &x 1}, m: *x}" == "{\"k\": {\"j\": \"1\"}, \"m\": \"1\"}"
#guard shot "- - &x a\n- *x\n"      == "[[\"a\"], \"a\"]"
#guard shot "[{a: &x 1}, [*x]]"     == "[{\"a\": \"1\"}, [\"1\"]]"

-- an anchor on a collection, aliased after it closes
#guard shot "[&x [1,2], *x]"        == "[[\"1\", \"2\"], [\"1\", \"2\"]]"
#guard shot "- &x\n  - 1\n- *x\n"   == "[[\"1\"], [\"1\"]]"
#guard shot "{k: &x {a: 1}, m: *x}" == "{\"k\": {\"a\": \"1\"}, \"m\": {\"a\": \"1\"}}"

-- a rebound anchor: each alias takes the MOST RECENT preceding definition
#guard shot "[&x a, *x, &x b, *x]"  == "[\"a\", \"a\", \"b\", \"b\"]"
#guard shot "- &x 1\n- *x\n- &x 2\n- *x\n" == "[\"1\", \"1\", \"2\", \"2\"]"

-- a chain: one anchor's value is itself reached through another alias
#guard shot "[&a x, &b [*a], *b]"   == "[\"x\", [\"x\"], [\"x\"]]"
#guard shot "{p: &a 1, q: &b [*a], r: *b}" == "{\"p\": \"1\", \"q\": [\"1\"], \"r\": [\"1\"]}"

-- anchor scope is per document (§3.2.2.2)
#guard shot "[&x a, *x]\n---\n[&y b, *y]\n" == "[\"a\", \"a\"] | [\"b\", \"b\"]"

/-! ### §7.1's only error: an anchor that does not previously occur -/

/-- Does loading `src` fail with `undefinedAlias`? -/
def refusesAlias (src : String) : Bool :=
  match parseYaml src with
  | Except.error (.undefinedAlias _ _ _) => true
  | _ => false

#guard refusesAlias "*x\n"            -- bare, nothing declared
#guard refusesAlias "[*x]"            -- inside a flow sequence
#guard refusesAlias "[&y a, *x]"      -- a different anchor is declared
#guard refusesAlias "[*x, &x a]"      -- forward reference: not *preceding*
#guard refusesAlias "*y\n---\n&y b\n" -- the anchor is in a later document


/-! ## The PARSE-side table for the same shape (plan row 20 / step 5a(vi))

The route above is the COMPOSE side.  The parser carries a second table —
`ParseState.anchors`, written by `addAnchor` at node finalization — and
`WellFormedAnchors` asks that every value in it be `Grammable` after stripping.
For this input that is false, and the two lemmas below say why in the two ways
it can be said: `Grammable` has no alias constructor at all, and the
`AllAliasesResolve` premise that `applyNodeFinalization_wfa` takes is false at
the state the parser is actually in when it finalizes `&x` over `[*x]` — the
collection's anchor binds only after its items are resolved, so its own
interior alias never sees it.

`ParserWfaScannable` mirrors that table onto `Scannable`, and the third lemma
spends the mirror on this input: finalizing `&x` over `[*x]` keeps the table
`WellFormedAnchorsS`.  These three are the consumer probe plan row 20 names —
they are what says the remaining parse-side clique is a rename and not a
redesign. -/

/-- `Grammable` has no alias constructor, so no alias node is ever `Grammable`:
    the direct reason `WellFormedAnchors` cannot hold of a table binding
    `[*x]`. -/
lemma alias_not_grammable (name : String) (inFlow : Bool) :
    ¬ Grammable (.alias name) inFlow := by
  intro h; cases h

/-- The table the parser finalizes over does not satisfy `AllAliasesResolve`,
    which is the premise the `Grammable`-valued `applyNodeFinalization_wfa`
    takes.  That route is therefore not merely harder for this input: its
    premise is false. -/
lemma selfDesc_not_aar : ¬ AllAliasesResolve unboundDoc.value #[] := by
  intro h
  cases h with
  | sequence _ _ _ _ _ h_items =>
    have h0 := h_items ⟨0, by simp⟩
    cases h0 with
    | alias _ _ h_find => simp at h_find

/-- …and the value really does still carry the alias after cleaning, which is
    the fact both refusals turn on. -/
example : (unboundDoc.value.resolveAliases #[]).stripAnchors
    = .sequence .flow #[.alias "x"] none none := rfl

/-- `[*x]` is `Scannable` — the mirror's hypothesis, where the original's
    `Grammable` is unavailable. -/
lemma unboundDoc_value_scannable : Scannable unboundDoc.value false :=
  .sequence _ _ _ _ _ (fun i => by match i with | ⟨0, _⟩ => exact .alias _ _)

/-- **The probe row 20 asks for**: finalizing `&x` over `[*x]` keeps the
    parse-side anchor table `WellFormedAnchorsS`.  The `Grammable`-valued
    original cannot be applied here at all — `selfDesc_not_aar` above. -/
lemma selfDesc_finalization_wfaS
    (ps : ParseState) (h : ps.anchors = #[]) (pos : YamlPos) :
    WellFormedAnchorsS
      (applyNodeFinalization unboundDoc.value ps
        { anchor := some "x", tag := none, hadDuplicateAnchor := false } pos).2.anchors :=
  applyNodeFinalization_wfaS unboundDoc.value ps _ pos
    (by intro nm v hf; rw [h] at hf; simp at hf)
    unboundDoc_value_scannable

end L4YAML.Tests.Guards.AliasNodeRoute

end Blanket
