# ezjson: what it guarantees, and how we prove it

## Draft Status

Accepted. Written from `089d520` (v0.4.2) and the law inventory
(`docs/rfc/ezjson-law-inventory.md`), which holds the evidence for every
verdict cited here. The maintainer accepted every recommendation in one
reply; each item below records the decision in place.

REVIEW-1 comes first because the others depend on it.

- [x] <!-- REVIEW-1 (resolved): What is the public surface? Today the README documents `main.bend` and `pull.bend`, but bolt's LSP imports `value.bend`, `parse.bend`, `print.bend` and `lex.bend` directly, matches on the cell constructors (`JCons`, `JSpan`, `JBind`) and calls `J.arr.go`. Recommend: the rows speak about the defs in `main.bend` and the types `Json`, `Pull.Ev` and `Pull.Cur`; every other module is internal and carries no promise; open a bolt issue to move its imports to `main.bend`. Bend has no private constructors, so the cells stay visible, and REVIEW-3 says what the rows assume about them. Not a behavior change. Decided: accepted as recommended. The rows speak about `main.bend`'s defs and the types `Json`, `Pull.Ev` and `Pull.Cur`; every other module is internal. A bolt issue asks bolt's LSP to import `main.bend`. -->
- [x] <!-- REVIEW-2 (resolved): The headline guarantee. Recommend JSON-PRINT-1, "for every well-formed value, `parse(print(j))` is that value". It is what makes ezjson safe as a writer, it ties the printer to the parser, and it is a structural induction we can afford first. JSON-TEXT-1 (accepts exactly the RFC 8259 grammar) is the stronger conformance claim and the costliest proof; it stays pending until the grammar relation exists. JSON-PULL-1 (the cursor agrees with `parse`) is second in priority, because it is what lets a caller move a large text from `parse` to the cursor. Decided: accepted as recommended. JSON-PRINT-1 is the headline; JSON-PULL-1 is second; JSON-TEXT-1 stays pending until the `Derives` relation exists. -->
- [x] <!-- REVIEW-3 (resolved): What is a well-formed value? A value built with the cell constructors directly prints malformed text (`JObj{JCons{..}}` prints `{null}`, `JNil{}` prints nothing, `JNum{"abc"}` prints `abc`), and a string holding a surrogate code point or one above U+10FFFF prints raw, which no UTF-8 JSON text can hold (inventory, "Bugs"). Recommend: add `wf : Json -> Bool` to `value.bend` (arrays are `JCons` chains ending in `JNil`, objects are `JPair`/`JBind` chains ending in `JNil`, `JNum` text passes `num.ok`, no cell at a value position) and state the value rows for well-formed values; and have `print` write U+FFFD for any code point that is not a Unicode scalar value, as Go's `encoding/json` does for invalid UTF-8, so strings need not be part of `wf`. The second half is a behavior change to `print`. Decided: accepted as recommended. `wf` is added to `value.bend` and the value rows assume it; `print` writes U+FFFD for a code point that is not a Unicode scalar value. -->
- [x] <!-- REVIEW-4 (resolved): Repeated keys. `get` returns the first value, for parsed and built objects, and the README says so. serde_json, Go's `encoding/json`, Python's `json` and JavaScript's `JSON.parse` keep the last. RFC 8259 §4 calls behavior with repeated names unpredictable, and RFC 7493 (I-JSON) forbids them. Recommend: keep first. It is documented and released, it stops the search early (the recent perf work cares), and the RFC permits it. JSON-TREE-4 states it. Not a behavior change. Decided: accepted as recommended. `get` keeps the first value of a repeated key. JSON-TREE-4 states it. -->
- [x] <!-- REVIEW-5 (resolved): A missing key and a `null` value both read as `null` through `get`; an index past the end and a `null` element both read as `null` through `at`. serde_json's `get` returns `Option<&Value>`; Jackson has `has`; Python has `in` and `len`. Recommend: keep `get` and `at` as they are, and add `has(j, key) -> Bool` and `len(j) -> U32` (0 for a non-container), each with its own row (JSON-TREE-8, JSON-TREE-9). New behavior, nothing breaks. Decided: accepted as recommended. `get` and `at` are unchanged; `has` and `len` are added (JSON-TREE-8, JSON-TREE-9). -->
- [x] <!-- REVIEW-6 (resolved): `as_f32` of a number outside the F32 range is `inf` or `-inf` (`1e39`, `1e999`, `-1e999`, confirmed), but `main.bend:68`, `value.bend:382` and the README promise none. Recommend: fix the code to return none on overflow, as documented; a number that rounds to zero (`1e-50`) keeps reading as `0`, as serde_json's `as_f64` does. Behavior change, lands as its own PR with master against branch results. Decided: accepted as recommended. `as_f32` returns none when the number overflows F32; an underflow still reads as `0`. -->
- [x] <!-- REVIEW-7 (resolved): `as_u32` reads only a plain digit spelling: `7` and `4294967295` read, `7.0`, `1e2`, `-0` and `4294967296` are none. serde_json's `as_u64` is none for any number it parsed as a float, so this is the convention. Recommend: keep it and state it exactly (JSON-TREE-6). Not a behavior change. Decided: accepted as recommended. `as_u32` keeps reading only a plain digit spelling; JSON-TREE-6 states it exactly. -->
- [x] <!-- REVIEW-8 (resolved): `skip` where no value can start (before an object key, at a close bracket, after the root, on an empty text) fails the cursor. After `next` returns a key, `skip` drops that member's value, which is what .NET's `Utf8JsonReader.Skip` does on a property name. Recommend: keep it; JSON-PULL-5 states the failure. Not a behavior change. Decided: accepted as recommended. `skip` where no value can start fails the cursor; JSON-PULL-5 states it. -->
- [x] <!-- REVIEW-9 (resolved): Semantic equality. A parsed string is `JSpan` and a built one is `JStr`, so Bend's `==` on `Json` is not JSON equality, and there is no `eq`. serde_json's `Value` has `PartialEq`. Recommend: not in this rollout. Define the relation `same` in `LAWS.bend` as a specification helper, because the round-trip rows need it, and decide a public `eq` later (Future Steps). Not a behavior change. Decided: accepted as recommended. No public `eq` in this rollout; `same` is a specification helper in `LAWS.bend`. -->
- [x] <!-- REVIEW-10 (resolved): The cursor's walk has a fuel of 2^32 - 1 word jumps (`pull.bend:1430`) and turns running out into `EErr`. Recommend: keep it, and state the cursor rows for texts shorter than 2^32 characters, which covers every text Bend can hold. The alternative, a walk structural on the suffix, is a rewrite of the hot loop for no observable gain. Not a behavior change. Decided: accepted as recommended. The fuel stays; the cursor rows are stated for texts shorter than 2^32 characters. -->
- [x] <!-- REVIEW-11 (resolved): Retiring the closed laws. All 99 are closed and proved by `{==}`; 42 point toward no requirement. Recommend deleting all 99 in the change that lands SPEC.md, as bolt did, keeping the inventory's "points toward" column as the map. The README's Compliance section is rewritten to point at SPEC.md. Decided: accepted as recommended. All 99 closed laws are deleted in the change that lands SPEC.md. -->
- [x] <!-- REVIEW-12 (resolved): The bolt pin. The flake pins bolt `5b05a1b` (before v0.5.0), which has no `closed`, `coverage` or `trace`, so its `clean` says nothing about laws. bolt v1.4.2 reports 454 errors: 99 closed laws, 105 defs named by no quantified law, 248 short parameter names (99 in `bench/`) and 2 wrapped headers. Recommend: a lint-first PR that moves the pin to bolt v1.4.2 with `laws` at warn and fixes the style findings, then the SPEC.md PR turns `closed` and `trace` to error. Decided: accepted as recommended. A lint-first change moves the pin to bolt v1.4.2 with `laws` at warn; the SPEC.md change turns `closed` and `trace` to error. -->
- [x] <!-- REVIEW-13 (resolved): The README's import line names `0xa3c2445eb44c5d8406e6229be518fccb`; bolt's ledger records v0.4.2 at this commit as `0xd9c8d4d2899ddda845dfa7525a3568ea`. Recommend: check with `ez` against the hub and fix the README in its own docs PR. Decided: accepted as recommended. The README hash is checked with `ez` and fixed in its own change. -->

## Abstract

ezjson has 99 laws. Every one is a closed equality proved by `{==}`, so the
proof gate passing tells us that 99 chosen inputs give the expected output,
and nothing about any other input. A differential run against a strict RFC
8259 reference found no disagreement over 2,266 texts, so the parser is
better than its laws: the problem is that nobody can tell from the gate
what is guaranteed. We propose a SPEC.md with two families of rows, RFC
8259 conformance and the public interface, each row either proved by a
quantified law or named as a trusted assumption, and a rollout that
deletes the closed laws and proves the rows cheapest first.

## Glossary

| Term | Meaning |
| :---- | :---- |
| JSON text | a string that matches RFC 8259's `JSON-text` rule |
| value | a `Json`; well-formed when `wf` holds (REVIEW-3) |
| cell | `JNil`, `JCons`, `JPair`, `JBind`: the links of an array or object, not values themselves |
| span | a string or key held as the first `n` characters of a source suffix (`JSpan`, `JBind`, `EStrS`, `EKeyS`, `ENum`), not a copy |
| cursor | `Pull.Cur`, the pull reader's state: the unread suffix, the open containers, and whether the root ended or failed |
| event | `Pull.Ev`, one thing `next` returns: a scalar, a key, a begin or end of a container, `EEnd` or `EErr` |
| closed law | a law with no `for` or `exs` binder; one example the checker runs |
| quantified law | a law with at least one binder; a statement for every input |
| proof gate | every `PROOF.bend` prints exactly `All terms check.` as its first line |
| Proved | a row backed by quantified laws tagged with its ID; its status is `proved` or `pending` |
| Trusted | a row the gate cannot check, with a reason in the trust table |
| `same` | the specification relation "these two values are the same JSON", ignoring span against owned representation (REVIEW-9) |

## Background

ezjson is JSON for Bend 2: `parse` reads a text into `Maybe<Json>`, `print`
writes compact text, six builders and seven readers work on values, and a
pull cursor (`cursor`, `next`, `skip`, `text`) reads a large text one event
at a time without building a tree. It does no IO. bolt's language server is
its main user.

Today the README's Compliance section lists the RFC 8259 sections that
"closed equalities in `ezjson/LAWS.bend` … check". Each law in the list is
one example, or a short concatenation of examples. Three of them enumerate
every code point from U+0000 to U+001F and are exhaustive over that range;
the rest cover the inputs written in them. The pinned bolt predates the
rules that would say so. Under bolt v1.4.2 every law is reported as closed
and every public def as named by no quantified law.

## Problem Statement

For every behavior, a reader should be able to answer two questions from
SPEC.md alone: is it guaranteed, and is the guarantee proved or assumed?
Today the answer to the first is "the README says so" and to the second
"it holds on the examples".

Goals:

- SPEC.md lists every guarantee, in two families: conformance to RFC 8259,
  and the behavior of each public def.
- Every Proved row has quantified laws tagged with its ID; bolt's `trace`
  checks SPEC.md against the tags at error.
- The closed laws are gone, and `closed` is at error.
- The one bug found (`as_f32`) and the malformed-output cases are fixed or
  ruled out of scope by a row.

Non-goals:

- Performance and memory. The recent work on the cursor is about not
  keeping the unread text alive; a law sees values, not heap shape. That is
  a Trusted row, backed by the `scale` check as an integration check.
- New features beyond `has` and `len` (REVIEW-5).
- Proving Bend's base library (`U32.read`, `F32.read`).

## Proposal

### Two levels, and the positions carried over from ez and bolt

We adopt the positions ez and bolt reached, and state them here so they can
be argued with now:

- Exactly two levels. A Proved row is backed by a quantified law tagged
  with its ID, passing the gate. A Trusted row names what the gate cannot
  check and says why. Pending is a status of a Proved row.
- A closed law has no standing. It is too weak to protect a behavior and
  too strong to let it change.
- A test is never evidence for a row. The differential harness that found
  no disagreement is how we audited the code; it is not committed and is
  not cited by any row.
- Laws only reach values. ezjson has the easy case: every public def is
  already pure, so there is no World and no planner to extract.

### The proof gate

Unchanged: `bend ezjson/PROOF.bend` must print exactly `All terms check.`
as its first line, which `ez.mkProofs` already enforces in `nix flake
check`.

### The interface, against mature JSON libraries

RFC 8259 specifies texts, not an API, so the interface rows are ours to
choose. We checked each def against the libraries most readers know, so the
rows follow convention where one exists and say so where they do not.

| ezjson | serde_json | Jackson | Go `encoding/json` | .NET `System.Text.Json` |
| :---- | :---- | :---- | :---- | :---- |
| `parse` | `from_str::<Value>` | `readTree` | `Unmarshal` into `any` | `JsonNode.Parse` |
| `print` | `to_string` | `writeValueAsString` | `Marshal` | `ToJsonString` |
| `null`, `bool`, `str`, `num`, `arr`, `obj` | `json!`, `Value::*` | `JsonNodeFactory` | literals | `JsonValue.Create` |
| `get` (first of repeated keys, `null` when missing) | `get` (last, `Option`) | `get` (last, `null` when missing) | map index (last) | indexer (parse rejects repeats) |
| `at` | `get(usize)` | `get(int)` | slice index | indexer |
| `as_bool`, `as_str`, `as_num` | `as_bool`, `as_str`, `Number` | `asBoolean`, `textValue` | type switch | `GetValue<T>` |
| `as_u32` (plain digits only) | `as_u64` (none for a float) | `canConvertToInt` | `Number.Int64` | `TryGetValue<uint>` |
| `as_f32` | `as_f64` | `floatValue` | `Number.Float64` | `TryGetValue<float>` |
| `cursor`, `next` | none built in | `JsonParser.nextToken` | `Decoder.Token` | `Utf8JsonReader.Read` |
| `skip` | none | `skipChildren` | none | `Utf8JsonReader.Skip` |
| `text` | none | `getText` | the token | `GetString`, `ValueSpan` |

The pull cursor is not a JSON standard, but it is a standard shape: Jackson,
Go, .NET, JSR 374 (`javax.json.stream`) and simdjson's on-demand API all
have one. ezjson's matches them on the points they agree on: commas and
colons are not events (Go), a string may be a view into the source rather
than a copy (.NET's `ValueSpan`, simdjson), `skip` after a key drops that
member's value (.NET), and the end of input is sticky (Go's repeated
`io.EOF`). It differs on errors: the others throw, and ezjson returns a
sticky `EErr`, since Bend has no exceptions. The rows below state all of it.

Where ezjson departs from the majority (first of repeated keys, `null` for
a missing key), REVIEW-4 and REVIEW-5 ask whether to keep the departure.

### Requirements: RFC 8259 texts

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-TEXT-1 | For texts shorter than 2^32 - 1 characters: `parse(t)` is `Some` exactly when `t` matches RFC 8259's `JSON-text` rule (§2 to §7) and holds no `\u` escape of an unpaired surrogate (§8.2) | Proved | pending | |
| JSON-TEXT-2 | For texts shorter than 2^32 - 1 characters: inserting any run of U+0020, U+0009, U+000A and U+000D before or after any token of a JSON text leaves `parse`'s result the same value; inserting any other character there makes it `None` (§2) | Proved | pending | |
| JSON-TEXT-3 | For texts shorter than 2^32 - 1 characters: for every two well-formed values `j` and `k`, `parse(print(j) ++ " " ++ print(k))` is `None`: a text holds exactly one value (§2) | Proved | pending | |
| JSON-TEXT-4 | For texts shorter than 2^32 - 1 characters: a bare word parses exactly when it is `null`, `true`, `false` or a number, and the literals are only the lowercase words (§3) | Proved | pending | |
| JSON-TEXT-5 | For texts shorter than 2^32 - 1 characters: for every text `t`, `parse` of U+FEFF followed by `t` is `None` (§8.1) | Proved | pending | |

JSON-TEXT-1 is the conformance claim, and its law needs a specification to
compare against. We write the RFC's grammar in `LAWS.bend` as a relation
`Derives(t, j)` ("the text `t` derives the value `j`"), one constructor per
ABNF rule, and prove both directions: `parse(t) == Some{j}` implies
`Derives(t, j)`, and `Derives(t, j)` implies `parse(t)` is `Some` of a
value `same` as `j`. The relation is a transcription of the RFC, not a
second parser, which is what separates it from the abandoned reference
implementation below.

JSON-TEXT-2 to 5 are corollaries once JSON-TEXT-1 lands, but each is
cheaper to prove directly on the lexer, so they land first.

### Requirements: numbers

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-NUM-1 | `num.ok(s)` holds exactly when `s` matches RFC 8259's `number` rule: an optional `-`, `0` or a nonzero digit and digits, an optional `.` and one or more digits, an optional `e` or `E`, an optional sign and one or more digits (§6) | Proved | pending | |
| JSON-NUM-2 | For texts shorter than 2^32 - 1 characters: for every `s` with `num.ok(s)`, `parse(s)` is `Some{JNum{s}}` and `print` of it is `s`: a number keeps its spelling | Proved | pending | |
| JSON-NUM-3 | `num(s)` is `JNum{s}` when `num.ok(s)`, and `null()` otherwise | Proved | pending | |

JSON-NUM-1 is the cheapest real law in the project and the first to land:
`num.ok` is a ten-state DFA, the rule is five lines of ABNF, and the proof is
an induction on the characters.

### Requirements: strings

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-STR-1 | For texts shorter than 2^32 - 1 characters: for every string `s` of Unicode scalar values, `parse(quote(s))` is a string value whose characters are `s` (§7) | Proved | pending | |
| JSON-STR-2 | For texts shorter than 2^32 - 1 characters: inside a string, `\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t` decode to their characters; `\uXXXX` of a non-surrogate decodes to that code point; a high then low surrogate escape decodes to one code point; any other escape, and an unpaired surrogate escape, make `parse` `None` (§7, §8.2) | Proved | pending | |
| JSON-STR-3 | For texts shorter than 2^32 - 1 characters: inside a string, a raw U+0000 to U+001F makes `parse` `None`, and every other raw code point except `"` and `\` is kept as itself (§7) | Proved | pending | |
| JSON-STR-4 | For texts shorter than 2^32 - 1 characters: two object names compare equal in `get` exactly when their decoded characters are equal, whatever escapes spelled them (§8.3) | Proved | pending | |
| JSON-STR-5 | `quote(s)` escapes exactly `"`, `\` and U+0000 to U+001F, using the two-character form where one exists and `\u00xx` otherwise, and writes every other scalar value as itself, and writes U+FFFD for every code point that is not a Unicode scalar value (a surrogate, or past U+10FFFF) (§7, §8.1) | Proved | pending | |

REVIEW-3 decides what `quote` does with a code point that is not a scalar
value. JSON-STR-1 and JSON-STR-5 are stated over scalar values either way.

### Requirements: print and round trip

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-PRINT-1 | For texts shorter than 2^32 - 1 characters: for every well-formed value `j`, `parse(print(j))` is `Some` of a value `same` as `j` with every code point that is not a Unicode scalar value replaced by U+FFFD | Proved | pending | |
| JSON-PRINT-2 | For texts shorter than 2^32 - 1 characters: for every text `t` with `parse(t) == Some{j}`, `print(j)` holds no whitespace outside strings, and `print(j) == print(j2)` where `parse(print(j)) == Some{j2}` | Proved | pending | |
| JSON-PRINT-3 | For every value built only from `null`, `bool`, `str`, `num`, `arr` and `obj`, or returned by `parse`, `wf` holds | Proved | pending | |

JSON-PRINT-1 is the headline (REVIEW-2). Its law, in sketch:

```
# LAW: print then parse is the same value
# JSON-PRINT-1
law print_parse:
  for j: V.Json
  for w: {V.wf(j) == True{} : Bool}
  {same.m(Parse.parse(Print.print(j)), Some{j}) == True{} : Bool}
```

JSON-PRINT-3 is what makes the precondition harmless: nothing a caller can
build through `main.bend` fails it.

### Requirements: the tree interface

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-TREE-1 | `as_bool(bool(b)) == Some{b}`, `as_str(str(s)) == Some{s}`, and `as_num(num(s)) == Some{s}` when `num.ok(s)` | Proved | pending | |
| JSON-TREE-2 | Each of `as_bool`, `as_str`, `as_num`, `as_u32`, `as_f32` is `None` on every value of another kind | Proved | pending | |
| JSON-TREE-3 | `at(arr(xs), i)` is the `i`-th element of `xs` when `i` is less than its length, and `null()` otherwise; `at(j, i)` is `null()` for every `j` that is not an array | Proved | pending | |
| JSON-TREE-4 | `get(obj(ps), k)` is the value of the first pair in `ps` whose key is `k`, and `null()` when there is none; `get(j, k)` is `null()` for every `j` that is not an object | Proved | pending | |
| JSON-TREE-5 | For texts shorter than 2^32 - 1 characters: for every text `t` with `parse(t) == Some{j}`, every reader (`get`, `at`, `as_*`) gives on `j` the result it gives on the owned value `same` as `j`: a span reads as its characters | Proved | pending | |
| JSON-TREE-6 | `as_u32(num(s))` is `Some{n}` exactly when `s` is one or more ASCII digits, with no leading zero unless `s` is `0`, whose value `n` is at most 4294967295 | Proved | pending | |
| JSON-TREE-7 | For every number value whose text is `s`: when `F32.read(s)` is `Some{x}` with `F32.abs(x)` at most 3.4028235e38 (the largest finite F32), `as_f32` is `Some{x}`; when that read is infinite or `None`, `as_f32` is `None` | Proved | pending | |
| JSON-TREE-8 | `has(obj(ps), k)` is true exactly when some pair in `ps` has key `k`, and `has(j, k)` is false for every `j` that is not an object (REVIEW-5) | Proved | pending | |
| JSON-TREE-9 | `len(arr(xs))` is the length of `xs`, `len(obj(ps))` the length of `ps`, and `len(j)` is 0 for every scalar (REVIEW-5) | Proved | pending | |

JSON-TREE-7 depended on a decided behavior change (REVIEW-6), which has
landed: an overflow reads as none. The row is stated over `F32.read`, which
JSON-TRUST-2 trusts. JSON-TREE-8 and 9 depend on new defs. JSON-TREE-4 depends on
REVIEW-4, JSON-TREE-6 on REVIEW-7.

### Requirements: the pull cursor

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-PULL-1 | For every text `t` shorter than 2^32 characters, the events `next` yields from `cursor(t)` end in `EEnd` exactly when `parse(t)` is `Some{j}`, and then they are `events(j)`: the value's scalars, keys and container begins and ends in document order, with no event for a comma or a colon | Proved | pending | |
| JSON-PULL-2 | Once `next` yields `EErr`, every later `next` on the returned cursor yields `EErr`, and `skip` returns a failed cursor | Proved | pending | |
| JSON-PULL-3 | Once `next` yields `EEnd`, every later `next` on the returned cursor yields `EEnd` | Proved | pending | |
| JSON-PULL-4 | For every cursor at a position where a value may start, `next(skip(c))` yields the event that follows that value's last event in the full stream from `c` | Proved | pending | |
| JSON-PULL-5 | `skip` at a position where no value may start (before an object key, at a close bracket, after the root, or on a failed cursor) returns a failed cursor (REVIEW-8) | Proved | pending | |
| JSON-PULL-6 | `text(ev)` is `Some` of the decoded characters for a string or key event, span or owned, and of the spelling for a number event, and `None` for every other event | Proved | pending | |

JSON-PULL-1 is stated against `parse` rather than against the grammar so
that it can land before JSON-TEXT-1, and so that when JSON-TEXT-1 lands the
cursor inherits conformance without a second grammar proof. `events` is a
specification helper in `LAWS.bend`.

### Retiring the closed laws

All 99 laws are closed (inventory). We delete them all in the change that
lands SPEC.md (REVIEW-11). The inventory's "points toward" column keeps
the one useful thing they held, a map of which examples illustrate which
row; each row's quantified law replaces them. The helpers they share
(`again`, `kind`, `pull.run` and the rest) go with them, except any a
quantified proof uses as a lemma, which moves next to that proof.

### Tagging and traceability

SPEC.md uses bolt's format: requirement tables headed `| ID | Requirement |
Level | Status | Law |`, the Law cell as `<path> <law>` entries joined by
`; `, a trust table headed `| ID | Assumption | Why it is trusted |`, and a
"Left to prove" section for pending rows with partial laws. Each law
carries its row's ID on its own comment line above `law`. With bolt v1.4.2,
`trace`, `closed` and `coverage` run at error, so a row and its laws cannot
drift apart without the lint failing.

### The refactoring contract

A tagged law's statement is owned by its row. It changes only when the
row's wording changes, which is a behavior change and says so. A proof may
be rewritten freely, and so may untagged laws. The recent performance work
(spans, burst words, the suffix-dropping walk) is exactly the kind of
change this contract is for: with the rows proved, a rewrite of the cursor
is mergeable on the gate alone.

### The trust boundary

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| JSON-TRUST-1 | The Bend checker is sound: a proof it accepts proves its law | The gate cannot check the checker. Same as EZ-TRUST-1 |
| JSON-TRUST-2 | `U32.read` and `F32.read` in Bend's base library read a decimal spelling as documented, rounding to nearest for F32 | Foreign to this project; `as_u32` and `as_f32` forward to them. JSON-TREE-6 could drop this by reading digits itself |
| JSON-TRUST-3 | The cursor does not keep a parse tree or the text it has passed: memory while walking a large text stays proportional to the open containers and the events the caller holds | A law sees values, not heap shape. The `scale` check walks 563 KiB and 615 KiB texts in CI as an integration check |
| JSON-TRUST-4 | The proof-gate runner (`ez.mkProofs`) fails the build unless the first line is `All terms check.` | It is ez's code, trusted as EZ-TRUST-4 |

### Decided behavior changes

Decided with the REVIEW items. Each lands as its own change, with
master's results against the branch's in the description.

| Change | Needed by | REVIEW |
| :---- | :---- | :---- |
| `as_f32` returns none on overflow (landed) | JSON-TREE-7 | REVIEW-6 |
| `print` writes U+FFFD for a code point that is not a scalar value (landed) | JSON-STR-1, JSON-STR-5, JSON-PRINT-1 | REVIEW-3 |
| add `wf` (landed) | JSON-PRINT-1, JSON-PRINT-3 | REVIEW-3 |
| add `has` and `len` (landed) | JSON-TREE-8, JSON-TREE-9 | REVIEW-5 |
| README import hash (landed: v0.4.2's hash; the next release's hash replaces it at publish) | none (docs) | REVIEW-13 |

### How we will know it worked

- `trace`, `closed` and `coverage` at error under bolt v1.4.2 or later,
  with the gate and `scale` green in `nix flake check`.
- No closed law in the tree.
- No pending row in the JSON-PRINT and JSON-NUM groups, and JSON-PULL-1
  proved. JSON-TEXT-1 may still be pending, with its partial laws tagged
  and "Left to prove" saying what is missing.
- A rewrite of `pull.bend`'s hot loop is mergeable on the gate alone.

The rows that go through `parse` and the cursor are planned in their own
design doc, `docs/rfc/ezjson-parse-proofs.md`, with its own REVIEW items.

## Abandoned Ideas

**Keep the closed laws as documentation of the RFC sections.** They read
well and the README cites them. But they state 99 inputs, and a reader of
the Compliance list takes them as guarantees. The inventory keeps the map;
the rows keep the claims.

**Commit the differential harness as a test.** It found nothing wrong with
the grammar across 2,266 texts, and it is cheap to run. But it is a closed
law on a bigger input: it says nothing about the next text, and a passing
run would be read as evidence for JSON-TEXT-1. We used it to audit and to
check the verdicts, and we say so in the inventory.

**Prove `parse` equal to a reference parser.** The reference would be a
second parser with its own bugs, and the law would say only that two
programs agree. The `Derives` relation is different: it is the RFC's ABNF
transcribed, one constructor per rule, short enough to check by reading
against the RFC.

**Hide the cells behind an opaque type.** It would make `wf` unnecessary.
Bend has no private constructors, and bolt already matches on the cells,
so this would break the main user for a guarantee the `wf` precondition
gives anyway.

**Switch `get` to the last repeated key, as most libraries do.** Kept as
REVIEW-4's alternative. It changes documented, released behavior, and
it costs a full scan of every object on every lookup.

**State memory behavior as a Proved row.** The cursor's reason to exist is
memory, so a row is tempting. Nothing a law can state distinguishes a
cursor that keeps the text from one that does not; the row would be
trusted in all but name. It is JSON-TRUST-3, with `scale` behind it.

## Rollout

| Phase | What lands | What it leaves true |
| :---- | :---- | :---- |
| Lint first | bolt pin to v1.4.2, `laws` at warn; S003 and S004 fixed (99 of them in `bench/`) | lint clean except law rules |
| One | SPEC.md from these tables; all 99 closed laws deleted; `closed` and `trace` at error; README Compliance points at SPEC.md. The first quantified laws landed with it: JSON-TREE-1, JSON-TREE-2 and JSON-NUM-3 proved, and the not-a-container halves of JSON-TREE-3 and 4 | the gate is honest: SPEC.md says what is proved, and nothing claims more |
| Behavior changes | `as_f32` overflow; `wf` and U+FFFD in `print`; `has` and `len`; README hash; one PR each | the rows that needed them can be proved |
| Two | JSON-NUM-1 to 3, JSON-TREE-1 to 4, 6, 8, 9, JSON-STR-5: structural inductions on small defs | the interface is proved |
| Three | JSON-STR-1, JSON-PRINT-1 to 3, JSON-TREE-5 | the headline is proved |
| Four | JSON-PULL-1 to 6 | the cursor is proved against `parse` |
| Five | the `Derives` relation, JSON-TEXT-1 to 5 | conformance is proved; the cursor inherits it |

## Risks

- **Proof effort on the cursor.** `pull.bend` is 1,594 lines of a state
  machine tuned for memory, with nineteen scanner modes. JSON-PULL-1 may need an
  invariant relating each mode to a lexer state. If it proves too costly,
  moving it to Trusted is a visible weakening the maintainer approves.
- **The grammar relation encodes a mistake.** `Derives` is checked against
  the RFC by reading only. Keeping it one constructor per ABNF rule, with
  the rule quoted above each, is the mitigation.
- **The spec encodes accidents.** First-of-repeated-keys and `null` for a
  missing key become promises. REVIEW-4 and REVIEW-5 are where to stop that.
- **Downstream breakage.** Moving bolt to `main.bend` (REVIEW-1) and the
  `print` change (REVIEW-3) touch bolt. Neither changes output for a
  well-formed value built from scalar strings.
- **Pressure to reintroduce examples.** A failing proof invites a closed law
  "for now". The contract is that a pending row is honest and a closed law
  is not.
- **Checker soundness.** JSON-TRUST-1, as everywhere.

## Future Steps

- A public `eq` (REVIEW-9), once `same` has been used enough to know which
  equality callers want (number by spelling or by value; objects by order
  or as maps).
- Errors with a position. Every library in the comparison reports where a
  text went wrong; ezjson returns `None` or `EErr`. A row would state the
  offset exactly.
- Streaming output: a writer that emits events, mirroring the cursor,
  as Jackson's `JsonGenerator` and .NET's `Utf8JsonWriter` do.
- bolt's Trusted row for its JSON can point at JSON-PRINT-1 and JSON-TEXT-1
  instead of "ezjson is correct".
