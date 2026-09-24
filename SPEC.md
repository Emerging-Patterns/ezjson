# ezjson specification

This is the list of every behavior ezjson guarantees, each under a stable requirement ID. There are two families: conformance to [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259) (JSON-TEXT, JSON-NUM, JSON-STR, JSON-PRINT) and the public interface in `ezjson/main.bend` (JSON-TREE, JSON-PULL). Every other module is internal and carries no promise.

Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law (a `for` or `exs` binder) in `ezjson/LAWS.bend` that passes the proof gate. A **Trusted** requirement is an assumption ezjson cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose laws have not all landed has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: the first line `bend ezjson/PROOF.bend` prints is exactly `All terms check.` Tests and fixtures are never evidence for a requirement.

A value is **well-formed** when `V.wf` holds of it: its arrays and objects are chains of cells ending in `JNil`, no cell stands where a value belongs, and every number's text is a JSON number. Every value built through `main.bend` or returned by `parse` is well-formed (JSON-PRINT-3). `same` is the specification relation "the same JSON value", which ignores whether a string or key is owned or a span of the source. `ezjson/LAWS.bend` decides it with `own`, which reads every span out into its own string: two values are `same` when their `own` forms are equal.

The reasoning behind each requirement, the verdict of each against the code at `089d520`, and the decisions that shaped them are in [docs/rfc/ezjson-spec.md](docs/rfc/ezjson-spec.md). Every law as it stood then, and the progress of the rollout, is in [docs/rfc/ezjson-law-inventory.md](docs/rfc/ezjson-law-inventory.md).

The number rule of RFC 8259 §6 is written out in `ezjson/LAWS.bend` as `number` and the defs above it, one def per ABNF production, so JSON-NUM-1 can be checked against the RFC by reading those defs.

## Format

A requirement table is any table whose header row is exactly `| ID | Requirement | Level | Status | Law |`. An ID is uppercase segments joined by hyphens, at least two (`[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`), unique within the requirement tables, and never reused once released. Level is `Proved` or `Trusted`. Status is `proved` or `pending` for a Proved row and empty for a Trusted row. A Law cell holds `<path> <law>` entries, paths relative to this file, separated by `; `. A proved row names one or more laws, and together they prove it. A pending row may name laws that each prove part of it; the row stays pending until its requirement is proved in full, and "Left to prove" says what is missing.

A law proves a requirement when a comment line `# <ID>`, alone on its line, sits in the unbroken comment block directly above its `law` line. A law may carry several tags, one per line:

```
# LAW: as_bool reads back the boolean bool built
# JSON-TREE-1
law as_bool_bool:
```

A tag may name a proved or a pending requirement, never a Trusted one or an ID no requirement table lists. bolt's `trace` rule checks all of this over the whole tree, and its `closed` rule rejects a law with no binder; both are errors in `bolt.bend`.

## Requirements

### RFC 8259 texts (JSON-TEXT)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-TEXT-1 | For texts shorter than 2^32 - 1 characters: `parse(t)` is `Some` exactly when `t` matches RFC 8259's `JSON-text` rule (§2 to §7) and holds no `\u` escape of an unpaired surrogate (§8.2) | Proved | pending |  |
| JSON-TEXT-2 | For texts shorter than 2^32 - 1 characters: inserting any run of U+0020, U+0009, U+000A and U+000D before or after any token of a JSON text leaves `parse`'s result the same value; inserting any other character there makes it `None` (§2) | Proved | pending |  |
| JSON-TEXT-3 | For texts shorter than 2^32 - 1 characters: for every two well-formed values `j` and `k`, `parse(print(j) ++ " " ++ print(k))` is `None`: a text holds exactly one value (§2) | Proved | pending |  |
| JSON-TEXT-4 | For texts shorter than 2^32 - 1 characters: a bare word parses exactly when it is `null`, `true`, `false` or a number, and the literals are only the lowercase words (§3) | Proved | pending |  |
| JSON-TEXT-5 | For texts shorter than 2^32 - 1 characters: for every text `t`, `parse` of U+FEFF followed by `t` is `None` (§8.1) | Proved | pending |  |

### Numbers (JSON-NUM)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-NUM-1 | `num.ok(s)` holds exactly when `s` matches RFC 8259's `number` rule: an optional `-`, `0` or a nonzero digit and digits, an optional `.` and one or more digits, an optional `e` or `E`, an optional sign and one or more digits (§6) | Proved | proved | ezjson/LAWS.bend num_grammar |
| JSON-NUM-2 | For texts shorter than 2^32 - 1 characters: for every `s` with `num.ok(s)`, `parse(s)` is `Some{JNum{s}}` and `print` of it is `s`: a number keeps its spelling | Proved | pending |  |
| JSON-NUM-3 | `num(s)` is `JNum{s}` when `num.ok(s)`, and `null()` otherwise | Proved | proved | ezjson/LAWS.bend num_keeps; ezjson/LAWS.bend num_null |

### Strings (JSON-STR)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-STR-1 | For texts shorter than 2^32 - 1 characters: for every string `s` of Unicode scalar values, `parse(quote(s))` is a string value whose characters are `s` (§7) | Proved | proved | ezjson/LAWS.bend str_back |
| JSON-STR-2 | For texts shorter than 2^32 - 1 characters: inside a string, `\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t` decode to their characters; `\uXXXX` of a non-surrogate decodes to that code point; a high then low surrogate escape decodes to one code point; any other escape, and an unpaired surrogate escape, make `parse` `None` (§7, §8.2) | Proved | pending |  |
| JSON-STR-3 | For texts shorter than 2^32 - 1 characters: inside a string, a raw U+0000 to U+001F makes `parse` `None`, and every other raw code point except `"` and `\` is kept as itself (§7) | Proved | pending |  |
| JSON-STR-4 | For texts shorter than 2^32 - 1 characters: two object names compare equal in `get` exactly when their decoded characters are equal, whatever escapes spelled them (§8.3) | Proved | pending |  |
| JSON-STR-5 | `quote(s)` escapes exactly `"`, `\` and U+0000 to U+001F, using the two-character form where one exists and `\u00xx` otherwise, and writes every other scalar value as itself, and writes U+FFFD for every code point that is not a Unicode scalar value (a surrogate, or past U+10FFFF) (§7, §8.1) | Proved | proved | ezjson/LAWS.bend print_non_scalar; ezjson/LAWS.bend esc_quote; ezjson/LAWS.bend esc_backslash; ezjson/LAWS.bend esc_b; ezjson/LAWS.bend esc_f; ezjson/LAWS.bend esc_n; ezjson/LAWS.bend esc_r; ezjson/LAWS.bend esc_t; ezjson/LAWS.bend esc_plain; ezjson/LAWS.bend esc_ctl |

### Print and round trip (JSON-PRINT)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-PRINT-1 | For texts shorter than 2^32 - 1 characters: for every well-formed value `j`, `parse(print(j))` is `Some` of a value `same` as `j` with every code point that is not a Unicode scalar value replaced by U+FFFD | Proved | proved | ezjson/LAWS.bend print_parse |
| JSON-PRINT-2 | For texts shorter than 2^32 - 1 characters: for every text `t` with `parse(t) == Some{j}`, `print(j)` holds no whitespace outside strings, and `print(j) == print(j2)` where `parse(print(j)) == Some{j2}` | Proved | proved | ezjson/LAWS.bend print_compact; ezjson/LAWS.bend print_stable |
| JSON-PRINT-3 | For every value built only from `null`, `bool`, `str`, `num`, `arr` and `obj`, or returned by `parse`, `wf` holds | Proved | proved | ezjson/LAWS.bend wf_scalars; ezjson/LAWS.bend wf_num; ezjson/LAWS.bend wf_arr; ezjson/LAWS.bend wf_obj; ezjson/LAWS.bend parse_wf |

### The tree interface (JSON-TREE)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-TREE-1 | `as_bool(bool(b)) == Some{b}`, `as_str(str(s)) == Some{s}`, and `as_num(num(s)) == Some{s}` when `num.ok(s)` | Proved | proved | ezjson/LAWS.bend as_bool_bool; ezjson/LAWS.bend as_str_str; ezjson/LAWS.bend as_num_num |
| JSON-TREE-2 | Each of `as_bool`, `as_str`, `as_num`, `as_u32`, `as_f32` is `None` on every value of another kind | Proved | proved | ezjson/LAWS.bend as_bool_kind; ezjson/LAWS.bend as_str_kind; ezjson/LAWS.bend as_num_kind; ezjson/LAWS.bend as_u32_kind; ezjson/LAWS.bend as_f32_kind |
| JSON-TREE-3 | `at(arr(xs), i)` is the `i`-th element of `xs` when `i` is less than its length, and `null()` otherwise; `at(j, i)` is `null()` for every `j` that is not an array | Proved | proved | ezjson/LAWS.bend at_not_arr; ezjson/LAWS.bend at_arr |
| JSON-TREE-4 | `get(obj(ps), k)` is the value of the first pair in `ps` whose key is `k`, and `null()` when there is none; `get(j, k)` is `null()` for every `j` that is not an object | Proved | proved | ezjson/LAWS.bend get_not_obj; ezjson/LAWS.bend get_empty; ezjson/LAWS.bend get_hit; ezjson/LAWS.bend get_miss |
| JSON-TREE-5 | For texts shorter than 2^32 - 1 characters: for every text `t` with `parse(t) == Some{j}`, every reader (`get`, `at`, `as_*`) gives on `j` the result it gives on the owned value `same` as `j`: a span reads as its characters | Proved | proved | ezjson/LAWS.bend get_same; ezjson/LAWS.bend at_same; ezjson/LAWS.bend as_str_same; ezjson/LAWS.bend as_bool_same; ezjson/LAWS.bend as_num_same; ezjson/LAWS.bend as_u32_same; ezjson/LAWS.bend as_f32_same |
| JSON-TREE-6 | `as_u32(num(s))` is `Some{n}` exactly when `s` is one or more ASCII digits, with no leading zero unless `s` is `0`, whose value `n` is at most 4294967295 | Proved | pending |  |
| JSON-TREE-7 | For every number value whose text is `s`: when `F32.read(s)` is `Some{x}` with `F32.abs(x)` at most 3.4028235e38 (the largest finite F32), `as_f32` is `Some{x}`; when that read is infinite or `None`, `as_f32` is `None` | Proved | proved | ezjson/LAWS.bend as_f32_fits; ezjson/LAWS.bend as_f32_overflow; ezjson/LAWS.bend as_f32_unread |
| JSON-TREE-8 | `has(obj(ps), k)` is true exactly when some pair in `ps` has key `k`, and `has(j, k)` is false for every `j` that is not an object | Proved | proved | ezjson/LAWS.bend has_not_obj; ezjson/LAWS.bend has_empty; ezjson/LAWS.bend has_hit; ezjson/LAWS.bend has_miss |
| JSON-TREE-9 | `len(arr(xs))` is the length of `xs`, `len(obj(ps))` the length of `ps`, and `len(j)` is 0 for every scalar | Proved | proved | ezjson/LAWS.bend len_arr; ezjson/LAWS.bend len_obj; ezjson/LAWS.bend len_scalar |

### The pull cursor (JSON-PULL)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-PULL-1 | For every text `t` shorter than 2^32 characters, the events `next` yields from `cursor(t)` end in `EEnd` exactly when `parse(t)` is `Some{j}`, and then they are `events(j)`: the value's scalars, keys and container begins and ends in document order, with no event for a comma or a colon | Proved | pending |  |
| JSON-PULL-2 | Once `next` yields `EErr`, every later `next` on the returned cursor yields `EErr`, and `skip` returns a failed cursor | Proved | proved | ezjson/LAWS.bend pull_err_fails; ezjson/LAWS.bend pull_failed_next; ezjson/LAWS.bend pull_failed_skip |
| JSON-PULL-3 | Once `next` yields `EEnd`, every later `next` on the returned cursor yields `EEnd` | Proved | proved | ezjson/LAWS.bend pull_end_ends; ezjson/LAWS.bend pull_ended_next |
| JSON-PULL-4 | For every cursor at a position where a value may start, `next(skip(c))` yields the event that follows that value's last event in the full stream from `c` | Proved | pending |  |
| JSON-PULL-5 | `skip` at a position where no value may start (before an object key, at a close bracket, after the root, or on a failed cursor) returns a failed cursor | Proved | proved | ezjson/LAWS.bend pull_failed_skip; ezjson/LAWS.bend pull_over_skip; ezjson/LAWS.bend skip_key; ezjson/LAWS.bend skip_close_arr; ezjson/LAWS.bend skip_close_obj |
| JSON-PULL-6 | `text(ev)` is `Some` of the decoded characters for a string or key event, span or owned, and of the spelling for a number event, and `None` for every other event | Proved | proved | ezjson/LAWS.bend text_str; ezjson/LAWS.bend text_key; ezjson/LAWS.bend text_str_span; ezjson/LAWS.bend text_key_span; ezjson/LAWS.bend text_num; ezjson/LAWS.bend text_none |

## Left to prove

Every pending row has no Law entry and is unproved in full; the RFC's Rollout says in which phase its laws land. No row is partly proved.

## Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and a passing proof gate says nothing about them.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| JSON-TRUST-1 | The Bend checker is sound: a proof it accepts proves its law. | It cannot be checked from inside Bend; this is EZ-TRUST-1. ezjson pins bend 2.0.25 through the flake. |
| JSON-TRUST-2 | `U32.read` and `F32.read` in Bend's base library read a decimal spelling as documented, rounding to nearest for F32. | Foreign to this project; `as_u32` and `as_f32` forward to them. |
| JSON-TRUST-3 | The cursor does not keep a parse tree or the text it has passed: memory while walking a large text stays proportional to the open containers and the events the caller holds. | A law sees values, not heap shape. The `scale` flake check walks a 563 KiB and a 615 KiB text with the cursor as an integration check. |
| JSON-TRUST-4 | The proof-gate runner fails the build unless the first line of `bend ezjson/PROOF.bend` is `All terms check.` | It is ez's `mkProofs`, run by `nix flake check` in CI; this is EZ-TRUST-4. |
