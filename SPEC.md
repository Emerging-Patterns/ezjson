# ezjson specification

This is the list of every behavior ezjson guarantees, each under a stable requirement ID. There are two families: conformance to [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259) (JSON-TEXT, JSON-NUM, JSON-STR, JSON-PRINT) and the public interface in `main.bend` (JSON-TREE, JSON-PULL, JSON-FIX). Every other module is internal and carries no promise.

Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law (a `for` or `exs` binder) in `LAWS.bend` that passes the proof gate. A **Trusted** requirement is an assumption ezjson cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose laws have not all landed has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: the first line `bend PROOF.bend` prints is exactly `ALL PROOFS CHECK`. Tests and fixtures are never evidence for a requirement.

A value is **well-formed** when `V.wf` holds of it: its arrays and objects are chains of cells ending in `JNil`, no cell stands where a value belongs, and every number's text is a JSON number. Every value built through `main.bend` or returned by `parse` is well-formed (JSON-PRINT-3). `same` is the specification relation "the same JSON value", which ignores whether a string or key is owned or a span of the source. `LAWS.bend` decides it with `own`, which reads every span out into its own string: two values are `same` when their `own` forms are equal.

The reasoning behind each requirement, the verdict of each against the code at `089d520`, and the decisions that shaped them are in [docs/rfc/ezjson-spec.md](docs/rfc/ezjson-spec.md). Every law as it stood then, and the progress of the rollout, is in [docs/rfc/ezjson-law-inventory.md](docs/rfc/ezjson-law-inventory.md).

The number rule of RFC 8259 §6 is written out in `LAWS.bend` as `number` and the defs above it, one def per ABNF production, so JSON-NUM-1 can be checked against the RFC by reading those defs.

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
| JSON-TEXT-1 | For texts shorter than 2^32 - 1 characters, all of them code points (at most U+10FFFF): `parse(t)` is `Some` exactly when `t` matches RFC 8259's `JSON-text` rule (§2 to §7) and holds no `\u` escape of an unpaired surrogate (§8.2) | Proved | proved | LAWS.bend text_some; LAWS.bend text_derives |
| JSON-TEXT-2 | For texts shorter than 2^32 - 1 characters: inserting any run of U+0020, U+0009, U+000A and U+000D before or after any token of a JSON text leaves `parse`'s result the same value; inserting any other character there, except a digit or `-` (which can make or extend a number), makes it `None` (§2) | Proved | proved | LAWS.bend ws_same; LAWS.bend ins_none |
| JSON-TEXT-3 | For texts shorter than 2^32 - 1 characters: for every two well-formed values `j` and `k`, `parse(print(j) ++ " " ++ print(k))` is `None`: a text holds exactly one value (§2) | Proved | proved | LAWS.bend two_none |
| JSON-TEXT-4 | For texts shorter than 2^32 - 1 characters: a bare word parses exactly when it is `null`, `true`, `false` or a number, and the literals are only the lowercase words (§3) | Proved | proved | LAWS.bend bare_word |
| JSON-TEXT-5 | For texts shorter than 2^32 - 1 characters: for every text `t`, `parse` of U+FEFF followed by `t` is `None` (§8.1) | Proved | proved | LAWS.bend bom_none |

### Numbers (JSON-NUM)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-NUM-1 | `num.ok(s)` holds exactly when `s` matches RFC 8259's `number` rule: an optional `-`, `0` or a nonzero digit and digits, an optional `.` and one or more digits, an optional `e` or `E`, an optional sign and one or more digits (§6) | Proved | proved | LAWS.bend num_grammar |
| JSON-NUM-2 | For texts shorter than 2^32 - 1 characters: for every `s` with `num.ok(s)`, `parse(s)` is `Some{JNum{s}}` and `print` of it is `s`: a number keeps its spelling | Proved | proved | LAWS.bend parse_num; LAWS.bend print_num |
| JSON-NUM-3 | `num(s)` is `JNum{s}` when `num.ok(s)`, and `null()` otherwise | Proved | proved | LAWS.bend num_keeps; LAWS.bend num_null |

### Strings (JSON-STR)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-STR-1 | For texts shorter than 2^32 - 1 characters: for every string `s` of Unicode scalar values, `parse(quote(s))` is a string value whose characters are `s` (§7) | Proved | proved | LAWS.bend str_back |
| JSON-STR-2 | For texts shorter than 2^32 - 1 characters: inside a string, `\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t` decode to their characters; `\uXXXX` of a non-surrogate decodes to that code point; a high then low surrogate escape decodes to one code point; any other escape, and an unpaired surrogate escape, make `parse` `None` (§7, §8.2) | Proved | proved | LAWS.bend esc_decodes; LAWS.bend esc_bad; LAWS.bend esc_u; LAWS.bend esc_pair; LAWS.bend esc_u_bad; LAWS.bend esc_lo_bad; LAWS.bend esc_hi_bad |
| JSON-STR-3 | For texts shorter than 2^32 - 1 characters: inside a string, a raw U+0000 to U+001F makes `parse` `None`, and every other raw code point except `"` and `\` is kept as itself (§7) | Proved | proved | LAWS.bend raw_kept; LAWS.bend ctl_none |
| JSON-STR-4 | For texts shorter than 2^32 - 1 characters: two object names compare equal in `get` exactly when their decoded characters are equal, whatever escapes spelled them (§8.3) | Proved | proved | LAWS.bend get_decoded |
| JSON-STR-5 | `quote(s)` escapes exactly `"`, `\` and U+0000 to U+001F, using the two-character form where one exists and `\u00xx` otherwise, and writes every other scalar value as itself, and writes U+FFFD for every code point that is not a Unicode scalar value (a surrogate, or past U+10FFFF) (§7, §8.1) | Proved | proved | LAWS.bend print_non_scalar; LAWS.bend esc_quote; LAWS.bend esc_backslash; LAWS.bend esc_b; LAWS.bend esc_f; LAWS.bend esc_n; LAWS.bend esc_r; LAWS.bend esc_t; LAWS.bend esc_plain; LAWS.bend esc_ctl |

### Print and round trip (JSON-PRINT)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-PRINT-1 | For texts shorter than 2^32 - 1 characters: for every well-formed value `j`, `parse(print(j))` is `Some` of a value `same` as `j` with every code point that is not a Unicode scalar value replaced by U+FFFD | Proved | proved | LAWS.bend print_parse |
| JSON-PRINT-2 | For texts shorter than 2^32 - 1 characters: for every text `t` with `parse(t) == Some{j}`, `print(j)` holds no whitespace outside strings, and `print(j) == print(j2)` where `parse(print(j)) == Some{j2}` | Proved | proved | LAWS.bend print_compact; LAWS.bend print_stable |
| JSON-PRINT-3 | For every value built only from `null`, `bool`, `str`, `num`, `arr` and `obj`, or returned by `parse`, `wf` holds | Proved | proved | LAWS.bend wf_scalars; LAWS.bend wf_num; LAWS.bend wf_arr; LAWS.bend wf_obj; LAWS.bend parse_wf |
| JSON-PRINT-4 | For texts shorter than 2^32 - 1 characters: for every well-formed value `j`, `parse(pretty(j))` is `Some` of a value `same` as `j` with every code point that is not a Unicode scalar value replaced by U+FFFD, as for `print` | Proved | proved | LAWS.bend pretty_parse |

### The tree interface (JSON-TREE)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-TREE-1 | `as_bool(bool(b)) == Some{b}`, `as_str(str(s)) == Some{s}`, and `as_num(num(s)) == Some{s}` when `num.ok(s)` | Proved | proved | LAWS.bend as_bool_bool; LAWS.bend as_str_str; LAWS.bend as_num_num |
| JSON-TREE-2 | Each of `as_bool`, `as_str`, `as_num`, `as_u32`, `as_f32` is `None` on every value of another kind | Proved | proved | LAWS.bend as_bool_kind; LAWS.bend as_str_kind; LAWS.bend as_num_kind; LAWS.bend as_u32_kind; LAWS.bend as_f32_kind |
| JSON-TREE-3 | `at(arr(xs), i)` is the `i`-th element of `xs` when `i` is less than its length, and `null()` otherwise; `at(j, i)` is `null()` for every `j` that is not an array | Proved | proved | LAWS.bend at_not_arr; LAWS.bend at_arr |
| JSON-TREE-4 | `get(obj(ps), k)` is the value of the first pair in `ps` whose key is `k`, and `null()` when there is none; `get(j, k)` is `null()` for every `j` that is not an object | Proved | proved | LAWS.bend get_not_obj; LAWS.bend get_empty; LAWS.bend get_hit; LAWS.bend get_miss |
| JSON-TREE-5 | For texts shorter than 2^32 - 1 characters: for every text `t` with `parse(t) == Some{j}`, every reader (`get`, `at`, `as_*`) gives on `j` the result it gives on the owned value `same` as `j`: a span reads as its characters | Proved | proved | LAWS.bend get_same; LAWS.bend at_same; LAWS.bend as_str_same; LAWS.bend as_bool_same; LAWS.bend as_num_same; LAWS.bend as_u32_same; LAWS.bend as_f32_same |
| JSON-TREE-6 | `as_u32(num(s))` is `Some{n}` exactly when `s` is one or more ASCII digits, with no leading zero unless `s` is `0`, whose value `n` is at most 4294967295 | Proved | proved | LAWS.bend as_u32_num; LAWS.bend u32_nat_inj |
| JSON-TREE-7 | For every number value whose text is `s`: when `F32.read(s)` is `Some{x}` with `F32.abs(x)` at most 3.4028235e38 (the largest finite F32), `as_f32` is `Some{x}`; when that read is infinite or `None`, `as_f32` is `None` | Proved | proved | LAWS.bend as_f32_fits; LAWS.bend as_f32_overflow; LAWS.bend as_f32_unread |
| JSON-TREE-8 | `has(obj(ps), k)` is true exactly when some pair in `ps` has key `k`, and `has(j, k)` is false for every `j` that is not an object | Proved | proved | LAWS.bend has_not_obj; LAWS.bend has_empty; LAWS.bend has_hit; LAWS.bend has_miss |
| JSON-TREE-9 | `len(arr(xs))` is the length of `xs`, `len(obj(ps))` the length of `ps`, and `len(j)` is 0 for every scalar | Proved | proved | LAWS.bend len_arr; LAWS.bend len_obj; LAWS.bend len_scalar |
| JSON-TREE-10 | `items(arr(xs))` is `xs`; for every well-formed array `j`, `arr(items(j))` is `j`, `at(j, i)` is the `i`-th element of `items(j)` (`null()` past its end) and `len(j)` is the length of `items(j)`: `items` gives an array's elements in order; `items(j)` is `[]` for every `j` that is not an array | Proved | proved | LAWS.bend items_arr; LAWS.bend items_back; LAWS.bend items_at; LAWS.bend items_len; LAWS.bend items_not_arr |
| JSON-TREE-11 | For every value `j`, `is_arr(j)` is true exactly when `j` is an array and `is_obj(j)` exactly when `j` is an object: `is_arr(arr(xs))` and `is_obj(obj(ps))` hold, and neither holds of a null, a boolean, a number or a string, owned or a span | Proved | proved | LAWS.bend is_arr_kind; LAWS.bend is_obj_kind; LAWS.bend is_arr_arr; LAWS.bend is_obj_obj |

### The pull cursor (JSON-PULL)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-PULL-1 | For every text `t` shorter than 2^32 characters, the events `next` yields from `cursor(t)` end in `EEnd` exactly when `parse(t)` is `Some{j}`, and then they are `events(j)`: the value's scalars, keys and container begins and ends in document order, with no event for a comma or a colon | Proved | proved | LAWS.bend pull_events; LAWS.bend pull_ends |
| JSON-PULL-2 | Once `next` yields `EErr`, every later `next` on the returned cursor yields `EErr`, and `skip` returns a failed cursor | Proved | proved | LAWS.bend pull_err_fails; LAWS.bend pull_failed_next; LAWS.bend pull_failed_skip |
| JSON-PULL-3 | Once `next` yields `EEnd`, every later `next` on the returned cursor yields `EEnd` | Proved | proved | LAWS.bend pull_end_ends; LAWS.bend pull_ended_next |
| JSON-PULL-4 | For every cursor whose unread text is shorter than 2^32 characters, at a position where a value may start, `next(skip(c))` yields the event that follows that value's last event in the full stream from `c` | Proved | proved | LAWS.bend pull_skip; LAWS.bend pull_skip_next |
| JSON-PULL-5 | `skip` at a position where no value may start (before an object key, at a close bracket, after the root, or on a failed cursor) returns a failed cursor | Proved | proved | LAWS.bend pull_failed_skip; LAWS.bend pull_over_skip; LAWS.bend skip_key; LAWS.bend skip_close_arr; LAWS.bend skip_close_obj |
| JSON-PULL-6 | `text(ev)` is `Some` of the decoded characters for a string or key event, span or owned, and of the spelling for a number event, and `None` for every other event | Proved | proved | LAWS.bend text_str; LAWS.bend text_key; LAWS.bend text_str_span; LAWS.bend text_key_span; LAWS.bend text_num; LAWS.bend text_none |

### Fixed decimals (JSON-FIX)

`num.fixed(s, n)` writes a number's text with exactly `n` digits after the point, rounding half to even on its decimal digits. The reference is Python's `format(Decimal(s).quantize(Decimal(10) ** -n, ROUND_HALF_EVEN), 'f')`, which is IEEE 754's roundTiesToEven applied to the exact decimal value of `s`; on every input where that decimal value is exactly a binary double, this is also Python's `'%.{n}f' % float(s)` (C's `printf("%.*f")`). Python's `'%.Nf'` rounds the double nearest to `s`, not `s`, so the two differ where the double falls on the other side of a rounding boundary: `2.675` to 2 places is `2.68` here and `2.67` in Python (the double is 2.67499999999999982236431605997495353221893310546875), `0.15` to 1 is `0.2` here and `0.1` there, `0.45` is `0.4` here and `0.5` there, `0.0005` to 3 is `0.000` here and `0.001` there, `9.995` to 2 is `10.00` here and `9.99` there. They also differ past the 17 significant digits a double holds (`1e23` to 0 places is a 1 and 23 zeros here, `99999999999999991611392` there; `123456789012345678.5` to 0 is `123456789012345678` here, `123456789012345680` there) and past the double's range (`1e400` is written out in full here, `inf` there). Exact values agree (`0.125`, `2.5` to 0 places is `2`, `0.5` is `0`). The laws below state the steps over `src/fixed.bend`; together they define the result for every text, and LAWS.bend states each step in the order the text is read: the sign (JSON-FIX-2), the cut and the exponent (JSON-FIX-3), the rounding (JSON-FIX-4), the writing (JSON-FIX-5). The exponent is read as a natural number and the point moved one place a step, so the time and memory of a call grow with the exponent's value: `1e999999999` asks for a billion digits, and a caller formatting untrusted numbers bounds the exponent first.

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| JSON-FIX-1 | For every text `s` and count `n`, `num.fixed(s, n)` is `None` when `num.ok(s)` is false, and `Some{F.text(s, n)}` when it is true, where `F.text` is `src/fixed.bend`'s writer that JSON-FIX-2 to JSON-FIX-5 describe | Proved | proved | LAWS.bend fixed_none; LAWS.bend fixed_some |
| JSON-FIX-2 | For every text `s` and count `n`, the text of `-` followed by `s` is `-` followed by the unsigned text of `s`, and a text that does not start with `-` (the empty one too) is written unsigned: the minus is kept even when every digit rounds to `0`, so `-0.04` to 1 place is `-0.0` and `-0` to 2 is `-0.00`, as Python's `'%.Nf'` and C's `printf` write a negative zero | Proved | proved | LAWS.bend text_minus; LAWS.bend text_plain; LAWS.bend text_empty |
| JSON-FIX-3 | An unsigned text is cut at its first `e` or `E` into a mantissa and an exponent (no mark: the exponent is empty), and the mantissa at its first `.` into integer and fraction digits (no point: the fraction is empty). An exponent's leading `-` makes it negative, a leading `+` is dropped, and any other exponent is positive and keeps every character. The exponent's digits are read most significant first as the natural number `k` (empty: 0). The integer digits, last first, and the fraction digits stand around the point, and the point moves `k` places right for a positive exponent and left for a negative one, one place a step: a move right carries the first fraction digit before the point, or a `0` when there is none, and a move left carries the last integer digit after the point, or a `0` when there is none; a move right then left, or left then right, gives the same digits back. So `1e-05` is `0.00001` and `2.5e1` is `25` | Proved | proved | LAWS.bend unsigned_steps; LAWS.bend parts_exp; LAWS.bend parts_plain; LAWS.bend mant_dot; LAWS.bend mant_int; LAWS.bend esign_minus; LAWS.bend esign_plus; LAWS.bend esign_digits; LAWS.bend place_parts; LAWS.bend nat_start; LAWS.bend nat_end; LAWS.bend nat_snoc; LAWS.bend move_right; LAWS.bend move_left; LAWS.bend ups_zero; LAWS.bend ups_succ; LAWS.bend downs_zero; LAWS.bend downs_succ; LAWS.bend up_digit; LAWS.bend up_zero; LAWS.bend down_digit; LAWS.bend down_zero; LAWS.bend up_down; LAWS.bend down_up |
| JSON-FIX-4 | The digits are cut after the `n`-th fraction place: exactly `n` fraction digits are kept, `0`s past the last fraction digit, and the rest are dropped. The kept digits go up by one in the last kept place exactly when the first dropped digit is above `5`; or is `5` and a later dropped digit is not `0`; or is `5`, every later dropped digit is `0`, and the last kept digit is odd (a tie goes to the even neighbour, and no kept digit at all counts as an even `0`). No dropped digit, or a first dropped digit below `5`, keeps the digits as they are. Going up by one makes a last `9` a `0` and carries, and all `9`s become `0`s under a new leading `1` | Proved | proved | LAWS.bend round_cut; LAWS.bend pad_width; LAWS.bend pad_none; LAWS.bend pad_digit; LAWS.bend pad_past; LAWS.bend up_exact; LAWS.bend up_below; LAWS.bend up_above; LAWS.bend up_past_half; LAWS.bend up_tie; LAWS.bend up_tie_none; LAWS.bend nonzero_zeros; LAWS.bend nonzero_digit; LAWS.bend bump_up; LAWS.bend bump_down; LAWS.bend inc_digit; LAWS.bend inc_nine; LAWS.bend inc_nines |
| JSON-FIX-5 | The rounded digits are written as the integer part, every digit before the last `n` with its leading `0`s dropped (`0` when none is left), followed by `.` and the last `n` digits when `n` is at least 1, and by nothing when `n` is 0: no point, as Python writes `'%.0f' % 2.5` as `2` | Proved | proved | LAWS.bend write_parts; LAWS.bend point_none; LAWS.bend point_some; LAWS.bend trim_zero; LAWS.bend trim_lead; LAWS.bend trim_zeros |

## Left to prove

Every row is proved. JSON-PULL-4 carries the same bound as JSON-PULL-1: its unread text is shorter than 2^32 characters. Without it the row fails for texts of about 2^35 characters or more: `skip` walks a whole value on one budget of 4 × (2^33 − 1) jumps and spends two on each bare word, so an array of about 2^34 numbers uses the budget up, and `skip` returns a failed cursor where `next` would read on.

## Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and a passing proof gate says nothing about them.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| JSON-TRUST-1 | The Bend checker is sound: a proof it accepts proves its law. | It cannot be checked from inside Bend; this is EZ-TRUST-1. ezjson pins bend 2.0.38 through the flake. |
| JSON-TRUST-2 | `F32.read` in Bend's base library reads a decimal spelling as documented, rounding to nearest. | Foreign to this project; `as_f32` forwards to it. `U32.read` is no longer trusted: JSON-TREE-6's `as_u32_num` is proved through it as written. |
| JSON-TRUST-3 | The cursor does not keep a parse tree or the text it has passed: memory while walking a large text stays proportional to the open containers and the events the caller holds. | A law sees values, not heap shape. The `scale` flake check walks a 563 KiB and a 615 KiB text with the cursor as an integration check. |
| JSON-TRUST-4 | The proof-gate runner fails the build unless the first line of `bend PROOF.bend` is `ALL PROOFS CHECK`. | It is the flake's `checks.proofs`, run by `nix flake check` in CI on the flake's bend 2.0.38: until ez releases on 2.0.38 a `runCommand` that applies ez's `mkProofs` rule (EZ-TRUST-4) to every PROOF.bend, then ez's `mkProofs` again. |
