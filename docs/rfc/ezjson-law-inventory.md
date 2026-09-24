# ezjson law inventory

Read at `089d520` (v0.4.2, main). Bend 2.0.25 from the release archive the
flake pins (sha256 `91c0e264…f9ccd4`, checked). The proof gate was run as
`bend ezjson/PROOF.bend`. The linter was run two ways: the bolt the flake
pins (`5b05a1b`, between v0.4.0 and v0.5.0) and bolt v1.4.2 (`bolt --gpu off`
over the whole tree, with `BEND_LIB` laid out by hand from bolt's
`ez.lock.toml`, because this environment cannot reach the hub). No nix was
available, so `nix flake check` was not run; its `proofs`, `lint` and
`scale` checks were run by hand as below.

The tables below are the audit as read at `089d520`; the laws they list
were deleted in phase one. "Progress" at the end is current.

This file is the evidence the RFC (`docs/rfc/ezjson-spec.md`) cites. It is a
progress tracker. When the rollout ends, what still matters moves into the
RFC and this file is deleted.

## How to read the tables

| Column | Values |
| :---- | :---- |
| Kind | `Q` quantified (at least one `for` or `exs` binder), `C` closed |
| Proof | `{==}` when the whole proof is `{==}`, `struct` when it matches, recurses or rewrites |
| Claim | what the law states, as its own `# LAW:` comment says, about the inputs it names |
| Points toward | the draft requirement it illustrates, or `none (<reason>)` |

Reasons for `none`: `helper pin` (one private helper on one input),
`wiring` (a `main.bend` wrapper equals the def it forwards to, on one input).

## The gate and the linter on the project itself

| Check | Result |
| :---- | :---- |
| `bend ezjson/PROOF.bend` | first line `All terms check.`, exit 0, 5.5 s |
| pinned bolt (`5b05a1b`), whole tree | `clean`, exit 0 |
| bolt v1.4.2, whole tree | 454 errors: 105 L001 (`coverage`), 99 L002 (`closed`), 248 S004, 2 S003 |
| `scale/main.bend` built from a fresh `git archive` | `rows=32000 skip-rows=k:n#1 nest=105001 skip-nest=k:n#1`, matching the four greps in `scale/default.nix` |

The pinned bolt predates the `closed`, `coverage` and `trace` rules, so its
`clean` says nothing about laws. Under v1.4.2 every law is reported as
closed and 105 defs (every public def among them) are named by no
quantified law. Of the 248 S004 findings, 99 are in `bench/main.bend`.

## Summary

| File | Laws | Quantified | Closed | Quantified by `{==}` | Points toward nothing |
| :---- | --: | --: | --: | --: | --: |
| `ezjson/LAWS.bend` | 99 | 0 | 99 | 0 | 42 |

Of the 42 pointing toward nothing, 25 pin one private helper on one input
and 17 check that a `main.bend` wrapper forwards, on one input.

**What ezjson proves today.** Nothing for every input. Every law is a
closed equality proved by `{==}`, so the gate runs 99 examples. Three
(`rfc_raw_controls`, `rfc_ws_ctl`, `rfc_u_controls`) enumerate all 32 code
points U+0000 to U+001F, so they are exhaustive over that range and are the
nearest thing to a guarantee the project has. The README's "Compliance"
section lists RFC 8259 sections these examples "check". That wording is
accurate, but a reader would take it as a guarantee, and no law quantifies
over texts, values, strings or numbers.

The code is better than its laws. A differential run (below) found no
disagreement between `parse`, `print`, the cursor and a strict RFC 8259
reference over 2,266 texts. The gap is in what is proved, not in what the
code does, except for the interface findings at the end.

## Inventory

| Law | Line | Kind | Proof | Claim | Points toward |
| :-- | --: | :-: | :-: | :-- | :-- |
| `roundtrip_null` | 26 | C | `{==}` | RFC 8259 §3: null round-trips | JSON-TEXT-4 |
| `roundtrip_bools` | 30 | C | `{==}` | RFC 8259 §3: true and false round-trip | JSON-TEXT-4 |
| `roundtrip_nums` | 34 | C | `{==}` | RFC 8259 §6: numbers keep their spelling | JSON-NUM-2 |
| `roundtrip_space` | 38 | C | `{==}` | RFC 8259 §2: space, tab, and line feed inside a value are insignificant | JSON-TEXT-2 |
| `roundtrip_escapes` | 42 | C | `{==}` | RFC 8259 §7: escapes decode and reprint | JSON-STR-2 |
| `roundtrip_nest` | 47 | C | `{==}` | nesting round-trips | JSON-PRINT-1 |
| `parse_empty` | 51 | C | `{==}` | empty input is bad | JSON-TEXT-1 |
| `parse_unclosed_arr` | 55 | C | `{==}` | an unclosed array is bad | JSON-TEXT-1 |
| `parse_stray` | 59 | C | `{==}` | a stray close is bad | JSON-TEXT-1 |
| `parse_two_roots` | 63 | C | `{==}` | RFC 8259 §2: two values are not one JSON text | JSON-TEXT-3 |
| `parse_unclosed_str` | 67 | C | `{==}` | an unclosed string is bad | JSON-TEXT-1 |
| `parse_mismatch` | 71 | C | `{==}` | a mismatched close is bad | JSON-TEXT-1 |
| `print_msg` | 75 | C | `{==}` | a built value prints | JSON-PRINT-1 |
| `get_uri` | 80 | C | `{==}` | a path reads a string | JSON-TREE-4 |
| `get_id` | 84 | C | `{==}` | a number reads | JSON-TREE-6 |
| `get_missing` | 88 | C | `{==}` | a missing key reads as none | JSON-TREE-4 |
| `get_not_num` | 92 | C | `{==}` | a string is not a number | JSON-TREE-2 |
| `parse_obj_not_str` | 96 | C | `{==}` | parsed text at a is an object, not a string | JSON-TREE-2 |
| `parse_path_chain` | 100 | C | `{==}` | parsed paths chain | JSON-TREE-5 |
| `arr_first` | 105 | C | `{==}` | an array's first item | JSON-TREE-3 |
| `find_missing` | 109 | C | `{==}` | find on a missing key is JNull | none (helper pin) |
| `reverse_nil` | 113 | C | `{==}` | reverse of no cells is the acc | none (helper pin) |
| `print_quote` | 117 | C | `{==}` | a quoted string | none (helper pin) |
| `print_escape` | 121 | C | `{==}` | escape of a quote | none (helper pin) |
| `parse_word_null` | 125 | C | `{==}` | RFC 8259 §3: null is the lowercase word | none (helper pin) |
| `parse_word_true` | 129 | C | `{==}` | RFC 8259 §3: true is the lowercase word | none (helper pin) |
| `parse_word_false` | 133 | C | `{==}` | RFC 8259 §3: false is the lowercase word | none (helper pin) |
| `parse_word_num` | 137 | C | `{==}` | a number word keeps its text | none (helper pin) |
| `parse_finish` | 141 | C | `{==}` | finish of a good root | none (helper pin) |
| `parse_result_bad` | 146 | C | `{==}` | result of a bad parse is none | none (helper pin) |
| `parse_close_arr_empty` | 150 | C | `{==}` | close_arr of an empty stack is bad | none (helper pin) |
| `parse_close_obj_empty` | 154 | C | `{==}` | close_obj of an empty stack is bad | none (helper pin) |
| `parse_put_root` | 158 | C | `{==}` | put of a value as the root | none (helper pin) |
| `parse_step_word` | 162 | C | `{==}` | one token as the root | none (helper pin) |
| `lex_text` | 167 | C | `{==}` | lex text of a reversed buffer | none (helper pin) |
| `lex_unescape_n` | 171 | C | `{==}` | n unescapes to newline | none (helper pin) |
| `lex_hex_A` | 175 | C | `{==}` | hex of A is 10 | none (helper pin) |
| `lex_classify_space` | 179 | C | `{==}` | classify of space is CSpace | none (helper pin) |
| `lex_tokens_null` | 183 | C | `{==}` | parse is finish of run of tokens | none (wiring) |
| `lex_feed_digit` | 188 | C | `{==}` | feed of a digit starts a word | none (helper pin) |
| `lex_run_empty` | 192 | C | `{==}` | run of no chars is the state | none (helper pin) |
| `lex_step_quote` | 196 | C | `{==}` | step of a quote starts a string | none (helper pin) |
| `lex_escape_n` | 201 | C | `{==}` | escape of n in a string | none (helper pin) |
| `lex_unicode` | 205 | C | `{==}` | unicode of the last hex digit | none (helper pin) |
| `lex_finish_idle` | 209 | C | `{==}` | finish of an idle lexer is no tokens | none (helper pin) |
| `value_obj` | 213 | C | `{==}` | RFC 8259 §4: an empty object prints | JSON-PRINT-1 |
| `lazy_stop_true` | 217 | C | `{==}` | stop takes the value when true | none (helper pin) |
| `public_parse` | 221 | C | `{==}` | the public parse | none (wiring) |
| `public_print` | 225 | C | `{==}` | the public print | none (wiring) |
| `public_obj` | 229 | C | `{==}` | the public obj | none (wiring) |
| `public_arr` | 233 | C | `{==}` | RFC 8259 §5: an empty array prints | none (wiring) |
| `public_num` | 237 | C | `{==}` | the public num keeps a JSON number and drops any other text | JSON-NUM-3 |
| `public_get` | 241 | C | `{==}` | the public get | none (wiring) |
| `parse_seps` | 247 | C | `{==}` | RFC 8259 §4 and §5: a missing comma, a trailing comma, a missing colon, and a trailing root comma are rejected | JSON-TEXT-1 |
| `parse_number` | 254 | C | `{==}` | RFC 8259 §6: a number keeps its spelling; a leading zero, a bare minus, a trailing dot, and a leading plus are rejected | JSON-NUM-1 |
| `parse_bad_text` | 260 | C | `{==}` | RFC 8259 §7 and §8.2: a bad escape, a short \\u, a raw line feed, and a lone surrogate are rejected | JSON-STR-2 |
| `parse_surrogate` | 277 | C | `{==}` | RFC 8259 §7: a surrogate pair is one code point | JSON-STR-2 |
| `public_null` | 282 | C | `{==}` | the public null | none (wiring) |
| `public_bool` | 286 | C | `{==}` | the public bool | none (wiring) |
| `public_str` | 290 | C | `{==}` | the public str | none (wiring) |
| `public_at` | 295 | C | `{==}` | the public at | none (wiring) |
| `public_as_bool` | 300 | C | `{==}` | the public as_bool | none (wiring) |
| `public_as_num` | 304 | C | `{==}` | the public as_num | none (wiring) |
| `public_as_u32` | 309 | C | `{==}` | the public as_u32 | JSON-TREE-6 |
| `public_as_f32` | 314 | C | `{==}` | the public as_f32 | none (wiring) |
| `rfc_values` | 347 | C | `{==}` | RFC 8259 §3: null, true, false, a number, a string, an array, and an object parse as those kinds | JSON-TEXT-1 |
| `rfc_literals` | 354 | C | `{==}` | RFC 8259 §3: true, false, and null are lowercase, and a longer word is not one of them | JSON-TEXT-4 |
| `rfc_ws` | 361 | C | `{==}` | RFC 8259 §2: space, tab, line feed, and carriage return are insignificant | JSON-TEXT-2 |
| `rfc_raw_controls` | 390 | C | `{==}` | RFC 8259 §7: a raw U+0000 through U+001F in a string is rejected | JSON-STR-3 |
| `rfc_ws_ctl` | 415 | C | `{==}` | RFC 8259 §2: among U+0000 through U+001F, only tab, line feed, and carriage return are whitespace. U+000B and U+000C are not. | JSON-TEXT-2 |
| `rfc_one` | 419 | C | `{==}` | RFC 8259 §2: a text is one value, with whitespace only around that value | JSON-TEXT-3 |
| `rfc_u_controls` | 463 | C | `{==}` | RFC 8259 §7: \\u0000 through \\u001F are those code points | JSON-STR-2 |
| `rfc_escapes` | 468 | C | `{==}` | RFC 8259 §7: quote, reverse solidus, solidus, and the short controls escape, and \\u reprints the decoded character | JSON-STR-2 |
| `rfc_gen_ctrl` | 477 | C | `{==}` | RFC 8259 §7 and §10: print escapes U+0000 through U+001F | JSON-STR-5 |
| `rfc_cmp` | 486 | C | `{==}` | RFC 8259 §8.3: escaped and unescaped spellings of one string compare equal | JSON-STR-4 |
| `rfc_name` | 492 | C | `{==}` | RFC 8259 §8.3: an object name compares as its decoded characters | JSON-STR-4 |
| `rfc_numbers` | 498 | C | `{==}` | RFC 8259 §6: a JSON number keeps its spelling. NaN, Infinity, a leading plus, and a leading zero are not numbers. | JSON-NUM-1 |
| `rfc_struct` | 513 | C | `{==}` | RFC 8259 §4 and §5: an empty object and an empty array are values, a name is a string, and a trailing comma is rejected | JSON-TEXT-1 |
| `rfc_line_sep` | 521 | C | `{==}` | RFC 8259 §7: U+2028 and U+2029 may occur unescaped in a string | JSON-STR-3 |
| `rfc_bom` | 527 | C | `{==}` | RFC 8259 §8.1: a leading U+FEFF is not whitespace, and print does not emit one | JSON-TEXT-5 |
| `pull_atoms` | 790 | C | `{==}` | RFC 8259 §3: pull reads null, true, and false as those events | JSON-PULL-1 |
| `pull_nums` | 795 | C | `{==}` | RFC 8259 §6: pull keeps a number's spelling | JSON-PULL-1 |
| `pull_text` | 801 | C | `{==}` | RFC 8259 §7: a string with no escapes is a span; an escape is decoded | JSON-PULL-6 |
| `pull_ws` | 807 | C | `{==}` | RFC 8259 §2: space, tab, line feed, and carriage return are not events | JSON-PULL-1 |
| `pull_one` | 812 | C | `{==}` | RFC 8259 §2 and §4: one value, and a trailing comma is rejected | JSON-PULL-2 |
| `pull_bad` | 818 | C | `{==}` | RFC 8259 §7 and §8.1: a raw control, a lone surrogate, and a BOM fail | JSON-PULL-2 |
| `pull_struct` | 824 | C | `{==}` | RFC 8259 §4 and §5: objects and arrays, and a name is a decoded string | JSON-PULL-1 |
| `pull_skip` | 830 | C | `{==}` | skip drops one value. The next event is what followed it | JSON-PULL-4 |
| `pull_span` | 836 | C | `{==}` | a string element of a large object is a span, read one event at a time | JSON-TRUST-3 |
| `pull_rows` | 840 | C | `{==}` | sixty-four string array elements are sixty-four string events, not one parse tree | JSON-TRUST-3 |
| `pull_rows_skip` | 844 | C | `{==}` | skipping the string array still reaches the next key and its number | JSON-PULL-4 |
| `pull_steps` | 848 | C | `{==}` | twenty-four numbers are twenty-seven events: begin, each, end, and done | JSON-PULL-1 |
| `pull_copy` | 852 | C | `{==}` | text copies a number and is none for null | JSON-PULL-6 |
| `pull_hold` | 875 | C | `{==}` | a number in an array leaves the comma unread, including a longer spelling | JSON-TRUST-3 |
| `pull_nest` | 879 | C | `{==}` | nested arrays and objects are events from the outside in | JSON-PULL-1 |
| `public_cursor` | 884 | C | `{==}` | the public cursor and next agree with the pull cursor | none (wiring) |
| `public_next` | 888 | C | `{==}` | the public next reads an object the same way | none (wiring) |
| `public_skip` | 892 | C | `{==}` | the public skip drops the same value the pull skip drops | none (wiring) |
| `public_text` | 897 | C | `{==}` | the public text copies a span the same way | none (wiring) |

## Coverage by requirement

The IDs are the draft rows in the RFC. A count is how many closed laws
illustrate the row. None of them proves it.

| Requirement | Closed laws pointing toward it |
| :---- | :---- |
| JSON-TEXT-1 grammar | `parse_empty`, `parse_unclosed_arr`, `parse_stray`, `parse_unclosed_str`, `parse_mismatch`, `parse_seps`, `rfc_values`, `rfc_struct` |
| JSON-TEXT-2 whitespace | `roundtrip_space`, `rfc_ws`, `rfc_ws_ctl` |
| JSON-TEXT-3 one value | `parse_two_roots`, `rfc_one` |
| JSON-TEXT-4 literals | `roundtrip_null`, `roundtrip_bools`, `rfc_literals` |
| JSON-TEXT-5 BOM | `rfc_bom` |
| JSON-NUM-1 number grammar | `parse_number`, `rfc_numbers` |
| JSON-NUM-2 spelling kept | `roundtrip_nums` |
| JSON-NUM-3 `num` | `public_num` |
| JSON-STR-1 quote round trip | none |
| JSON-STR-2 escapes decode | `roundtrip_escapes`, `parse_bad_text`, `parse_surrogate`, `rfc_u_controls`, `rfc_escapes` |
| JSON-STR-3 raw characters | `rfc_raw_controls`, `rfc_line_sep` |
| JSON-STR-4 names compare decoded | `rfc_cmp`, `rfc_name` |
| JSON-STR-5 print escapes exactly | `rfc_gen_ctrl` |
| JSON-PRINT-1 round trip | `roundtrip_nest`, `print_msg`, `value_obj` |
| JSON-PRINT-2 canonical | none |
| JSON-TREE-1 builders and readers | none (only `wiring` laws) |
| JSON-TREE-2 kinds exclusive | `get_not_num`, `parse_obj_not_str` |
| JSON-TREE-3 `at` | `arr_first` |
| JSON-TREE-4 `get` | `get_uri`, `get_missing` |
| JSON-TREE-5 span and owned agree | `parse_path_chain` |
| JSON-TREE-6 `as_u32` | `get_id`, `public_as_u32` |
| JSON-TREE-7 `as_f32` | none |
| JSON-PULL-1 cursor agrees with `parse` | `pull_atoms`, `pull_nums`, `pull_ws`, `pull_struct`, `pull_steps`, `pull_nest` |
| JSON-PULL-2 failure is sticky | `pull_one`, `pull_bad` |
| JSON-PULL-3 end is sticky | none |
| JSON-PULL-4 `skip` | `pull_skip`, `pull_rows_skip` |
| JSON-PULL-5 `skip` off a value | none |
| JSON-PULL-6 `text` | `pull_text`, `pull_copy` |
| JSON-TRUST-3 cursor memory | `pull_span`, `pull_rows`, `pull_hold` |

## Requirements against code

Each draft row, with a verdict. "Run" means confirmed by the differential
harness or the interface probe below; "reading" means from the source only.

| Requirement | Verdict | Evidence |
| :---- | :---- | :---- |
| JSON-TEXT-1 | holds (run) | 0 disagreements with the strict reference over 2,266 texts, 1,006 of them rejected |
| JSON-TEXT-2 | holds (run, reading) | `lex.bend:64-67` classifies exactly U+0020, U+000A, U+000D, U+0009 as space; `rfc_ws_ctl` is exhaustive over U+0000 to U+001F |
| JSON-TEXT-3 | holds (run) | `parse.bend:171` marks a second root bad |
| JSON-TEXT-4 | holds (run) | `parse.bend:130-139`, `word.ok` compares whole words |
| JSON-TEXT-5 | holds (run) | U+FEFF is `COther`, so it starts a word that is not a number |
| JSON-NUM-1 | holds (run) | the DFA in `value.bend:237-282`; no reference disagreement |
| JSON-NUM-2 | holds (run) | `JNum{raw}` keeps the text; `print.bend:70` writes it back |
| JSON-NUM-3 | holds (run) | `value.bend:285` |
| JSON-STR-1 | partly (run) | holds for strings of Unicode scalar values. A string holding a surrogate code point (`str` of `Char.from_u32(0xD800)`) prints it raw, so the output is not a JSON text that can be encoded in UTF-8; a code point above U+10FFFF prints the same way |
| JSON-STR-2 | holds (run) | `lex.bend:124-200` and the pull copier |
| JSON-STR-3 | partly (run) | U+0000 to U+001F are rejected and every scalar above passes. A raw surrogate code point inside a string literal is accepted (`"\u{d800}"` as a Bend char, not as an escape), which RFC 8259 §8.2 leaves to the implementation |
| JSON-STR-4 | holds (run) | `find.eq` and `span.eq` compare decoded characters |
| JSON-STR-5 | holds (reading) | `print.bend:38-47`; only `"`, `\` and U+0000 to U+001F are escaped |
| JSON-PRINT-1 | partly (run) | holds for values from the builders and from `parse`. Values built with the cell constructors directly print text that is not JSON: `JArr{JNull{}}` prints `[null]` by accident, `JObj{JCons{..}}` prints `{null}`, `JNil{}` prints the empty string, `JNum{"abc"}` prints `abc` |
| JSON-PRINT-2 | holds (run) | the harness compared `print(parse(t))` with the reference's compact form on every accepted text |
| JSON-TREE-1 | holds (reading) | `value.bend:84-108`, `349-372` |
| JSON-TREE-2 | holds (reading) | each `as_*` matches one constructor |
| JSON-TREE-3 | holds (run) | `at([1,2],2)` and `at({},0)` are `null` |
| JSON-TREE-4 | holds (run) | first value of a repeated key, both parsed and built. A missing key and a key whose value is `null` both read as `null` |
| JSON-TREE-5 | holds (run) | an escaped key (`"a\nb"`) is found by its decoded text |
| JSON-TREE-6 | holds (run) | `7` and `4294967295` read; `7.0`, `1e2`, `1E1`, `-0`, `-1`, `0.5`, `4294967296` are none |
| JSON-TREE-7 | fails (run) | `as_f32` of `1e39`, `1e999` is `inf`, of `-1e999` is `-inf`. `main.bend:68` and the README say "none when it … does not fit". `1e-50` reads as `0` |
| JSON-PULL-1 | holds (run) | the harness compared the full event stream with the reference's on every accepted text |
| JSON-PULL-2 | holds (run) | `next` after `EErr` is `EErr` (`pull.bend:1531`) |
| JSON-PULL-3 | holds (run) | `next` after `EEnd` is `EEnd` again |
| JSON-PULL-4 | holds (run) | the event after `skip` of the root is `.` on every accepted text |
| JSON-PULL-5 | holds (run) | `skip` at an object key, at a close bracket, on an empty text, or after the root fails the cursor |
| JSON-PULL-6 | holds (run) | `text` of `ENull`, `EBool` is none; of `EKey` is the key |

## What each entry point reads

ezjson does no IO, so there is no World. Every public def is a pure
function of its arguments. Two reads are worth naming because a law has
to account for them:

| Entry point | Reads besides its arguments | Line |
| :---- | :---- | :---- |
| `as_u32` | `U32.read` from Bend's base library | `value.bend:378` |
| `as_f32` | `F32.read` from Bend's base library | `value.bend:386` |
| `next`, `skip` | a fuel of 2^32 - 1 word jumps; running out returns a failed cursor, not a partial answer | `pull.bend:1430-1446` |

The fuel cannot run out on a text Bend can hold in memory today, but it is
a place where a walk stops and turns into `EErr`, so a law about `next`
must state it or the fuel must go.

## The differential run

A scratch program (not committed; see the RFC's Abandoned Ideas for why it
is not a test) built every text below with `bend -o` and wrote, per text,
`print(parse(t))`, the cursor's full event stream through `pull.bend` and
through `main.bend`, and the event after `skip` of the root. A Python
script compared them with `json.loads` made strict (no `NaN`/`Infinity`,
no leading U+FEFF, no lone surrogate escapes, numbers kept as text,
object pairs kept in order).

- 122 hand-written texts, run once per seed: every row of the README's Compliance list, number
  edge spellings, escapes, surrogate pairs, BOM, U+000B and U+000C,
  duplicate keys, unclosed and mismatched brackets, trailing and missing
  separators, 30-digit and `1e999` numbers.
- 1,900 generated texts over three seeds (2,266 runs in all): random values up to depth four
  with random whitespace, and one random mutation of each.

Result: 0 disagreements. `parse` and the cursor accepted exactly the same
texts as the reference; for each accepted text, `print` gave the
reference's compact form and the cursor gave the reference's events; the
`main.bend` cursor matched `pull.bend` on every text.

## Findings

Recorded, not resolved. The RFC carries a REVIEW item for each one a
requirement depends on.

### Behavior the code guarantees that no requirement mentions

- The cursor and `parse` accept exactly the same texts and agree on
  content (run). This is the property that lets a caller switch from
  `parse` to the cursor for a big text, and nothing states it.
- After `EEnd`, `next` keeps returning `EEnd`; after `EErr`, `EErr` (run).
  Go's `Decoder.Token` behaves the same at end of input.
- `print` of a parsed value is the compact form: no whitespace, the
  original number spelling, strings re-escaped minimally (run).
- `get` returns the first value of a repeated key (run, and README).

### Behavior that looks accidental

- A missing key and a key whose value is `null` are indistinguishable
  through `get` (run). serde_json's `Value::get` returns
  `Option<&Value>`; Jackson has `has` and `get` returning null only for
  missing.
- `get` picks the first of repeated keys (run). serde_json, Go's
  `encoding/json`, Python's `json` and JavaScript's `JSON.parse` all keep
  the last. RFC 8259 §4 says only that behavior with repeated names is
  unpredictable.
- `skip` at an object key fails the cursor (run). .NET's
  `Utf8JsonReader.Skip` on a property name skips the property's value;
  Jackson's `skipChildren` on a field name does nothing.
- `as_u32` reads only a plain digit spelling: `7.0` and `1e2` are none
  (run). serde_json's `as_u64` is also none for any number parsed as a
  float, so this is conventional; it should be a row, not an accident.
- `Json` exposes its list cells (`JNil`, `JCons`, `JPair`) and span forms
  (`JSpan`, `JBind`) as constructors of the public type. Parsed and built
  values of the same JSON differ structurally (`JSpan` against `JStr`), and
  there is no semantic equality. bolt's LSP matches on `J.JStr`, `J.JSpan`,
  `J.JBind`, `J.JCons` and calls `J.arr.go` (bolt v1.4.2, `bolt/lsp/*.bend`),
  so the cells are already depended on downstream.
- Downstream imports `value.bend`, `parse.bend`, `print.bend` and
  `lex.bend` directly, not `main.bend` (bolt v1.4.2). The README documents
  only `main.bend` and `pull.bend`.

### Requirements with no corresponding code

- None found against the README. The README's promise that `as_f32` is
  none when the number does not fit is a requirement the code breaks, below.

### Bugs

- `as_f32` returns `inf` or `-inf` for a number outside the F32 range
  instead of none (run: `1e39`, `1e999`, `-1e999`). The doc comment at
  `main.bend:68` and `value.bend:382`, and the README, say none.
- `print` can write a text that is not JSON: a string holding a surrogate
  code point or one above U+10FFFF is written raw (run), and a value made
  with the cell constructors prints malformed text (run). Whether this is a
  bug depends on REVIEW-3 (what a well-formed value is).
- The README's import line names `0xa3c2445eb44c5d8406e6229be518fccb`.
  bolt's ledger records v0.4.2 at this same commit as
  `0xd9c8d4d2899ddda845dfa7525a3568ea` (reading; the hub was not reachable
  to confirm which one the hub serves). Resolved: the seven files at
  `089d520` match the file hashes bolt's ledger records for `0xd9c8…`.
- bolt's spec (v1.4.2, `docs/rfc/bolt-spec.md` and BOLT-TRUST-8) says "a
  surrogate-pair `\u` escape comes back as invalid UTF-8 (that bug is in
  ezjson)". It does not reproduce in ezjson v0.4.2: `parse` then `print` of
  `"a\ud83d\ude00b"` gives the code points `34 97 128512 98 34`, a key
  spelled with the pair is found by `get` with the character U+1F600, and
  the cursor yields the same character (run). The invalid UTF-8 bolt sees
  is outside ezjson; bolt should be told.

## Progress

| Phase | State | What landed |
| :---- | :---- | :---- |
| Decisions | done | every REVIEW item resolved as recommended |
| Lint first | done | bolt pin `5b05a1b` to v1.4.2 (`9a8fd99`); 248 S004 and 2 S003 fixed; `laws` at warn. 922-text harness and interface probe byte-identical before and after |
| One | done | SPEC.md (31 Proved rows, 4 Trusted); all 99 closed laws and their helpers deleted; `closed`, `unsafe` and `trace` at error, `coverage` at warn; README points at SPEC.md. Also 12 quantified laws: JSON-TREE-1, JSON-TREE-2 and JSON-NUM-3 proved; JSON-TREE-3 and 4 partial (the not-a-container halves) |
| Behavior changes | in progress | `as_f32` overflow landed, JSON-TREE-7 proved (3 laws); `has` and `len` added, JSON-TREE-9 proved (3 laws), JSON-TREE-8 partial (3 laws); `wf` added and `print` writes U+FFFD for a non-scalar, JSON-PRINT-3 partial (4 laws), JSON-STR-5 partial (1 law). README hash fixed to v0.4.2's `0xd9c8…`, checked offline: all seven files of `089d520` match the per-file sha256 bolt's ledger records for that hash. `0xa3c2…` was written in #2 to #4, before the first tagged release. Done |
| Two | in progress | JSON-TREE-4 and JSON-TREE-8 proved: `get` and `has` on a built object are characterized by an empty object, a first key equal to the one asked for, and a first key that differs, with keys compared by `==`. That rests on `find.eq` being string equality (`find_eq_refl`, `find_eq_sound`, `find_eq_false`), which uses bolt's word-equality lemmas (`weq`, `ueq`), copied with attribution. JSON-NUM-1 proved: RFC 8259 §6 written as `number` in LAWS.bend, one def per production with alternatives read in order, and `num.ok` proved equal to it by one lemma per DFA state (`st_start` to `st_bad`). JSON-TREE-3 proved: `at(arr(xs), i)` is `nth(xs, U32.to_nat(i))`, which rests on `u32_dec` (a nonzero U32 is one more than itself minus one, through `Word.adc`); `at` still counts down natively, since a Nat index would be unary. JSON-STR-5 partial: nine laws cover every code point but the 27 controls that take `\u00xx`, which land with JSON-STR-1. JSON-TREE-6 is scheduled last: `U32.read` checks overflow by dividing by ten, so its row needs U32 multiply and divide lemmas, the costliest arithmetic left. JSON-PULL-6 proved (`text`, with `span_take`: a span's text is the first `nn` characters of its source). JSON-PULL-2 and 5 partial: failed cursors and skip after the root. `next.use` now builds the failed and the ended cursor itself, which is what every step already produced (harness and probe byte-identical). The fuel is now a budget of levels (REVIEW-P4 (a), +2.5% on scale at ten times its size), and JSON-PULL-2 and 3 are proved. JSON-PULL-5 proved: skip before a key or at a close bracket, after any whitespace, fails (`go_ws`: the cursor steps over whitespace keeping its state). A top-level skip now refuses a key when it sees the quote, which is where it failed anyway once the key was read. Next: the parser, per docs/rfc/ezjson-parse-proofs.md (WP-L1) |
| Parser, WP-L1 | done | `lexers_agree`: the lexer's span path and its character path give the same tokens up to spans, for texts of at most 2^32 - 1 characters. Lemma only, no row changes; the next packages (WP-L2 printed values, WP-P1 the parser) turn it into rows |
| Parser, WP-L2 | done | `tokens_print`: parse's lexer reads a well-formed value's printed text as the value's tokens, up to spans, with strings fixed as `print` writes them. JSON-STR-1 proved (`str_back`), JSON-STR-5 proved (`esc_ctl` adds the 27 controls written as `\u00xx`). Found that JSON-PRINT-1 is false as worded for strings holding a non-scalar code point, raised as REVIEW-P6 in docs/rfc/ezjson-parse-proofs.md and decided (a): the row now allows for the U+FFFD replacement. |
| Parser, WP-P1 | done | `parse_tj`: the parser on a well-formed value's tokens gives the value back, strings and span keys owned and fixed (`canon`). JSON-PRINT-3 proved: `parse_wf`, every value `parse` returns is well-formed, for every text, as an invariant of the parser's state. |
| Parser, WP-H | done | JSON-PRINT-1 proved (`print_parse`): print then parse gives back a value `same` as the one printed, with every code point that is not a Unicode scalar value replaced by U+FFFD; `same` is decided by `own` in LAWS.bend. `span.eq` refactored to agree with `span.str` past a span's end (harness and probe byte-identical). JSON-PRINT-2 proved (`print_compact`, `print_stable`) and JSON-TREE-5 proved (`get_same`, `at_same`, `as_*_same`). |
| Grammar, WP-G | in progress | JSON-NUM-2 (`parse_num`, `print_num`), JSON-TEXT-3 (`two_none`), JSON-TEXT-4 (`bare_word`) and JSON-TEXT-5 (`bom_none`) proved. JSON-STR-3 proved (`raw_kept`, `ctl_none`). JSON-STR-2 partial (`esc_decodes`, `esc_bad`, `esc_u`, `esc_pair`). Left: JSON-TEXT-1 and 2, the rest of JSON-STR-2, JSON-STR-4 |
| Three to five | open | see the RFC's Rollout |

Laws now: 55, all quantified, 0 closed. `coverage` warnings: 93.
Every new proof was broken on purpose (an absurd case replaced by `{==}`,
a rewrite removed, a statement changed) and the gate failed each time.

