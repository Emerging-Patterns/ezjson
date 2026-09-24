# ezjson: proving the parser and the cursor

## Draft Status

Accepted, written after phase two's small rows landed (SPEC.md at `e9cf214`).
It plans the rows that go through `parse` or the cursor: JSON-TEXT-1 to 5,
JSON-NUM-2, JSON-STR-1 to 4 and the rest of JSON-STR-5, JSON-PRINT-1 and 2,
the parse half of JSON-PRINT-3, JSON-TREE-5 and JSON-PULL-1 to 6. The parent
RFC is `docs/rfc/ezjson-spec.md`; its decisions stand.

- [x] <!-- REVIEW-P1 (resolved): The lexer has two paths. `Lex.tokens` scans with spans (`TStrS`, `TWordS`) and, at the first backslash inside a string, hands the rest of the text to the character machine `Lex.run`. Recommend: keep both, and prove as a lemma that their tokens mean the same (WP-L1). The other option, one path, would make the proofs shorter but touches code the recent performance work tuned, for no change a user sees. Not a behavior change. Decided: accepted as recommended. Keep both lexer paths; WP-L1 proves they agree. -->
- [x] <!-- REVIEW-P2 (resolved): How to prove the cursor. `pull.bend` is its own machine: 1,594 lines, 125 defs, 19 scanner modes, and it shares only character classes with the lexer. JSON-PULL-1 (the cursor's events are the value's events) needs an invariant from every mode to a lexer and parser state, which makes it the most expensive law in the rollout. Recommend: prove the local rows first (PULL-2, 3, 5 and 6: sticky failure, sticky end, where skip fails, text), then spike PULL-1 on texts of scalars and arrays only, and decide with the measured size in hand. Moving PULL-1 to Trusted is the fallback, and it would weaken a row, so it needs your approval. Decided: accepted as recommended. Local cursor rows first, then a PULL-1 spike on scalars and arrays, deciding with its size in hand. -->
- [x] <!-- REVIEW-P4 (resolved): The cursor's fuel cannot be checked. `next.go` runs on a Nat fuel of `U32.to_nat(4294967295)`, and the checker normalizes that term in full, four billion successors, as soon as a law reaches `next` on a live cursor: even `{next.fuel() == next.fuel()}` by reflexivity overflows its stack. Only failed and ended cursors, which never reach `next.go`, can be reasoned about today, which blocks JSON-PULL-1, 3 and 4 and half of 2 and 5. Options: (a) fuel whose normal form is small, a depth of 32 where each level runs the one below twice (2^32 steps, structural recursion on the depth), measured against master with `scale` and the bench since the walk is the tuned hot loop; (b) keep the fuel in `Cur`, which changes a public type; (c) move the live-cursor rows to Trusted, a weakening. Recommend (a), with the measurement in its PR, and (c) only if it costs speed. Decided: accepted as recommended. (a): a fuel of nested budgets, 32 deep, measured against master in its PR. -->
- [x] <!-- REVIEW-P3 (resolved): JSON-TREE-6 (as_u32) goes last. Base's `U32.read` accepts digits by checking that dividing by ten gives back the accumulator, so the row needs U32 multiply and divide lemmas, and nothing else in the rollout does. Recommend: keep it Proved and pending, and do it after the parser. Not a behavior change. Decided: accepted as recommended. JSON-TREE-6 stays Proved and pending and goes last. -->
- [x] <!-- REVIEW-P6 (resolved): JSON-PRINT-1 is false as worded for a string that holds a code point that is not a Unicode scalar value. REVIEW-3 made `print` write U+FFFD for such a code point and kept strings out of `wf`, so `parse(print(str("\u{D800}")))` is a string of U+FFFD, not a value `same` as the one printed. Options: (a) reword the row: "`parse(print(j))` is `Some` of a value `same` as `j` with every code point that is not a Unicode scalar value replaced by U+FFFD"; (b) restrict the row to values whose strings and keys hold only scalar values, as JSON-STR-1 is. Recommend (a): it covers every well-formed value, it says what happens to the other code points, and WP-L2 already proves the lexer half in that form (`tokens_print`, through `fix`). Not a behavior change: it corrects the row to what the code does. Decided: (a). JSON-PRINT-1 reads "`same` as `j` with every code point that is not a Unicode scalar value replaced by U+FFFD". -->
- [x] <!-- REVIEW-P7 (resolved): JSON-TEXT-2 is false as worded. It says inserting any character other than the four whitespace characters before or after a token makes `parse` `None`, but inserting `1` after the `[` of `[1]` gives `[11]` and inserting `-` gives `[-1]`, and both parse. Options: (a) except a digit or `-`, which can make or extend a number; (b) drop the second clause, since JSON-TEXT-1 says which texts parse; (c) narrow it to characters no token holds outside a string. Recommend (a): it keeps RFC 8259 §2's point that only those four are whitespace, and its proof builds on JSON-TEXT-1's grammar. Not a behavior change: it corrects the row to what the code does. Decided: (a). JSON-TEXT-2 reads "inserting any other character there, except a digit or `-` (which can make or extend a number), makes it `None`". -->
- [x] <!-- REVIEW-P8 (resolved): JSON-TEXT-1 is false as worded. RFC 8259's `unescaped` rule stops at U+10FFFF, but a Bend `Char` is any U32, and `parse` keeps a raw character past U+10FFFF inside a string: a string of U+110000 parses (and prints back as U+FFFD), though it matches no `JSON-text`. Options: (a) restrict the row to texts whose characters are all code points, at most U+10FFFF, the only texts RFC 8259 speaks of; (b) make the lexer reject such a character inside a string, a behavior change that costs a comparison per string character in the tuned loop and a rewording of JSON-STR-3; (c) keep only the half "matches the grammar, so `Some`". Recommend (a): no code change, and the claim stays an "exactly when". Outside strings such a character is a word character, and a word holding one is no number, so it makes `parse` `None` as the grammar says. Decided: (a). JSON-TEXT-1 reads "For texts shorter than 2^32 - 1 characters, all of them code points (at most U+10FFFF)". -->

## Update

WP-L1 has landed as `lexers_agree` in `ezjson/PROOF.bend`: for every text
`short` enough (at most 2^32 - 1 characters), `dens(Lex.tokens(s))` equals
`dens` of the character machine's tokens. Where the code differs from the
sketch:

- `rel` relates a scanner state to a lexer state through `dlex` (the state
  with spans replaced), and a word or string's span to the character
  machine's reversed buffer, exactly (`tokens.rev`), not only through `text`.
- Two refactors made the lexer provable, both byte-identical on the
  harness: `escape` and `step.hiesc` test for `u` by code point, and the span
  scanner's mode is an enum (`Span`), not a U32 matched with literals.
- The count's no-wrap fact comes from `pos_ne`, not an ordering lemma.

WP-L2 has landed as `tokens_print`: for every well-formed value `j` whose
text is `short`, `dens(tokens(print(j)))` is `tj(j)`, the value's tokens read
straight off it, with each string's characters fixed as `print` writes them
(`fix`: a scalar value is itself, any other code point U+FFFD). Where the
code differs from the sketch:

- The induction runs on the character machine (`lexp`), and WP-L1 carries it
  to `tokens`. Its invariant is `pend`: after a value's text the machine
  holds the value's tokens, or, for a number or a literal, the open word,
  which the next `,`, `]` or `}` closes (`close`).
- The induction is on the value and its shape together, as `wf.go` is, so
  one law covers values, array cells and object cells. The split on what
  follows a cell is in a helper (`lexp_cons`, `lexp_pair`, `lexp_bind`) that
  takes the induction hypotheses as functions.
- A number's characters are word characters because `number` holds of them
  (`oth_number`, one lemma per grammar def); a string's escapes read back
  one character at a time (`lex_char`), and the 32 controls below U+0020
  are checked one by one (`lex_ctl`).

JSON-STR-1 follows (`str_back`), and so does the rest of JSON-STR-5
(`esc_ctl`, the controls as `\u00` and two lowercase hex digits).

WP-P1 has landed as `parse_tj`: for every well-formed value `j`, running the
parser on `tj(j)` gives `Some{canon(j)}`, the value with its strings and span
keys owned and fixed. The induction (`pv`) is again on the value and its
shape; its invariant is the open frame, `rpush` and `ppush` giving the cells
an array or object frame holds, reversed, and `aslot` and `oslot` its slot.
A number's word is taken as that number because a JSON number is none of the
literals (`step_num`, through `str_eq_sound`).

The parse half of JSON-PRINT-3 landed with it (`parse_wf`): every value
`parse` returns is well-formed, for every text. It is an invariant of the
parser's state (`pinv`: the root and every open frame's cells are
well-formed) that every token keeps (`step_inv`).

JSON-PRINT-1 has landed as `print_parse`, the first part of WP-H. Parsing
commutes with reading spans out: `ownp` of the parser's state after a token is
the parser's state, owned, after that token with its span read out
(`step_own`), so `own` of `parse(print(j))` is the parser on `dens` of the
tokens, which WP-L2 and WP-P1 finish. `canon` is then the spec's
`fixv(own(j))` (`canon_fix`). One refactor made a word span provably act as
its word: `span.eq` now agrees with `span.str` when a span's count runs past
the end of its source (`span_eq_go`). `parse` never builds such a span, and
the harness and the interface probe print the same bytes; for a hand-built
value with one, `get` now finds the key the value prints.

WP-H is done. JSON-TREE-5: each reader commutes with `own`, so a span reads
as its characters (`get_same`, `at_same`, `as_*_same`); for `get`, a span key
compares as the key it covers (`span_find`, through `find.eq` being
`String.eq`). The laws hold for every value, not only parsed ones.
JSON-PRINT-2: printing ignores spans and the U+FFFD fix (`print_own`,
`print_fix`), so a parsed value, printed, parsed and printed again, prints the
same (`print_stable`); and a well-formed value's text leaves no whitespace
outside strings (`print_compact`), where "outside strings" is a four-state
scan written from RFC 8259 §7 in LAWS.bend (`tx.step`).

WP-G has started with the rows the round trip gives cheaply. JSON-NUM-2
(`parse_num`) is JSON-PRINT-1 on a number: only a number owns as a number.
JSON-TEXT-4 (`bare_word`) and JSON-TEXT-5 (`bom_none`) go through the
character lexer: a bare word lexes as one word token, and a text that starts
with U+FEFF lexes with a first token the parser rejects (the word it starts,
or the error token). Once the parser's error flag is raised no token lowers it
(`step_bad`). "Bare word" is written in LAWS.bend (`bare`: one or more
characters that are not whitespace, not structural, not `"` or `\`), and so
are the literals and numbers it may be (`lit_or_num`).
JSON-TEXT-3 (`two_none`): the character lexer reads two values' text, a
space between, as the first value's tokens then the second's (`two_lex`,
through WP-L2's `lexp`); the parser takes the first as the root (WP-P1's
`pv`), and the second value's first token then raises the error flag
(`after_root`).
JSON-STR-3: a raw character other than a control, `"` or `\` is kept
(`raw_kept`, through STR-1's `one_str`); and a raw control inside a string
makes `parse` `None` for every text (`ctl_none`). "Inside a string" is a
four-state scan written from RFC 8259 §7 in LAWS.bend (`cs.step`), and the
proof keeps it in step with the character lexer's mode (`okm`, `tr_m`): once
the scan meets a raw control inside a string, the lexer is rejecting, so its
tokens hold the error token, which the parser never gets past.
JSON-STR-2: the two-character escapes decode inside a string of
raw characters, and a backslash before anything else but `u` rejects the
text whatever follows (`esc_decodes`, `esc_bad`); `\u` and four hex digits
of a non-surrogate decode to that code point (`esc_u`), and a high then low
surrogate escape to the code point UTF-16 pairs them to (`esc_pair`). The
escape table, hex digits and the pair rule are written in LAWS.bend from
RFC 8259 §7 (`unesc`, `hexd`, `hex4`, `pair`). A `\u` not followed by four
hex digits (`esc_u_bad`), a low surrogate escape with no high one before it
(`esc_lo_bad`), and a high surrogate escape not followed by a low one
(`esc_hi_bad`) reject the text. Each leaves the lexer rejecting or inside an
escape when the text ends, so its tokens hold the error token (`uni_rej`,
`lo_rej`, `hi_rej`, `lex_none`).
JSON-STR-4: a member name is spelled as any list of pieces, each a raw
character, a two-character escape, a `\u` escape, or a surrogate pair
(`Piece`, `spell`, `spelled` in LAWS.bend). `get` on the parsed one-member
object finds the member exactly when the key equals the characters the
pieces stand for (`get_decoded`). The name's characters are taken to be
Unicode scalar values, as the characters of any Unicode text are. The
proof reads the pieces with the character lexer (`piece_lex`,
`spell_lex`), lands in the state the printed object leaves (`obj_lex`),
and takes the parse from `print_parse`'s lemmas (`parse_obj`). `get`
then compares with `find.eq`, which is `String.eq` (`find_str_eq`).
Walking past the other members of a longer object is `get_hit` and
`get_miss`; spans are TREE-5's `get_same`.
JSON-TEXT-1, the half from the grammar to `Some`: a derivation is a tree
with one constructor per rule of §2 to §7, whitespace fields where §2 allows
whitespace, and pieces for strings (`Gv`, `g.text`, `g.ok`, `g.val` in
LAWS.bend). A text of whitespace, a well-formed derivation's text and
whitespace parses, as the value the derivation stands for (`text_some`).
The character lexer reads a derivation's text to its value's tokens by
induction on the tree (`lexg`): a value's text leaves the lexer between
tokens or inside a word (`gend`, `iw`, `fl`), whitespace then punctuation
pushes the word (`ws_punct`), and a string or a member's name is its token
(`str_in`, `mem_in`). The parser half is WP-P1's, over a copy of `tj` that
keeps strings as they are rather than fixed as print writes them (`tj_r`,
`pv_r`, `parse_tjr`): the derivation's strings may hold code points that
are not scalar values. `tj` and its parser lemma now follow from that copy
through `fxv`, which fixes a value's strings (`tj_fx`, `canon_fx`, `wf_fx`),
so the parser induction is written once. The other half: a text that
parses is whitespace, a derivation's text and whitespace (`text_derives`,
with `derived` saying the whitespace is whitespace and the derivation follows
the rules). Its parser step: a token list the
parser accepts, spans replaced, is exactly its value's tokens
(`parse_toks`). The invariant pairs each state that has not failed with
the tokens it has read, reversed (`rs`, `ti`): a frame's cells, the
separator after them, and a key and colon waiting for a value; a frame
waiting after a value holds cells (`sok`). Each token keeps it
(`step_ti`), and a finished state has read its root's tokens (`fin_ti`).
Its lexer step: the character lexer's state after any text is described by
`jl`, one case per mode. Between tokens or in a word, the text read is the
lexemes read (`Lx`, `It`: a punctuation character, a word, or a string's
pieces, each after its whitespace), then whitespace, then the word; in a
string, it is also the pieces read so far and, in an escape, the escape's
characters so far (`uj` for a `\u` escape's digits, `hj` for a high
surrogate's). Each character keeps it (`jstep`, with a lemma per mode:
`j_idle`, `j_word`, `j_str`, `j_esc`, `j_uni`, `j_hi`, `j_hiesc`, `j_lo`), so
the whole text does (`jrun`). The lexemes' tokens are the lexer's, and each
string's pieces are well spelled; the facts about a character come back out of
the lexer's own tests (`cls_space`, `rawc`, `sur_inv`).
The derivation is then read off the lexemes, walking the value the tokens
parse to (`bld`, by shape: a value, or an array's or object's cells and
their closing bracket). Each lexeme's whitespace goes where §2 puts it, a
punctuation lexeme's token names its character (`lp_inv`), and the lexemes
spell the derivation's text (`fr`, `rc_inj`). A text that parses leaves the
lexer between tokens or in a word (`lnb`, `lx_fin`), since any other mode
ends in the error token. `derived` checks a raw string character against
`raw_char`, which also admits a code point past U+10FFFF; for the texts
JSON-TEXT-1 is about, whose characters are all code points (REVIEW-P8), that
is RFC 8259's `unescaped`, so the two laws together are the row.

## What parse does

| |
|:---:|
| <pre>text ──Lex.tokens──▶ tokens ──Parse.run──▶ P{bad, root, stack} ──Parse.finish──▶ Maybe Json</pre> |
| Caption: `parse` is a lexer, a stack machine over tokens, and a check that nothing is left open. |

- `Lex.tokens` walks the text once. While no string has a backslash it keeps
  a word or a string as a span of the text (`TWordS{cut, n}`, `TStrS{cut, n}`),
  so nothing is copied. At the first backslash in a string it rebuilds the
  string so far into a buffer and runs `Lex.run`, the character machine, on
  the rest of the text.
- `Lex.run` is a fold of `Lex.feed` over the characters, so running it on
  `xs ++ ys` is running it on `ys` from where `xs` left it. That is what makes
  a printed value, which is a concatenation, tractable.
- `Parse.run` is a fold of `Parse.step` over the tokens. `P.bad` never goes
  back to false once set, and `Parse.finish` answers `Some` only with no
  error, no open frame and a root.

## The plan

Each row keeps the wording SPEC.md has. The laws are stated over `main.bend`
where the row talks about the interface, and over `Lex` and `Parse` only in
lemmas.

**Token meaning.** `den` maps a token to its owned form: a span becomes the
characters it covers. Two token lists mean the same when their `den`s are
equal. Every lexer lemma is stated modulo `den`, so the span path and the
buffer path can be compared.

**WP-L1, the two lexer paths agree.** For every text,
`den(Lex.tokens(s)) == den(Lex.finish(Lex.run(String.to_list(s), Lex0)))`.
The invariant pairs each `Scan` state with a `Lex` state: `Go` in word or
string mode with `cut` holding exactly the characters the buffer holds,
reversed, and `Old{lex}` with `lex`. This is the spike: every parse row goes
through it, and it tests the list lemmas (take and drop over a suffix) the
rest needs.

**WP-L2, lexing a printed value.** For every well-formed `j`,
`den(tokens(print(j)))` is `toks(j)`, the token list read straight off the
value: a bracket per container, a colon and a comma where they go, `TStr`
of each decoded string and `TWord` of each number or literal. The string
case is JSON-STR-1 at the token level. It includes the `\u00xx` controls
that JSON-STR-5 still misses, since the lexer reads them back.

**WP-P1, the parser on a value's tokens.** For every well-formed `j`,
running `Parse.run` over `toks(j) ++ rest` from a state that can take a value
is running it over `rest` after `put` of `j`. The induction is on `j`, with
the open frames as the invariant.

**WP-H, the headline.** JSON-PRINT-1 is WP-L2 then WP-P1 then `finish`,
together with `same` (a span and its characters are the same value).
JSON-PRINT-2 follows from it and from the printer writing no whitespace.
JSON-TREE-5 (a reader answers the same on a span and on its characters)
comes with `same`.

**WP-G, the grammar.** `Derives(t, j)` transcribes RFC 8259 §2 to §7, one
constructor per ABNF rule, reusing JSON-NUM-1's `number`. JSON-TEXT-1 is
`parse(t) == Some{j}` exactly when `Derives(t, j')` for a `j'` that is `same`
as `j`. JSON-TEXT-2 to 5, JSON-NUM-2 and JSON-STR-2 to 4 are corollaries,
though some are cheaper to prove directly on the lexer, and those land
first.

**WP-C, the cursor.** REVIEW-P2.

| |
|:---:|
| <pre>WP-L1 ──▶ WP-L2 ──▶ WP-P1 ──▶ WP-H ──▶ WP-G<br>                                   └──▶ WP-C (PULL-1)<br>WP-C local (PULL-2, 3, 5, 6): no dependency</pre> |
| Caption: the work packages. The local cursor rows can start at any time. |

| WP | Rows | Needs | Effort |
| :---- | :---- | :---- | :---- |
| WP-L1 | none (lemma) | take and drop lemmas over String | large |
| WP-L2 | JSON-STR-1, rest of JSON-STR-5 | WP-L1, `\u` hex lemmas | large |
| WP-P1 | parse half of JSON-PRINT-3 | WP-L2 | medium |
| WP-H | JSON-PRINT-1, JSON-PRINT-2, JSON-TREE-5 | WP-P1 | medium |
| WP-G | JSON-TEXT-1 to 5, JSON-NUM-2, JSON-STR-2 to 4 | WP-H, JSON-NUM-1 | large |
| WP-C local | JSON-PULL-2, 3, 5, 6 | none | small to medium |
| WP-C | JSON-PULL-1, JSON-PULL-4 | WP-H, REVIEW-P2 | largest |
| last | JSON-TREE-6 | U32 multiply and divide lemmas | medium |

## Risks

- **The span invariant is harder than it looks.** A span token holds the
  whole rest of the text, not just its own characters, so the invariant has
  to say exactly which prefix of `cut` a token covers. The spike measures
  this before anything builds on it.
- **Proof size.** bolt's rule proofs run to tens of thousands of lines. Keep
  the lemmas in PROOF.bend general, and keep the gate's time in view (5 s
  today).
- **The cursor may not be worth proving as is.** REVIEW-P2's spike is there
  so we find out before spending the effort, and the fallback is a visible
  weakening you approve.
