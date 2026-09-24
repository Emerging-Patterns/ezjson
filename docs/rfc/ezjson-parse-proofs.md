# ezjson: proving the parser and the cursor

## Draft Status

Draft, written after phase two's small rows landed (SPEC.md at `e9cf214`).
It plans the rows that go through `parse` or the cursor: JSON-TEXT-1 to 5,
JSON-NUM-2, JSON-STR-1 to 4 and the rest of JSON-STR-5, JSON-PRINT-1 and 2,
the parse half of JSON-PRINT-3, JSON-TREE-5 and JSON-PULL-1 to 6. The parent
RFC is `docs/rfc/ezjson-spec.md`; its decisions stand.

- [ ] <!-- REVIEW-P1: The lexer has two paths. `Lex.tokens` scans with spans (`TStrS`, `TWordS`) and, at the first backslash inside a string, hands the rest of the text to the character machine `Lex.run`. Recommend: keep both, and prove as a lemma that their tokens mean the same (WP-L1). The other option, one path, would make the proofs shorter but touches code the recent performance work tuned, for no change a user sees. Not a behavior change. -->
- [ ] <!-- REVIEW-P2: How to prove the cursor. `pull.bend` is its own machine: 1,594 lines, 125 defs, 19 scanner modes, and it shares only character classes with the lexer. JSON-PULL-1 (the cursor's events are the value's events) needs an invariant from every mode to a lexer and parser state, which makes it the most expensive law in the rollout. Recommend: prove the local rows first (PULL-2, 3, 5 and 6: sticky failure, sticky end, where skip fails, text), then spike PULL-1 on texts of scalars and arrays only, and decide with the measured size in hand. Moving PULL-1 to Trusted is the fallback, and it would weaken a row, so it needs your approval. -->
- [ ] <!-- REVIEW-P4: The cursor's fuel cannot be checked. `next.go` runs on a Nat fuel of `U32.to_nat(4294967295)`, and the checker normalizes that term in full, four billion successors, as soon as a law reaches `next` on a live cursor: even `{next.fuel() == next.fuel()}` by reflexivity overflows its stack. Only failed and ended cursors, which never reach `next.go`, can be reasoned about today, which blocks JSON-PULL-1, 3 and 4 and half of 2 and 5. Options: (a) fuel whose normal form is small, a depth of 32 where each level runs the one below twice (2^32 steps, structural recursion on the depth), measured against master with `scale` and the bench since the walk is the tuned hot loop; (b) keep the fuel in `Cur`, which changes a public type; (c) move the live-cursor rows to Trusted, a weakening. Recommend (a), with the measurement in its PR, and (c) only if it costs speed. -->
- [ ] <!-- REVIEW-P3: JSON-TREE-6 (as_u32) goes last. Base's `U32.read` accepts digits by checking that dividing by ten gives back the accumulator, so the row needs U32 multiply and divide lemmas, and nothing else in the rollout does. Recommend: keep it Proved and pending, and do it after the parser. Not a behavior change. -->

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
