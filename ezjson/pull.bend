# ezjson/pull: one JSON text, one event at a time.
# `cursor` holds the unread suffix of the source. `next` returns one event and
# the cursor after it. `skip` drops one value. A span event keeps the suffix
# it points at, so it stays readable while that event is held and is gone
# when the event is dropped. Commas and colons are not events.
import Base
import ./value.bend as V
import ./lex.bend as Lex

# where the next token of an open array or object has to be
type Slot is Data:
  SVal{}
  SCom{}
  SKey{}
  SCol{}

# an open array or object. `fresh` is the empty container, before any value
type Frame is Data:
  FArr{slot: Slot, fresh: Bool}
  FObj{slot: Slot, fresh: Bool}

# one event. A span is the first `nn` chars of a source suffix, not a copy
type Ev is Data:
  ENull{}
  EBool{b: Bool}
  ENum{src: String, nn: U32}
  EStr{body: String}
  EStrS{src: String, nn: U32}
  EKey{body: String}
  EKeyS{src: String, nn: U32}
  EBeginArr{}
  EEndArr{}
  EBeginObj{}
  EEndObj{}
  EEnd{}
  EErr{}

# the cursor. `rest` is the unread suffix. `done` is set once the root value
# has ended. `bad` sticks after the first error
type Cur is Data:
  Cur{rest: String, stack: List<&2, Frame>, done: Bool, bad: Bool}

# read the next event, or drop one whole value
type Goal is Data:
  GNext{}
  GSkip{depth: Nat}

# what a step hands back: an event, or a finished skip
type Stop is Data:
  SEv{ev: Ev}
  SSkip{}

# a bare word, once it has been classified
type Atom is Data:
  ANull{}
  ATrue{}
  AFalse{}
  ANum{}
  ABad{}

# a string's text: a span of the source, or chars decoded from escapes
type Piece is Data:
  PSpan{cut: String, nn: U32}
  POwn{body: String}

# what one character of a string does. The usual one is KGo: stay in the
# string. The others leave it
type Skind is Data:
  KGo{}
  KEnd{}
  KEsc{}
  KBad{}

# where a finished value lands, or that the slot cannot take one
type Spot is Data:
  Spot{stack: List<&2, Frame>, root: Bool}
  SpotBad{}

# what the scanner is inside. Skip-modes (`MSk*`) walk a string they will
# not keep, so a dropped value does not build its text
type Mode is Data:
  MIdle{}
  # a bare word's characters, reversed, so the unread array is not kept
  MWord{buf: List<&2, Char>, nn: U32, num: V.Num}
  MSpan{cut: String, nn: U32}
  MCopy{buf: List<&2, Char>}
  MEsc{buf: List<&2, Char>}
  MUni{left: Nat, acc: U32, buf: List<&2, Char>}
  MHi{hi: U32, buf: List<&2, Char>}
  MHiEsc{hi: U32, buf: List<&2, Char>}
  MLo{left: Nat, acc: U32, hi: U32, buf: List<&2, Char>}
  MSkStr{}
  MSkEsc{}
  MSkUni{left: Nat, acc: U32}
  MSkHi{hi: U32}
  MSkHiEsc{hi: U32}
  MSkLo{left: Nat, acc: U32, hi: U32}
  MDone{stop: Stop, saved: String}
  # the cursor rest is the suffix the stepper is already on, so closing a
  # long string does not keep that suffix a second time
  MRest{stop: Stop}
  # the quote is consumed; the next character is the first of the string
  MQuote{}
  # resume `mode` on `rest` after a plain word, which the stepper did not
  # walk byte by byte
  MJump{rest: String, mode: Mode}

# the scanner's state, apart from the unread suffix it is walking
type St is Data:
  S{mode: Mode, stack: List<&2, Frame>, goal: Goal, done: Bool, bad: Bool}

# a failed step. The unread suffix is dropped
def err.st(goal: Goal) -> St:
  S{MDone{SEv{EErr{}}, ""}, Nil{}, goal, False{}, True{}}

# a failed cursor
def bad.cur() -> (Stop & Cur):
  (SEv{EErr{}}, Cur{"", Nil{}, False{}, True{}})

# the first `nn` chars of `src`, reversed, for the escape copier
def copy.rev(src: String, +nn: U32, zero: Bool, acc: List<&2, Char>) -> List<&2, Char>:
  match src zero:
    case s True{}:
      acc
    case SNil{} False{}:
      acc
    case SCon{h, t} False{}:
      copy.rev(t, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), h <> acc)

# a value can start here
def expect.val.go(stack: List<&2, Frame>) -> Bool:
  match stack:
    case Nil{}:
      True{}
    case Con{FArr{SVal{}, fresh}, rest}:
      True{}
    case Con{FObj{SVal{}, fresh}, rest}:
      True{}
    case other:
      False{}

# a value can start here, and the root is not already finished
def expect.val(stack: List<&2, Frame>, done: Bool) -> Bool:
  match done:
    case True{}:
      False{}
    case False{}:
      expect.val.go(stack)

# a string can start here: a value, or an object key
def expect.str.go(stack: List<&2, Frame>) -> Bool:
  match stack:
    case Nil{}:
      True{}
    case Con{FArr{SVal{}, fresh}, rest}:
      True{}
    case Con{FObj{SVal{}, fresh}, rest}:
      True{}
    case Con{FObj{SKey{}, fresh}, rest}:
      True{}
    case other:
      False{}

# a string can start here, and the root is not already finished
def expect.str(stack: List<&2, Frame>, done: Bool) -> Bool:
  match done:
    case True{}:
      False{}
    case False{}:
      expect.str.go(stack)

# the stack after a value, and whether that value was the root
def place.spot(stack: List<&2, Frame>) -> Spot:
  match stack:
    case Nil{}:
      Spot{Nil{}, True{}}
    case Con{FArr{SVal{}, fresh}, frames}:
      Spot{FArr{SCom{}, False{}} <> frames, False{}}
    case Con{FObj{SVal{}, fresh}, frames}:
      Spot{FObj{SCom{}, False{}} <> frames, False{}}
    case other:
      SpotBad{}

# a value has landed in a slot that can take it
def place.val.ok(ev: Ev, rest: String, goal: Goal, stack: List<&2, Frame>, root: Bool) -> St:
  match goal:
    case GNext{}:
      S{MDone{SEv{ev}, rest}, stack, GNext{}, root, False{}}
    case GSkip{0n}:
      S{MDone{SSkip{}, rest}, stack, GSkip{0n}, root, False{}}
    case GSkip{1n+left}:
      S{MIdle{}, stack, GSkip{1n+left}, False{}, False{}}

# a value has landed. `rest` is the suffix the cursor keeps
def place.val.on(ev: Ev, rest: String, goal: Goal, spot: Spot) -> St:
  match spot:
    case SpotBad{}:
      err.st(goal)
    case Spot{stack, root}:
      place.val.ok(ev, rest, goal, stack, root)

# a value has landed
def place.val(ev: Ev, rest: String, stack: List<&2, Frame>, goal: Goal) -> St:
  place.val.on(ev, rest, goal, place.spot(stack))

# an object key has landed. The value comes after the colon
def place.key(ev: Ev, rest: String, frames: List<&2, Frame>, goal: Goal) -> St:
  match goal:
    case GNext{}:
      S{MDone{SEv{ev}, rest}, FObj{SCol{}, False{}} <> frames, goal, False{}, False{}}
    case GSkip{0n}:
      err.st(goal)
    case GSkip{1n+left}:
      S{MIdle{}, FObj{SCol{}, False{}} <> frames, goal, False{}, False{}}

# a string event, span or owned, as a key or a value
def str.ev(piece: Piece, key: Bool) -> Ev:
  match piece key:
    case PSpan{cut, nn} True{}:
      EKeyS{cut, nn}
    case PSpan{cut, nn} False{}:
      EStrS{cut, nn}
    case POwn{body} True{}:
      EKey{body}
    case POwn{body} False{}:
      EStr{body}

# a string value inside a skip, once the slot is known
def str.cont.on(goal: Goal, spot: Spot) -> St:
  match spot:
    case SpotBad{}:
      err.st(goal)
    case Spot{stack2, root}:
      S{MIdle{}, stack2, goal, False{}, False{}}

# a string value inside a skip: keep the slot, not the text
def str.cont(stack: List<&2, Frame>, goal: Goal) -> St:
  str.cont.on(goal, place.spot(stack))

# a string value. A skip that is still inside a container keeps scanning
def str.val(ev: Ev, rest: String, stack: List<&2, Frame>, goal: Goal) -> St:
  match goal:
    case GSkip{1n+left}:
      str.cont(stack, goal)
    case GNext{}:
      place.val(ev, rest, stack, goal)
    case GSkip{0n}:
      place.val(ev, rest, stack, goal)

# a finished string. A key goes to the open object; anything else is a value
def str.place(piece: Piece, rest: String, stack: List<&2, Frame>, goal: Goal) -> St:
  match stack:
    case Con{FObj{SKey{}, fresh}, frames}:
      place.key(str.ev(piece, True{}), rest, frames, goal)
    case other:
      str.val(str.ev(piece, False{}), rest, stack, goal)

# a string a skip will not keep
def str.skip(rest: String, stack: List<&2, Frame>, goal: Goal) -> St:
  match goal:
    case GNext{}:
      err.st(goal)
    case GSkip{depth}:
      str.place(POwn{""}, rest, stack, goal)

# a value has landed, and the cursor rest is the suffix already in hand
def place.val.ok.here(ev: Ev, goal: Goal, stack: List<&2, Frame>, root: Bool) -> St:
  match goal:
    case GNext{}:
      S{MRest{SEv{ev}}, stack, GNext{}, root, False{}}
    case GSkip{0n}:
      S{MRest{SSkip{}}, stack, GSkip{0n}, root, False{}}
    case GSkip{1n+left}:
      S{MIdle{}, stack, GSkip{1n+left}, False{}, False{}}

# a value has landed on the suffix in hand, once the slot is known
def place.val.on.here(ev: Ev, goal: Goal, spot: Spot) -> St:
  match spot:
    case SpotBad{}:
      err.st(goal)
    case Spot{stack, root}:
      place.val.ok.here(ev, goal, stack, root)

# a value has landed on the suffix in hand
def place.val.here(ev: Ev, stack: List<&2, Frame>, goal: Goal) -> St:
  place.val.on.here(ev, goal, place.spot(stack))

# an object key has landed on the suffix in hand
def place.key.here(ev: Ev, frames: List<&2, Frame>, goal: Goal) -> St:
  match goal:
    case GNext{}:
      S{MRest{SEv{ev}}, FObj{SCol{}, False{}} <> frames, goal, False{}, False{}}
    case GSkip{0n}:
      err.st(goal)
    case GSkip{1n+left}:
      S{MIdle{}, FObj{SCol{}, False{}} <> frames, goal, False{}, False{}}

# a string value on the suffix in hand. A skip inside a container keeps scanning
def str.val.here(ev: Ev, stack: List<&2, Frame>, goal: Goal) -> St:
  match goal:
    case GSkip{1n+left}:
      str.cont(stack, goal)
    case GNext{}:
      place.val.here(ev, stack, goal)
    case GSkip{0n}:
      place.val.here(ev, stack, goal)

# a finished string whose rest is the suffix the stepper is on
def str.place.here(piece: Piece, stack: List<&2, Frame>, goal: Goal) -> St:
  match stack:
    case Con{FObj{SKey{}, fresh}, frames}:
      place.key.here(str.ev(piece, True{}), frames, goal)
    case other:
      str.val.here(str.ev(piece, False{}), stack, goal)

# a skipped string closed on the suffix in hand
def str.skip.here(stack: List<&2, Frame>, goal: Goal) -> St:
  match goal:
    case GNext{}:
      err.st(goal)
    case GSkip{depth}:
      str.place.here(POwn{""}, stack, goal)

# one character of a string: stay in it, close it, start an escape, or fail
def span.kind(cls: Lex.Class, ctrl: Bool) -> Skind:
  match cls ctrl:
    case Lex.CQuote{} c:
      KEnd{}
    case Lex.CBack{} False{}:
      KEsc{}
    case k True{}:
      KBad{}
    case k False{}:
      KGo{}

# classify one string character. `ch` is a code point, so the keep is a word
def span.kind.of(+ch: Char) -> Skind:
  span.kind(Lex.classify(ch), U32.is_lt(Char.to_u32(ch), 32))

# `]` or `}` of a skip: depth 1 finishes the value, deeper keeps going.
# The cursor rest is the suffix the stepper is already on
def close.skip.go(stack: List<&2, Frame>, left: Nat, root: Bool) -> St:
  match left:
    case 0n:
      S{MRest{SSkip{}}, stack, GSkip{0n}, root, False{}}
    case 1n+more:
      S{MIdle{}, stack, GSkip{1n+more}, False{}, False{}}

# `]` or `}` of a skip, once the frame has been popped
def close.skip(stack: List<&2, Frame>, depth: Nat, root: Bool) -> St:
  match depth:
    case 0n:
      err.st(GSkip{0n})
    case 1n+left:
      close.skip.go(stack, left, root)

# the parent after a container closes, for a reader
def close.next(ev: Ev, stack: List<&2, Frame>, root: Bool) -> St:
  S{MRest{SEv{ev}}, stack, GNext{}, root, False{}}

# a container closed. `frames` is the stack with that frame popped
def close.out(ev: Ev, frames: List<&2, Frame>, goal: Goal) -> St:
  match frames goal:
    case Nil{} GNext{}:
      close.next(ev, Nil{}, True{})
    case Nil{} GSkip{depth}:
      close.skip(Nil{}, depth, True{})
    case Con{FArr{SVal{}, fresh}, outer} GNext{}:
      close.next(ev, FArr{SCom{}, False{}} <> outer, False{})
    case Con{FObj{SVal{}, fresh}, outer} GNext{}:
      close.next(ev, FObj{SCom{}, False{}} <> outer, False{})
    case Con{FArr{SVal{}, fresh}, outer} GSkip{depth}:
      close.skip(FArr{SCom{}, False{}} <> outer, depth, False{})
    case Con{FObj{SVal{}, fresh}, outer} GSkip{depth}:
      close.skip(FObj{SCom{}, False{}} <> outer, depth, False{})
    case frames2 g:
      err.st(g)

# a `]`. Empty, or just after a value
def close.arr(stack: List<&2, Frame>, goal: Goal) -> St:
  match stack:
    case Con{FArr{SVal{}, True{}}, frames}:
      close.out(EEndArr{}, frames, goal)
    case Con{FArr{SCom{}, fresh}, frames}:
      close.out(EEndArr{}, frames, goal)
    case other:
      err.st(goal)

# a `}`. Empty, or just after a value
def close.obj(stack: List<&2, Frame>, goal: Goal) -> St:
  match stack:
    case Con{FObj{SKey{}, True{}}, frames}:
      close.out(EEndObj{}, frames, goal)
    case Con{FObj{SCom{}, fresh}, frames}:
      close.out(EEndObj{}, frames, goal)
    case other:
      err.st(goal)

# a comma between values, or between object members
def punct.comma(stack: List<&2, Frame>, goal: Goal) -> St:
  match stack:
    case Con{FArr{SCom{}, fresh}, frames}:
      S{MIdle{}, FArr{SVal{}, False{}} <> frames, goal, False{}, False{}}
    case Con{FObj{SCom{}, fresh}, frames}:
      S{MIdle{}, FObj{SKey{}, False{}} <> frames, goal, False{}, False{}}
    case other:
      err.st(goal)

# a colon after a key
def punct.colon(stack: List<&2, Frame>, goal: Goal) -> St:
  match stack:
    case Con{FObj{SCol{}, fresh}, frames}:
      S{MIdle{}, FObj{SVal{}, False{}} <> frames, goal, False{}, False{}}
    case other:
      err.st(goal)

# `[` pushed. A reader returns the begin; a skip counts the container
def punct.arr.go(stack: List<&2, Frame>, goal: Goal) -> St:
  match goal:
    case GNext{}:
      S{MRest{SEv{EBeginArr{}}}, stack, goal, False{}, False{}}
    case GSkip{depth}:
      S{MIdle{}, stack, GSkip{1n+depth}, False{}, False{}}

# `[`, once it is known whether a value may start
def punct.arr.if(stack: List<&2, Frame>, goal: Goal, ok: Bool) -> St:
  match ok:
    case True{}:
      punct.arr.go(FArr{SVal{}, True{}} <> stack, goal)
    case False{}:
      err.st(goal)

# `[`, when a value may start
def punct.arr(+stack: List<&2, Frame>, goal: Goal, done: Bool) -> St:
  punct.arr.if(stack, goal, expect.val(stack, done))

# `{` pushed
def punct.obj.go(stack: List<&2, Frame>, goal: Goal) -> St:
  match goal:
    case GNext{}:
      S{MRest{SEv{EBeginObj{}}}, stack, goal, False{}, False{}}
    case GSkip{depth}:
      S{MIdle{}, stack, GSkip{1n+depth}, False{}, False{}}

# `{`, once it is known whether a value may start
def punct.obj.if(stack: List<&2, Frame>, goal: Goal, ok: Bool) -> St:
  match ok:
    case True{}:
      punct.obj.go(FObj{SKey{}, True{}} <> stack, goal)
    case False{}:
      err.st(goal)

# `{`, when a value may start
def punct.obj(+stack: List<&2, Frame>, goal: Goal, done: Bool) -> St:
  punct.obj.if(stack, goal, expect.val(stack, done))

# one punctuation token, once the root is still open. The suffix stays
# with the stepper: a bracket closes on it, and a comma does not keep it
def punct.go(tok: Lex.Tok, stack: List<&2, Frame>, goal: Goal, done: Bool) -> St:
  match tok:
    case Lex.TOpenArr{}:
      punct.arr(stack, goal, done)
    case Lex.TOpenObj{}:
      punct.obj(stack, goal, done)
    case Lex.TCloseArr{}:
      close.arr(stack, goal)
    case Lex.TCloseObj{}:
      close.obj(stack, goal)
    case Lex.TColon{}:
      punct.colon(stack, goal)
    case Lex.TComma{}:
      punct.comma(stack, goal)
    case other:
      err.st(goal)

# one punctuation token
def punct.on(tok: Lex.Tok, stack: List<&2, Frame>, goal: Goal, done: Bool) -> St:
  match done:
    case True{}:
      err.st(goal)
    case False{}:
      punct.go(tok, stack, goal, done)

# whitespace, kept as the same state
def idle.space(stack: List<&2, Frame>, goal: Goal, done: Bool) -> St:
  S{MIdle{}, stack, goal, done, False{}}

# a `"` may open a string here
def look.quote(stack: List<&2, Frame>, goal: Goal, done: Bool, ok: Bool) -> St:
  match ok:
    case True{}:
      S{MQuote{}, stack, goal, done, False{}}
    case False{}:
      err.st(goal)

# a word's first character. The buffer is that character, not the array behind it
def look.word(+ch: Char, stack: List<&2, Frame>, goal: Goal, done: Bool, ok: Bool) -> St:
  match ok:
    case True{}:
      S{MWord{ch <> [], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))},
        stack, goal, done, False{}}
    case False{}:
      err.st(goal)

# one character between tokens. The suffix stays with the stepper: a bracket
# closes on it, a comma does not keep it, and a word keeps only its own char
def look.plan(
  ch: Char,
  +stack: List<&2, Frame>,
  goal: Goal,
  +done: Bool,
  cls: Lex.Class
) -> St:
  match cls:
    case Lex.CSpace{}:
      idle.space(stack, goal, done)
    case Lex.CPunct{tok}:
      punct.on(tok, stack, goal, done)
    case Lex.CQuote{}:
      look.quote(stack, goal, done, expect.str(stack, done))
    case Lex.CBack{}:
      err.st(goal)
    case Lex.COther{}:
      look.word(ch, stack, goal, done, expect.val(stack, done))

# the end of the text, between tokens
def idle.eof(stack: List<&2, Frame>, goal: Goal, done: Bool, bad: Bool) -> (Stop & Cur):
  match goal done bad:
    case GNext{} True{} False{}:
      (SEv{EEnd{}}, Cur{"", stack, True{}, False{}})
    case g d b:
      bad.cur()

# a number, when the word is not null, true, or false
def word.kind.num(ok: Bool) -> Atom:
  match ok:
    case True{}:
      ANum{}
    case False{}:
      ABad{}

# null, true, false, or a number that kept a legal spelling
def word.kind.go(num: V.Num, is_null: Bool, is_true: Bool, is_false: Bool) -> Atom:
  match is_null is_true is_false:
    case True{} x y:
      ANull{}
    case False{} True{} y:
      ATrue{}
    case False{} False{} True{}:
      AFalse{}
    case False{} False{} False{}:
      word.kind.num(V.num.ok.done(num))

# what a bare word is
def word.kind(+cut: String, +nn: U32, num: V.Num) -> Atom:
  word.kind.go(num, V.span.eq(cut, nn, "null"), V.span.eq(cut, nn, "true"),
    V.span.eq(cut, nn, "false"))

# a word that ended at the end of the text
def word.eof.place(
  atom: Atom,
  cut: String,
  nn: U32,
  stack: List<&2, Frame>,
  goal: Goal
) -> St:
  match atom:
    case ABad{}:
      err.st(goal)
    case ANull{}:
      place.val(ENull{}, "", stack, goal)
    case ATrue{}:
      place.val(EBool{True{}}, "", stack, goal)
    case AFalse{}:
      place.val(EBool{False{}}, "", stack, goal)
    case ANum{}:
      place.val(ENum{cut, nn}, "", stack, goal)

# the delimiter of a skipped word, once the value is inside the container.
# The delimiter is consumed. The caller resumes on the suffix after it
def lay.plan(stack: List<&2, Frame>, goal: Goal, cls: Lex.Class) -> St:
  match cls:
    case Lex.CSpace{}:
      S{MIdle{}, stack, goal, False{}, False{}}
    case Lex.CPunct{tok}:
      punct.on(tok, stack, goal, False{})
    case other:
      err.st(goal)

# place the word, then take the delimiter, because the skip is still open
def see.more.on(goal: Goal, cls: Lex.Class, spot: Spot) -> St:
  match spot:
    case SpotBad{}:
      err.st(goal)
    case Spot{stack, root}:
      lay.plan(stack, goal, cls)

# place the word, then take the delimiter
def see.more(stack: List<&2, Frame>, goal: Goal, cls: Lex.Class) -> St:
  see.more.on(goal, cls, place.spot(stack))

# a code point that ends a bare word: the same bytes `classify` calls
# punctuation, a quote, a backslash, or whitespace. A form feed stays in the word
def word.special(+cp: U32) -> Bool:
  Bool.or(U32.is_eq(cp, 9),
    Bool.or(U32.is_eq(cp, 10),
      Bool.or(U32.is_eq(cp, 13),
        Bool.or(U32.is_eq(cp, 32),
          Bool.or(U32.is_eq(cp, 34),
            Bool.or(U32.is_eq(cp, 44),
              Bool.or(U32.is_eq(cp, 58),
                Bool.or(U32.is_eq(cp, 91),
                  Bool.or(U32.is_eq(cp, 92),
                    Bool.or(U32.is_eq(cp, 93),
                      Bool.or(U32.is_eq(cp, 123), U32.is_eq(cp, 125))))))))))))

# where a plain word run stopped. A stop keeps the delimiter, already consumed
type Wst is Data:
  WMore{buf: List<&2, Char>, nn: U32, num: V.Num}
  WStop{buf: List<&2, Char>, nn: U32, num: V.Num, ch: Char}
  WEof{buf: List<&2, Char>, nn: U32, num: V.Num}

# one more plain byte of a word. The buffer grows by that character
def word.step(ch: Char, +cp: U32, buf: List<&2, Char>, nn: U32, num: V.Num) -> Wst:
  WMore{ch <> buf, U32.add(nn, 1), V.num.ok.step(num, cp)}

# keep the byte when it is not a delimiter
def word.keep.go(
  ch: Char,
  cp: U32,
  buf: List<&2, Char>,
  nn: U32,
  num: V.Num,
  keep: Bool
) -> Wst:
  match keep:
    case True{}:
      word.step(ch, cp, buf, nn, num)
    case False{}:
      WStop{buf, nn, num, ch}

# a digit is never a delimiter, so a long number does not walk `classify`
def word.digit.go(
  ch: Char,
  +cp: U32,
  buf: List<&2, Char>,
  nn: U32,
  num: V.Num,
  dig: Bool
) -> Wst:
  match dig:
    case True{}:
      word.step(ch, cp, buf, nn, num)
    case False{}:
      word.keep.go(ch, cp, buf, nn, num, Bool.not(word.special(cp)))

# one byte of a word: another plain byte, or the delimiter that ends it
def word.decide(ch: Char, +cp: U32, buf: List<&2, Char>, nn: U32, num: V.Num) -> Wst:
  word.digit.go(ch, cp, buf, nn, num, V.num.ok.digit(cp))

# the suffix after a plain word. Tail call, so a long number is one loop
def word.run(txt: String, st: Wst) -> (String & Wst):
  match txt st:
    case rest WStop{buf, nn, num, ch}:
      (rest, WStop{buf, nn, num, ch})
    case rest WEof{buf, nn, num}:
      (rest, WEof{buf, nn, num})
    case SNil{} WMore{buf, nn, num}:
      ("", WEof{buf, nn, num})
    case SCon{+c, t} WMore{buf, nn, num}:
      word.run(t, word.decide(c, Char.to_u32(c), buf, nn, num))

# drop an unread suffix. Tail call, so a failed long value does not stack
def word.drop(txt: String) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{c, t}:
      word.drop(t)

# drop a word's characters. Tail call, so a long spelling does not stack
def word.forget(buf: List<&2, Char>) -> Bool:
  match buf:
    case Nil{}:
      True{}
    case Con{c, t}:
      word.forget(t)

# a failed word, once its buffer and the unread suffix are gone
def word.burst.err(goal: Goal, dropped: Bool) -> St:
  match dropped:
    case d:
      err.st(goal)

# a failed word drops the buffer after the unread suffix
def word.burst.dead(goal: Goal, dropped: Bool, buf: List<&2, Char>) -> St:
  match dropped:
    case d:
      word.burst.err(goal, word.forget(buf))

# a finished event already carries its suffix. Anything else continues on `rest`
def jump.keep(dropped: Bool, st: St) -> St:
  match dropped st:
    case d S{mode, stack, goal, done, bad}:
      S{mode, stack, goal, done, bad}

# a state that already stopped drops `rest`. Anything else resumes on it
def jump.unless.done(+rest: String, st: St) -> St:
  match st:
    case S{MDone{stop, saved}, stack, goal, done, bad}:
      jump.keep(word.drop(rest), S{MDone{stop, saved}, stack, goal, done, bad})
    case S{mode, stack, goal, done, bad}:
      S{MJump{rest, mode}, stack, goal, done, bad}

# a word that ended because the text did, once its spelling is in hand
def word.burst.eof.raw(
  +raw: String,
  +nn: U32,
  num: V.Num,
  stack: List<&2, Frame>,
  goal: Goal
) -> St:
  match goal:
    case GSkip{1n+left}:
      word.burst.err(goal, word.drop(raw))
    case GNext{}:
      word.eof.place(word.kind(raw, nn, num), raw, nn, stack, goal)
    case GSkip{0n}:
      word.eof.place(word.kind(raw, nn, num), raw, nn, stack, goal)

# the empty suffix of an eof is dropped, then the word is placed
def word.burst.eof.at(
  dropped: Bool,
  buf: List<&2, Char>,
  nn: U32,
  num: V.Num,
  stack: List<&2, Frame>,
  goal: Goal
) -> St:
  match dropped:
    case d:
      word.burst.eof.raw(Lex.text(buf), nn, num, stack, goal)

# the skip is still inside a container, so the delimiter is taken and the
# stepper continues. Only this path classifies that byte
def word.burst.skip(rest: String, +ch: Char, stack: List<&2, Frame>, goal: Goal) -> St:
  jump.unless.done(rest, see.more(stack, goal, Lex.classify(ch)))

# a value landed on the delimiter. The suffix is consed back once, not copied.
# The number keeps its own spelling, so it does not hold the rest of the array
def word.burst.goal(
  ev: Ev,
  ch: Char,
  rest: String,
  stack: List<&2, Frame>,
  goal: Goal
) -> St:
  match goal:
    case GNext{}:
      place.val(ev, SCon{ch, rest}, stack, goal)
    case GSkip{0n}:
      place.val(ev, SCon{ch, rest}, stack, goal)
    case GSkip{1n+left}:
      word.burst.skip(rest, ch, stack, goal)

# both the spelling and the unread suffix are dropped when the word is not one
def word.burst.junk(goal: Goal, dropped: Bool, rest: String) -> St:
  match dropped:
    case d:
      word.burst.err(goal, word.drop(rest))

# place the word. A number keeps its own spelling; the delimiter stays unread
def word.burst.atom(
  rest: String,
  ch: Char,
  raw: String,
  nn: U32,
  stack: List<&2, Frame>,
  goal: Goal,
  atom: Atom
) -> St:
  match atom:
    case ABad{}:
      word.burst.junk(goal, word.drop(raw), SCon{ch, rest})
    case ANull{}:
      word.burst.goal(ENull{}, ch, rest, stack, goal)
    case ATrue{}:
      word.burst.goal(EBool{True{}}, ch, rest, stack, goal)
    case AFalse{}:
      word.burst.goal(EBool{False{}}, ch, rest, stack, goal)
    case ANum{}:
      word.burst.goal(ENum{raw, nn}, ch, rest, stack, goal)

# the delimiter is classified once, and only when a skip must consume it.
# The plain bytes never were
def word.burst.raw(
  rest: String,
  ch: Char,
  +raw: String,
  +nn: U32,
  num: V.Num,
  stack: List<&2, Frame>,
  goal: Goal
) -> St:
  word.burst.atom(rest, ch, raw, nn, stack, goal, word.kind(raw, nn, num))

# a word ended on a delimiter. Its spelling is its own text
def word.burst.stop(
  rest: String,
  ch: Char,
  buf: List<&2, Char>,
  nn: U32,
  num: V.Num,
  stack: List<&2, Frame>,
  goal: Goal
) -> St:
  word.burst.raw(rest, ch, Lex.text(buf), nn, num, stack, goal)

# both the unread suffix and the buffer are dropped when the word cannot finish
def word.burst.fail(goal: Goal, dropped: Bool, buf: List<&2, Char>) -> St:
  match dropped:
    case d:
      word.burst.dead(goal, True{}, buf)

# `got` is the suffix after the run, and why it stopped
def word.burst.at(got: (String & Wst), stack: List<&2, Frame>, goal: Goal) -> St:
  (rest, wst) = got
  match wst:
    case WEof{buf, nn, num}:
      word.burst.eof.at(word.drop(rest), buf, nn, num, stack, goal)
    case WStop{buf, nn, num, ch}:
      word.burst.stop(rest, ch, buf, nn, num, stack, goal)
    case WMore{buf, nn, num}:
      word.burst.fail(goal, word.drop(rest), buf)

# plain digits and letters in one loop. The delimiter is consed back once
def word.burst(
  txt: String,
  buf: List<&2, Char>,
  nn: U32,
  num: V.Num,
  stack: List<&2, Frame>,
  goal: Goal,
  bad: Bool
) -> St:
  match bad:
    case True{}:
      word.burst.dead(goal, word.drop(txt), buf)
    case False{}:
      word.burst.at(word.run(txt, WMore{buf, nn, num}), stack, goal)

# a backslash in a span: copy the prefix, or drop it when skipping
def span.esc(
  +cut: String,
  +nn: U32,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  match goal:
    case GNext{}:
      S{MEsc{copy.rev(cut, nn, U32.is_zero(nn), [])}, stack, goal, done, False{}}
    case GSkip{depth}:
      S{MSkEsc{}, stack, goal, done, False{}}

# the next state after one character of a span. The unread tail stays with
# the stepper, so the usual character does not keep it
def span.advance(
  key: Skind,
  cut: String,
  nn: U32,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  match key:
    case KGo{}:
      S{MSpan{cut, U32.add(nn, 1)}, stack, goal, done, False{}}
    case KEnd{}:
      str.place.here(PSpan{cut, nn}, stack, goal)
    case KEsc{}:
      span.esc(cut, nn, stack, goal, done)
    case KBad{}:
      err.st(goal)

# the first character inside a string. A normal one opens the span on this
# suffix; the stepper then walks the tail, so the keep is once per string
def quote.go(
  key: Skind,
  ch: Char,
  tl: String,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  match key:
    case KGo{}:
      S{MSpan{SCon{ch, tl}, 1}, stack, goal, done, False{}}
    case KEnd{}:
      str.place.here(PSpan{"", 0}, stack, goal)
    case KEsc{}:
      span.esc("", 0, stack, goal, done)
    case KBad{}:
      err.st(goal)

# the first character inside a string
def quote.first(
  +ch: Char,
  tl: String,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  quote.go(span.kind.of(ch), ch, tl, stack, goal, done)

# the next state after one character of a string being skipped
def sk.advance(key: Skind, stack: List<&2, Frame>, goal: Goal, done: Bool) -> St:
  match key:
    case KGo{}:
      S{MSkStr{}, stack, goal, done, False{}}
    case KEnd{}:
      str.skip.here(stack, goal)
    case KEsc{}:
      S{MSkEsc{}, stack, goal, done, False{}}
    case KBad{}:
      err.st(goal)

# one character of a string that is being decoded
def copy.hit.go(
  +ch: Char,
  +tl: String,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  cls: Lex.Class,
  ctrl: Bool
) -> St:
  match cls ctrl:
    case Lex.CQuote{} c:
      str.place(POwn{Lex.text(buf)}, tl, stack, goal)
    case Lex.CBack{} False{}:
      S{MEsc{buf}, stack, goal, done, False{}}
    case k True{}:
      err.st(goal)
    case k False{}:
      S{MCopy{ch <> buf}, stack, goal, done, False{}}

# one character of a string that is being decoded
def copy.hit(
  +ch: Char,
  +tl: String,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  bad: Bool,
  cls: Lex.Class,
  ctrl: Bool
) -> St:
  match bad:
    case True{}:
      err.st(goal)
    case False{}:
      copy.hit.go(ch, tl, buf, stack, goal, done, cls, ctrl)

# the character after a backslash, once `u` has been noticed
def esc.put(
  _tl: String,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  got: Maybe<&2, Char>
) -> St:
  match got:
    case Some{ch}:
      S{MCopy{ch <> buf}, stack, goal, done, False{}}
    case None{}:
      err.st(goal)

# the character after a backslash
def esc.hit.go(
  +ch: Char,
  +tl: String,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  is_u: Bool
) -> St:
  match is_u:
    case True{}:
      S{MUni{3n, 0, buf}, stack, goal, done, False{}}
    case False{}:
      esc.put(tl, buf, stack, goal, done, Lex.unescape(ch))

# the character after a backslash
def esc.hit(
  +ch: Char,
  +tl: String,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  bad: Bool
) -> St:
  match bad:
    case True{}:
      err.st(goal)
    case False{}:
      esc.hit.go(ch, tl, buf, stack, goal, done, U32.is_eq(Char.to_u32(ch), 117))

# a `\u` code point that is not a surrogate
def uni.end.go(
  _tl: String,
  cp: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  key: Lex.Sur
) -> St:
  match key:
    case Lex.SOk{}:
      S{MCopy{Char.from_u32(cp) <> buf}, stack, goal, done, False{}}
    case Lex.SHi{}:
      S{MHi{cp, buf}, stack, goal, done, False{}}
    case Lex.SLo{}:
      err.st(goal)

# four hex digits are in
def uni.end(
  tl: String,
  +cp: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  uni.end.go(tl, cp, buf, stack, goal, done, Lex.unicode.sur(cp))

# one more hex digit, or the code point
def uni.put(
  tl: String,
  left: Nat,
  acc: U32,
  dig: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  match left:
    case 0n:
      uni.end(tl, (acc * 16 + dig : U32), buf, stack, goal, done)
    case 1n+p:
      S{MUni{p, (acc * 16 + dig : U32), buf}, stack, goal, done, False{}}

# one hex digit of a `\u` escape
def uni.hit.go(
  +ch: Char,
  +tl: String,
  left: Nat,
  acc: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  ok: Bool
) -> St:
  match ok:
    case True{}:
      uni.put(tl, left, acc, Lex.hex(ch), buf, stack, goal, done)
    case False{}:
      err.st(goal)

# one hex digit of a `\u` escape
def uni.hit(
  +ch: Char,
  +tl: String,
  left: Nat,
  acc: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  bad: Bool
) -> St:
  match bad:
    case True{}:
      err.st(goal)
    case False{}:
      uni.hit.go(ch, tl, left, acc, buf, stack, goal, done, Lex.hex.ok(Char.to_u32(ch)))

# the character after a high surrogate, on a live cursor
def hi.hit.go(
  _tl: String,
  hi: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  cls: Lex.Class
) -> St:
  match cls:
    case Lex.CBack{}:
      S{MHiEsc{hi, buf}, stack, goal, done, False{}}
    case other:
      err.st(goal)

# the character after a high surrogate: it has to be a backslash
def hi.hit(
  tl: String,
  hi: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  bad: Bool,
  cls: Lex.Class
) -> St:
  match bad:
    case True{}:
      err.st(goal)
    case False{}:
      hi.hit.go(tl, hi, buf, stack, goal, done, cls)

# the character after the backslash of a pair: it has to be `u`
def hiesc.hit.go(
  _tl: String,
  hi: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  is_u: Bool
) -> St:
  match is_u:
    case True{}:
      S{MLo{3n, 0, hi, buf}, stack, goal, done, False{}}
    case False{}:
      err.st(goal)

# the character after the backslash of a pair
def hiesc.hit(
  +ch: Char,
  tl: String,
  hi: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  bad: Bool
) -> St:
  match bad:
    case True{}:
      err.st(goal)
    case False{}:
      hiesc.hit.go(tl, hi, buf, stack, goal, done, U32.is_eq(Char.to_u32(ch), 117))

# the low surrogate is in, or it is not one
def lo.end.go(
  _tl: String,
  lo: U32,
  hi: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  key: Lex.Sur
) -> St:
  match key:
    case Lex.SLo{}:
      S{MCopy{Char.from_u32(Lex.unicode.pair(hi, lo)) <> buf}, stack, goal, done, False{}}
    case other:
      err.st(goal)

# four hex digits of the low surrogate are in
def lo.end(
  tl: String,
  +lo: U32,
  hi: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  lo.end.go(tl, lo, hi, buf, stack, goal, done, Lex.unicode.sur(lo))

# one more hex digit of the low surrogate, or the code point
def lo.put(
  tl: String,
  left: Nat,
  acc: U32,
  hi: U32,
  dig: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  match left:
    case 0n:
      lo.end(tl, (acc * 16 + dig : U32), hi, buf, stack, goal, done)
    case 1n+p:
      S{MLo{p, (acc * 16 + dig : U32), hi, buf}, stack, goal, done, False{}}

# one hex digit of the low surrogate
def lo.hit.go(
  +ch: Char,
  +tl: String,
  left: Nat,
  acc: U32,
  hi: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  ok: Bool
) -> St:
  match ok:
    case True{}:
      lo.put(tl, left, acc, hi, Lex.hex(ch), buf, stack, goal, done)
    case False{}:
      err.st(goal)

# one hex digit of the low surrogate
def lo.hit(
  +ch: Char,
  +tl: String,
  left: Nat,
  acc: U32,
  hi: U32,
  buf: List<&2, Char>,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  bad: Bool
) -> St:
  match bad:
    case True{}:
      err.st(goal)
    case False{}:
      lo.hit.go(ch, tl, left, acc, hi, buf, stack, goal, done, Lex.hex.ok(Char.to_u32(ch)))

# a decoded short escape puts the skip back in the string
def sk.esc.put(
  _tl: String,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  got: Maybe<&2, Char>
) -> St:
  match got:
    case Some{ch}:
      S{MSkStr{}, stack, goal, done, False{}}
    case None{}:
      err.st(goal)

# a short escape, or the start of `\u`, inside a skipped string
def sk.esc.go(
  +ch: Char,
  tl: String,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  is_u: Bool
) -> St:
  match is_u:
    case True{}:
      S{MSkUni{3n, 0}, stack, goal, done, False{}}
    case False{}:
      sk.esc.put(tl, stack, goal, done, Lex.unescape(ch))

# the character after a backslash in a skipped string
def sk.esc(
  +ch: Char,
  tl: String,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  bad: Bool
) -> St:
  match bad:
    case True{}:
      err.st(goal)
    case False{}:
      sk.esc.go(ch, tl, stack, goal, done, U32.is_eq(Char.to_u32(ch), 117))

# a skipped `\u` that is not a surrogate
def sk.uni.end.go(
  _tl: String,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  key: Lex.Sur,
  cp: U32
) -> St:
  match key:
    case Lex.SOk{}:
      S{MSkStr{}, stack, goal, done, False{}}
    case Lex.SHi{}:
      S{MSkHi{cp}, stack, goal, done, False{}}
    case Lex.SLo{}:
      err.st(goal)

# four hex digits of a skipped `\u` are in
def sk.uni.end(
  tl: String,
  +cp: U32,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  sk.uni.end.go(tl, stack, goal, done, Lex.unicode.sur(cp), cp)

# one more skipped hex digit, or the code point
def sk.uni.put(
  tl: String,
  left: Nat,
  acc: U32,
  dig: U32,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  match left:
    case 0n:
      sk.uni.end(tl, (acc * 16 + dig : U32), stack, goal, done)
    case 1n+p:
      S{MSkUni{p, (acc * 16 + dig : U32)}, stack, goal, done, False{}}

# one hex digit of a skipped `\u`
def sk.uni.go(
  +ch: Char,
  tl: String,
  left: Nat,
  acc: U32,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  ok: Bool
) -> St:
  match ok:
    case True{}:
      sk.uni.put(tl, left, acc, Lex.hex(ch), stack, goal, done)
    case False{}:
      err.st(goal)

# one hex digit of a skipped `\u`
def sk.uni(
  +ch: Char,
  tl: String,
  left: Nat,
  acc: U32,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  bad: Bool
) -> St:
  match bad:
    case True{}:
      err.st(goal)
    case False{}:
      sk.uni.go(ch, tl, left, acc, stack, goal, done, Lex.hex.ok(Char.to_u32(ch)))

# the character after a skipped high surrogate
def sk.hi(stack: List<&2, Frame>, goal: Goal, done: Bool, hi: U32, cls: Lex.Class) -> St:
  match cls:
    case Lex.CBack{}:
      S{MSkHiEsc{hi}, stack, goal, done, False{}}
    case other:
      err.st(goal)

# `u` after the backslash of a skipped pair
def sk.hiesc(stack: List<&2, Frame>, goal: Goal, done: Bool, hi: U32, is_u: Bool) -> St:
  match is_u:
    case True{}:
      S{MSkLo{3n, 0, hi}, stack, goal, done, False{}}
    case False{}:
      err.st(goal)

# the low half of a skipped pair is in, or it is not one
def sk.lo.end(_tl: String, stack: List<&2, Frame>, goal: Goal, done: Bool, key: Lex.Sur) -> St:
  match key:
    case Lex.SLo{}:
      S{MSkStr{}, stack, goal, done, False{}}
    case other:
      err.st(goal)

# one more hex digit of a skipped low surrogate, or the code point
def sk.lo.put(
  tl: String,
  left: Nat,
  acc: U32,
  hi: U32,
  dig: U32,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool
) -> St:
  match left:
    case 0n:
      sk.lo.end(tl, stack, goal, done, Lex.unicode.sur((acc * 16 + dig : U32)))
    case 1n+p:
      S{MSkLo{p, (acc * 16 + dig : U32), hi}, stack, goal, done, False{}}

# one hex digit of a skipped low surrogate
def sk.lo.go(
  +ch: Char,
  tl: String,
  left: Nat,
  acc: U32,
  hi: U32,
  stack: List<&2, Frame>,
  goal: Goal,
  done: Bool,
  ok: Bool
) -> St:
  match ok:
    case True{}:
      sk.lo.put(tl, left, acc, hi, Lex.hex(ch), stack, goal, done)
    case False{}:
      err.st(goal)

# jumps back from a plain word still available to this step. A byte step
# keeps the count and shrinks the suffix instead, so a long string does not
# burn it. Built at run time: a Nat literal of this size is unary
def next.fuel() -> Nat:
  U32.to_nat(4294967295)

# one character, between events. A plain word is one tail loop. A finished
# event returns; everything else tail-calls on the shorter suffix. A string
# character and a bracket are not handed to the step twice, so a long row or
# a long array moves the suffix instead of keeping it
def next.go(fuel: Nat, txt: String, st: St) -> (Stop & Cur):
  match fuel txt st:
    case n any S{MDone{stop, saved}, stack, goal, done, bad}:
      (stop, Cur{saved, stack, done, bad})
    case n txt S{MRest{stop}, stack, goal, done, bad}:
      (stop, Cur{txt, stack, done, bad})
    case 0n any S{mode, stack, goal, done, bad}:
      bad.cur()
    case 1n+left any S{MJump{rest, mode}, stack, goal, done, bad}:
      next.go(left, rest, S{mode, stack, goal, done, bad})
    case 1n+left SNil{} S{MQuote{}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{ch, tl} S{MQuote{}, stack, goal, done, True{}}:
      next.go(1n+left, tl, err.st(goal))
    case 1n+left SCon{ch, +tl} S{MQuote{}, stack, goal, done, False{}}:
      next.go(1n+left, tl, quote.first(ch, tl, stack, goal, done))
    case 1n+left SNil{} S{MIdle{}, stack, goal, done, bad}:
      idle.eof(stack, goal, done, bad)
    case 1n+left SCon{ch, tl} S{MIdle{}, stack, goal, done, True{}}:
      next.go(1n+left, tl, err.st(goal))
    case 1n+left SCon{ch, tl} S{MIdle{}, stack, goal, done, False{}}:
      next.go(1n+left, tl, look.plan(ch, stack, goal, done, Lex.classify(ch)))
    case 1n+left txt S{MWord{buf, nn, num}, stack, goal, done, bad}:
      next.go(left, "", word.burst(txt, buf, nn, num, stack, goal, bad))
    case 1n+left SNil{} S{MSpan{cut, nn}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{ch, tl} S{MSpan{cut, nn}, stack, goal, done, True{}}:
      next.go(1n+left, tl, err.st(goal))
    case 1n+left SCon{ch, tl} S{MSpan{cut, nn}, stack, goal, done, False{}}:
      next.go(1n+left, tl, span.advance(span.kind.of(ch), cut, nn, stack, goal, done))
    case 1n+left SNil{} S{MCopy{buf}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{+ch, +tl} S{MCopy{buf}, stack, goal, done, bad}:
      next.go(1n+left, tl, copy.hit(ch, tl, buf, stack, goal, done, bad, Lex.classify(ch),
        U32.is_lt(Char.to_u32(ch), 32)))
    case 1n+left SNil{} S{MEsc{buf}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{+ch, +tl} S{MEsc{buf}, stack, goal, done, bad}:
      next.go(1n+left, tl, esc.hit(ch, tl, buf, stack, goal, done, bad))
    case 1n+left SNil{} S{MUni{left2, acc, buf}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{+ch, +tl} S{MUni{left2, acc, buf}, stack, goal, done, bad}:
      next.go(1n+left, tl, uni.hit(ch, tl, left2, acc, buf, stack, goal, done, bad))
    case 1n+left SNil{} S{MHi{hi, buf}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{ch, tl} S{MHi{hi, buf}, stack, goal, done, bad}:
      next.go(1n+left, tl, hi.hit(tl, hi, buf, stack, goal, done, bad, Lex.classify(ch)))
    case 1n+left SNil{} S{MHiEsc{hi, buf}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{+ch, tl} S{MHiEsc{hi, buf}, stack, goal, done, bad}:
      next.go(1n+left, tl, hiesc.hit(ch, tl, hi, buf, stack, goal, done, bad))
    case 1n+left SNil{} S{MLo{left2, acc, hi, buf}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{+ch, +tl} S{MLo{left2, acc, hi, buf}, stack, goal, done, bad}:
      next.go(1n+left, tl, lo.hit(ch, tl, left2, acc, hi, buf, stack, goal, done, bad))
    case 1n+left SNil{} S{MSkStr{}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{ch, tl} S{MSkStr{}, stack, goal, done, True{}}:
      next.go(1n+left, tl, err.st(goal))
    case 1n+left SCon{ch, tl} S{MSkStr{}, stack, goal, done, False{}}:
      next.go(1n+left, tl, sk.advance(span.kind.of(ch), stack, goal, done))
    case 1n+left SNil{} S{MSkEsc{}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{+ch, tl} S{MSkEsc{}, stack, goal, done, bad}:
      next.go(1n+left, tl, sk.esc(ch, tl, stack, goal, done, bad))
    case 1n+left SNil{} S{MSkUni{left2, acc}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{+ch, tl} S{MSkUni{left2, acc}, stack, goal, done, bad}:
      next.go(1n+left, tl, sk.uni(ch, tl, left2, acc, stack, goal, done, bad))
    case 1n+left SNil{} S{MSkHi{hi}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{ch, tl} S{MSkHi{hi}, stack, goal, done, bad}:
      next.go(1n+left, tl, sk.hi(stack, goal, done, hi, Lex.classify(ch)))
    case 1n+left SNil{} S{MSkHiEsc{hi}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{+ch, tl} S{MSkHiEsc{hi}, stack, goal, done, bad}:
      next.go(1n+left, tl, sk.hiesc(stack, goal, done, hi, U32.is_eq(Char.to_u32(ch), 117)))
    case 1n+left SNil{} S{MSkLo{left2, acc, hi}, stack, goal, done, bad}:
      bad.cur()
    case 1n+left SCon{+ch, tl} S{MSkLo{left2, acc, hi}, stack, goal, done, bad}:
      next.go(1n+left, tl, sk.lo.go(ch, tl, left2, acc, hi, stack, goal, done,
        Lex.hex.ok(Char.to_u32(ch))))

# an event from a step. A skip that surfaces here is a broken reader
def next.use(got: (Stop & Cur)) -> (Ev & Cur):
  (stop, cur) = got
  match stop:
    case SEv{ev}:
      (ev, cur)
    case SSkip{}:
      (EErr{}, Cur{"", Nil{}, False{}, True{}})

# the next event, unless the cursor has already failed
def next.open(rest: String, stack: List<&2, Frame>, done: Bool, bad: Bool) -> (Ev & Cur):
  match bad:
    case True{}:
      (EErr{}, Cur{"", Nil{}, False{}, True{}})
    case False{}:
      next.use(next.go(next.fuel(), rest, S{MIdle{}, stack, GNext{}, done, False{}}))

# the cursor after a skip. An event other than a failure means the skip
# stopped on something that was not one value
def skip.use(got: (Stop & Cur)) -> Cur:
  (stop, cur) = got
  match stop:
    case SSkip{}:
      cur
    case SEv{EErr{}}:
      cur
    case SEv{ev}:
      Cur{"", Nil{}, False{}, True{}}

# drop one value, unless the cursor has already failed or the root is over
def skip.open(rest: String, stack: List<&2, Frame>, done: Bool, bad: Bool) -> Cur:
  match done bad:
    case d True{}:
      Cur{"", Nil{}, False{}, True{}}
    case True{} False{}:
      Cur{"", Nil{}, False{}, True{}}
    case False{} False{}:
      skip.use(next.go(next.fuel(), rest, S{MIdle{}, stack, GSkip{0n}, False{}, False{}}))

# a cursor at the start of `src`. It holds that string as its unread suffix,
# so dropping the caller's own variable does not drop the cursor, and
# dropping the cursor drops what it has not read yet
def cursor(src: String) -> Cur:
  Cur{src, Nil{}, False{}, False{}}

# the next event. A comma or a colon is consumed on the way to the event
# after it. After the root value, further calls are the end, or an error
# when another value follows
def next(cur: Cur) -> (Ev & Cur):
  Cur{rest, stack, done, bad} = cur
  next.open(rest, stack, done, bad)

# drop the next value: one scalar, or one array or object with everything
# inside it. The cursor is left where that value ended. A string with no
# escapes is not copied; a string being skipped is not decoded into a buffer
def skip(cur: Cur) -> Cur:
  Cur{rest, stack, done, bad} = cur
  skip.open(rest, stack, done, bad)

# the text of a string, a key, or a number. A span is copied here. None when
# the event is not one of those
def text(ev: Ev) -> Maybe<&2, String>:
  match ev:
    case EStr{body}:
      Some{body}
    case EKey{body}:
      Some{body}
    case EStrS{src, +nn}:
      Some{V.span.str(src, nn, U32.is_zero(nn))}
    case EKeyS{src, +nn}:
      Some{V.span.str(src, nn, U32.is_zero(nn))}
    case ENum{src, +nn}:
      Some{V.span.str(src, nn, U32.is_zero(nn))}
    case other:
      None{}
