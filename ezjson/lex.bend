# ezjson/lex: a JSON text as tokens. A string is decoded: \", \\, \/, \b, \f,
# \n, \r, \t, and \uXXXX. A \u escape of a surrogate pair is one code point.
import Base

# the tokens: brackets, `:`, `,`, a string (decoded), or a bare word
# (a number, true, false, null)
type Tok is Data:
  TOpenArr{}
  TCloseArr{}
  TOpenObj{}
  TCloseObj{}
  TColon{}
  TComma{}
  TStr{s: String}
  TWord{raw: String}
  TStrS{src: String, n: U32}
  TWordS{src: String, n: U32}
  TBad{}

# what a char is: punctuation (with its token), a quote, whitespace, or a
# word char
type Class is Data:
  CPunct{t: Tok}
  CQuote{}
  CBack{}
  CSpace{}
  COther{}

# what the machine is inside of: nothing, a bare word, a string, an escape,
# a \u escape, a high surrogate waiting for its pair, or a rejected text
type Mode is Data:
  Idle{}
  Word{}
  Str{}
  Esc{}
  Uni{left: Nat, acc: U32}
  Hi{hi: U32}
  HiEsc{hi: U32}
  Lo{left: Nat, acc: U32, hi: U32}
  Bad{}

# a \u code point: an ordinary scalar, a high surrogate, or a low surrogate
type Sur is Data:
  SOk{}
  SHi{}
  SLo{}

# the lexer's state: buf and toks are both reversed
type Lex is Data:
  Lex{mode: Mode, buf: List<&2, Char>, toks: List<&2, Tok>}

# a char's class, by code point. Written as comparisons rather than as
# `case '[':` arms: a character literal in a pattern is a U32 literal inside a
# constructor pattern, and bend's C backend pays about 90 MB for each one.
def classify.go(+cp: U32) -> Class:
  Bool.pick(Class, U32.is_eq(cp, 91), CPunct{TOpenArr{}},  # '['
  Bool.pick(Class, U32.is_eq(cp, 93), CPunct{TCloseArr{}},  # ']'
  Bool.pick(Class, U32.is_eq(cp, 123), CPunct{TOpenObj{}},  # '{'
  Bool.pick(Class, U32.is_eq(cp, 125), CPunct{TCloseObj{}},  # '}'
  Bool.pick(Class, U32.is_eq(cp, 58), CPunct{TColon{}},  # ':'
  Bool.pick(Class, U32.is_eq(cp, 44), CPunct{TComma{}},  # ','
  Bool.pick(Class, U32.is_eq(cp, 34), CQuote{},  # '"'
  Bool.pick(Class, U32.is_eq(cp, 92), CBack{},  # '\\'
  Bool.pick(Class, U32.is_eq(cp, 32), CSpace{},  # ' '
  Bool.pick(Class, U32.is_eq(cp, 10), CSpace{},  # '\n'
  Bool.pick(Class, U32.is_eq(cp, 13), CSpace{},  # '\r'
  Bool.pick(Class, U32.is_eq(cp, 9), CSpace{},  # '\t'
    COther{}))))))))))))

# a char's class
def classify(ch: Char) -> Class:
  classify.go(Char.to_u32(ch))

# the buffer is reversed, so consing each head onto the front yields the text
def text.go(buf: List<&2, Char>, acc: String) -> String:
  match buf:
    case Nil{}:
      acc
    case Con{h, t}:
      text.go(t, SCon{h, acc})

# the buffered chars (reversed) as a string
def text(buf: List<&2, Char>) -> String:
  text.go(buf, "")

def unescape.go(+cp: U32) -> Maybe<&2, Char>:
  Bool.pick(Maybe<&2, Char>, U32.is_eq(cp, 34), Some{'"'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(cp, 92), Some{'\\'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(cp, 47), Some{'/'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(cp, 98), Some{Char.from_u32(8)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(cp, 102), Some{Char.from_u32(12)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(cp, 110), Some{'\n'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(cp, 114), Some{'\r'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(cp, 116), Some{'\t'},
    None{}))))))))

# the char an escape stands for; none when the escape is not one JSON allows
def unescape(+ch: Char) -> Maybe<&2, Char>:
  unescape.go(Char.to_u32(ch))

def escape.put(mb: Maybe<&2, Char>, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match mb:
    case Some{ch}:
      Lex{Str{}, ch <> buf, toks}
    case None{}:
      Lex{Bad{}, [], toks}

# the char after a backslash in a string
def escape(ch: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match ch:
    case 'u':
      Lex{Uni{3n, 0}, buf, toks}
    case other:
      escape.put(unescape(other), buf, toks)

def hex.ok(+cp: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)),
    Bool.or(Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)),
      Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102))))

# a hex digit's value
def hex(ch: Char) -> U32:
  +x = Char.to_u32(ch)
  Bool.pick(U32, U32.is_le(x, 57), (x - 48 : U32),
    Bool.pick(U32, U32.is_ge(x, 97), (x - 87 : U32), (x - 55 : U32)))

def unicode.sur.lo(ge: Bool, le: Bool) -> Sur:
  match ge le:
    case True{} True{}:
      SLo{}
    case a b:
      SOk{}

def unicode.sur.hi(+cp: U32, ge: Bool, le: Bool) -> Sur:
  match ge le:
    case True{} True{}:
      SHi{}
    case a b:
      unicode.sur.lo(U32.is_ge(cp, 56320), U32.is_le(cp, 57343))

def unicode.sur(+cp: U32) -> Sur:
  unicode.sur.hi(cp, U32.is_ge(cp, 55296), U32.is_le(cp, 56319))

def unicode.pair(hi: U32, lo: U32) -> U32:
  U32.add(65536, U32.add(U32.mul(U32.sub(hi, 55296), 1024), U32.sub(lo, 56320)))

def unicode.end.go(cp: U32, buf: List<&2, Char>, toks: List<&2, Tok>, key: Sur) -> Lex:
  match key:
    case SOk{}:
      Lex{Str{}, Char.from_u32(cp) <> buf, toks}
    case SHi{}:
      Lex{Hi{cp}, buf, toks}
    case SLo{}:
      Lex{Bad{}, [], toks}

def unicode.end(+cp: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  unicode.end.go(cp, buf, toks, unicode.sur(cp))

def unicode.put(left: Nat, acc: U32, dig: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match left:
    case 0n:
      unicode.end((acc * 16 + dig : U32), buf, toks)
    case 1n+p:
      Lex{Uni{p, (acc * 16 + dig : U32)}, buf, toks}

def unicode.go(left: Nat, acc: U32, ch: Char, buf: List<&2, Char>, toks: List<&2, Tok>, ok: Bool) -> Lex:
  match ok:
    case True{}:
      unicode.put(left, acc, hex(ch), buf, toks)
    case False{}:
      Lex{Bad{}, [], toks}

# one hex digit of a \uXXXX escape; the code point once four are in
def unicode(left: Nat, acc: U32, +ch: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  unicode.go(left, acc, ch, buf, toks, hex.ok(Char.to_u32(ch)))

def unicode.low.end.go(lo: U32, hi: U32, buf: List<&2, Char>, toks: List<&2, Tok>, key: Sur) -> Lex:
  match key:
    case SLo{}:
      Lex{Str{}, Char.from_u32(unicode.pair(hi, lo)) <> buf, toks}
    case other:
      Lex{Bad{}, [], toks}

def unicode.low.end(+lo: U32, hi: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  unicode.low.end.go(lo, hi, buf, toks, unicode.sur(lo))

def unicode.low.put(left: Nat, acc: U32, hi: U32, dig: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match left:
    case 0n:
      unicode.low.end((acc * 16 + dig : U32), hi, buf, toks)
    case 1n+p:
      Lex{Lo{p, (acc * 16 + dig : U32), hi}, buf, toks}

def unicode.low.go(
  left: Nat,
  acc: U32,
  hi: U32,
  ch: Char,
  buf: List<&2, Char>,
  toks: List<&2, Tok>,
  ok: Bool
) -> Lex:
  match ok:
    case True{}:
      unicode.low.put(left, acc, hi, hex(ch), buf, toks)
    case False{}:
      Lex{Bad{}, [], toks}

def unicode.low(left: Nat, acc: U32, hi: U32, +ch: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  unicode.low.go(left, acc, hi, ch, buf, toks, hex.ok(Char.to_u32(ch)))

def step.str.go(ch: Char, buf: List<&2, Char>, toks: List<&2, Tok>, ctrl: Bool) -> Lex:
  match ctrl:
    case True{}:
      Lex{Bad{}, [], toks}
    case False{}:
      Lex{Str{}, ch <> buf, toks}

def step.str(+ch: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  step.str.go(ch, buf, toks, U32.is_lt(Char.to_u32(ch), 32))

def step.hi.go(hi: U32, buf: List<&2, Char>, toks: List<&2, Tok>, slash: Bool) -> Lex:
  match slash:
    case True{}:
      Lex{HiEsc{hi}, buf, toks}
    case False{}:
      Lex{Bad{}, [], toks}

def step.hi(hi: U32, ch: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  step.hi.go(hi, buf, toks, U32.is_eq(Char.to_u32(ch), 92))

def step.hiesc(hi: U32, ch: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match ch:
    case 'u':
      Lex{Lo{3n, 0, hi}, buf, toks}
    case other:
      Lex{Bad{}, [], toks}

# one char, by the mode and the char's class
def step(mode: Mode, cls: Class, ch: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match mode cls:
    case Idle{} CPunct{t}:
      Lex{Idle{}, [], t <> toks}
    case Idle{} CQuote{}:
      Lex{Str{}, [], toks}
    case Idle{} CSpace{}:
      Lex{Idle{}, [], toks}
    case Idle{} CBack{}:
      Lex{Bad{}, [], toks}
    case Idle{} COther{}:
      Lex{Word{}, [ch], toks}
    case Word{} CPunct{t}:
      Lex{Idle{}, [], t <> TWord{text(buf)} <> toks}
    case Word{} CQuote{}:
      Lex{Str{}, [], TWord{text(buf)} <> toks}
    case Word{} CSpace{}:
      Lex{Idle{}, [], TWord{text(buf)} <> toks}
    case Word{} CBack{}:
      Lex{Bad{}, [], toks}
    case Word{} COther{}:
      Lex{Word{}, ch <> buf, toks}
    case Str{} CQuote{}:
      Lex{Idle{}, [], TStr{text(buf)} <> toks}
    case Str{} CBack{}:
      Lex{Esc{}, buf, toks}
    case Str{} other:
      step.str(ch, buf, toks)
    case Esc{} other:
      escape(ch, buf, toks)
    case Uni{left, acc} other:
      unicode(left, acc, ch, buf, toks)
    case Hi{hi} other:
      step.hi(hi, ch, buf, toks)
    case HiEsc{hi} other:
      step.hiesc(hi, ch, buf, toks)
    case Lo{left, acc, hi} other:
      unicode.low(left, acc, hi, ch, buf, toks)
    case Bad{} other:
      Lex{Bad{}, [], toks}

# one char into the machine
def feed(+ch: Char, st: Lex) -> Lex:
  Lex{mode, buf, toks} = st
  step(mode, classify(ch), ch, buf, toks)

# every char, in order
def run(cs: List<&2, Char>, st: Lex) -> Lex:
  match cs:
    case Nil{}:
      st
    case Con{c, t}:
      run(t, feed(c, st))

# the tokens, in order; text that ends inside a string or a word ends in TBad
# when the string was not closed
def finish(st: Lex) -> List<&2, Tok>:
  Lex{mode, buf, toks} = st
  match mode:
    case Idle{}:
      List.reverse(&2, Tok, toks)
    case Word{}:
      List.reverse(&2, Tok, TWord{text(buf)} <> toks)
    case other:
      List.reverse(&2, Tok, TBad{} <> toks)

# the first n chars of src, reversed, for the escape fallback's buffer
def tokens.rev(src: String, +nn: U32, zero: Bool, acc: List<&2, Char>) -> List<&2, Char>:
  match src zero:
    case s True{}:
      acc
    case SNil{} False{}:
      acc
    case SCon{h, t} False{}:
      tokens.rev(t, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), h <> acc)

def tokens.push(cut: String, nn: U32, word: Bool, toks: List<&2, Tok>) -> List<&2, Tok>:
  match word:
    case True{}:
      TWordS{cut, nn} <> toks
    case False{}:
      TStrS{cut, nn} <> toks

# `cut` is the suffix where the open word or string began, so closing it does
# not walk the text again. Old means a backslash handed the tail to the copier
type Scan is Data:
  Go{cut: String, n: U32, mode: U32, toks: List<&2, Tok>}
  Old{st: Lex}

def tokens.hit(
  +ch: Char,
  tail: String,
  cut: String,
  +nn: U32,
  mode: U32,
  toks: List<&2, Tok>,
  cls: Class,
  ctrl: Bool
) -> Scan:
  match mode cls ctrl:
    case 0 CSpace{} b:
      Go{cut, nn, 0, toks}
    case 0 CPunct{p} b:
      Go{cut, nn, 0, p <> toks}
    case 0 CQuote{} b:
      Go{tail, 0, 2, toks}
    case 0 CBack{} b:
      Go{cut, nn, 3, toks}
    case 0 COther{} b:
      Go{SCon{ch, tail}, 1, 1, toks}
    case 1 COther{} b:
      Go{cut, U32.add(nn, 1), 1, toks}
    case 1 CPunct{p} b:
      Go{"", 0, 0, p <> tokens.push(cut, nn, True{}, toks)}
    case 1 CQuote{} b:
      Go{tail, 0, 2, tokens.push(cut, nn, True{}, toks)}
    case 1 CBack{} b:
      Go{cut, nn, 3, toks}
    case 1 k b:
      Go{"", 0, 0, tokens.push(cut, nn, True{}, toks)}
    case 2 k True{}:
      Go{cut, nn, 3, toks}
    case 2 CQuote{} False{}:
      Go{"", 0, 0, tokens.push(cut, nn, False{}, toks)}
    case 2 CBack{} False{}:
      Old{feed('\\', Lex{Str{}, tokens.rev(cut, nn, U32.is_zero(nn), []), toks})}
    case 2 k False{}:
      Go{cut, U32.add(nn, 1), 2, toks}
    case m k b:
      Go{cut, nn, 3, toks}

def tokens.done(cut: String, nn: U32, mode: U32, toks: List<&2, Tok>) -> List<&2, Tok>:
  match mode:
    case 0:
      List.reverse(&2, Tok, toks)
    case 1:
      List.reverse(&2, Tok, tokens.push(cut, nn, True{}, toks))
    case m:
      List.reverse(&2, Tok, TBad{} <> toks)

def tokens.end(st: Scan) -> List<&2, Tok>:
  match st:
    case Old{lex}:
      finish(lex)
    case Go{cut, n, mode, toks}:
      tokens.done(cut, n, mode, toks)

def tokens.feed(+ch: Char, tail: String, st: Scan) -> Scan:
  match st:
    case Old{lex}:
      Old{feed(ch, lex)}
    case Go{cut, n, mode, toks}:
      tokens.hit(ch, tail, cut, n, mode, toks, classify(ch), U32.is_lt(Char.to_u32(ch), 32))

# match only the text, so a literal unrolls. The tail is where the next span starts
def tokens.go(txt: String, st: Scan) -> List<&2, Tok>:
  match txt:
    case SNil{}:
      tokens.end(st)
    case SCon{+c, +t}:
      tokens.go(t, tokens.feed(c, t, st))

# a text as tokens. Clean words and strings are spans of the text
def tokens(txt: String) -> List<&2, Tok>:
  tokens.go(txt, Go{"", 0, 0, []})
