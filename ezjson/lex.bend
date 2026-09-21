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
def classify.go(+x: U32) -> Class:
  Bool.pick(Class, U32.is_eq(x, 91), CPunct{TOpenArr{}},  # '['
  Bool.pick(Class, U32.is_eq(x, 93), CPunct{TCloseArr{}},  # ']'
  Bool.pick(Class, U32.is_eq(x, 123), CPunct{TOpenObj{}},  # '{'
  Bool.pick(Class, U32.is_eq(x, 125), CPunct{TCloseObj{}},  # '}'
  Bool.pick(Class, U32.is_eq(x, 58), CPunct{TColon{}},  # ':'
  Bool.pick(Class, U32.is_eq(x, 44), CPunct{TComma{}},  # ','
  Bool.pick(Class, U32.is_eq(x, 34), CQuote{},  # '"'
  Bool.pick(Class, U32.is_eq(x, 92), CBack{},  # '\\'
  Bool.pick(Class, U32.is_eq(x, 32), CSpace{},  # ' '
  Bool.pick(Class, U32.is_eq(x, 10), CSpace{},  # '\n'
  Bool.pick(Class, U32.is_eq(x, 13), CSpace{},  # '\r'
  Bool.pick(Class, U32.is_eq(x, 9), CSpace{},  # '\t'
    COther{}))))))))))))

# a char's class
def classify(c: Char) -> Class:
  classify.go(Char.to_u32(c))

# the buffered chars (reversed) as a string
def text(buf: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, buf))

def unescape.go(+x: U32) -> Maybe<&2, Char>:
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 34), Some{'"'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 92), Some{'\\'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 47), Some{'/'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 98), Some{Char.from_u32(8)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 102), Some{Char.from_u32(12)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 110), Some{'\n'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 114), Some{'\r'},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 116), Some{'\t'},
    None{}))))))))

# the char an escape stands for; none when the escape is not one JSON allows
def unescape(+c: Char) -> Maybe<&2, Char>:
  unescape.go(Char.to_u32(c))

def escape.put(m: Maybe<&2, Char>, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match m:
    case Some{ch}:
      Lex{Str{}, ch <> buf, toks}
    case None{}:
      Lex{Bad{}, [], toks}

# the char after a backslash in a string
def escape(c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match c:
    case 'u':
      Lex{Uni{3n, 0}, buf, toks}
    case other:
      escape.put(unescape(other), buf, toks)

def hex.ok(+x: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)),
    Bool.or(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 70)),
      Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102))))

# a hex digit's value
def hex(c: Char) -> U32:
  +x = Char.to_u32(c)
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

def unicode.end.go(cp: U32, buf: List<&2, Char>, toks: List<&2, Tok>, k: Sur) -> Lex:
  match k:
    case SOk{}:
      Lex{Str{}, Char.from_u32(cp) <> buf, toks}
    case SHi{}:
      Lex{Hi{cp}, buf, toks}
    case SLo{}:
      Lex{Bad{}, [], toks}

def unicode.end(+cp: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  unicode.end.go(cp, buf, toks, unicode.sur(cp))

def unicode.put(left: Nat, acc: U32, d: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match left:
    case 0n:
      unicode.end((acc * 16 + d : U32), buf, toks)
    case 1n+p:
      Lex{Uni{p, (acc * 16 + d : U32)}, buf, toks}

def unicode.go(left: Nat, acc: U32, c: Char, buf: List<&2, Char>, toks: List<&2, Tok>, ok: Bool) -> Lex:
  match ok:
    case True{}:
      unicode.put(left, acc, hex(c), buf, toks)
    case False{}:
      Lex{Bad{}, [], toks}

# one hex digit of a \uXXXX escape; the code point once four are in
def unicode(left: Nat, acc: U32, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  unicode.go(left, acc, c, buf, toks, hex.ok(Char.to_u32(c)))

def unicode.low.end.go(lo: U32, hi: U32, buf: List<&2, Char>, toks: List<&2, Tok>, k: Sur) -> Lex:
  match k:
    case SLo{}:
      Lex{Str{}, Char.from_u32(unicode.pair(hi, lo)) <> buf, toks}
    case other:
      Lex{Bad{}, [], toks}

def unicode.low.end(+lo: U32, hi: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  unicode.low.end.go(lo, hi, buf, toks, unicode.sur(lo))

def unicode.low.put(left: Nat, acc: U32, hi: U32, d: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match left:
    case 0n:
      unicode.low.end((acc * 16 + d : U32), hi, buf, toks)
    case 1n+p:
      Lex{Lo{p, (acc * 16 + d : U32), hi}, buf, toks}

def unicode.low.go(left: Nat, acc: U32, hi: U32, c: Char, buf: List<&2, Char>, toks: List<&2, Tok>,
    ok: Bool) -> Lex:
  match ok:
    case True{}:
      unicode.low.put(left, acc, hi, hex(c), buf, toks)
    case False{}:
      Lex{Bad{}, [], toks}

def unicode.low(left: Nat, acc: U32, hi: U32, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  unicode.low.go(left, acc, hi, c, buf, toks, hex.ok(Char.to_u32(c)))

def step.str.go(c: Char, buf: List<&2, Char>, toks: List<&2, Tok>, ctrl: Bool) -> Lex:
  match ctrl:
    case True{}:
      Lex{Bad{}, [], toks}
    case False{}:
      Lex{Str{}, c <> buf, toks}

def step.str(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  step.str.go(c, buf, toks, U32.is_lt(Char.to_u32(c), 32))

def step.hi.go(hi: U32, buf: List<&2, Char>, toks: List<&2, Tok>, slash: Bool) -> Lex:
  match slash:
    case True{}:
      Lex{HiEsc{hi}, buf, toks}
    case False{}:
      Lex{Bad{}, [], toks}

def step.hi(hi: U32, c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  step.hi.go(hi, buf, toks, U32.is_eq(Char.to_u32(c), 92))

def step.hiesc(hi: U32, c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match c:
    case 'u':
      Lex{Lo{3n, 0, hi}, buf, toks}
    case other:
      Lex{Bad{}, [], toks}

# one char, by the mode and the char's class
def step(mode: Mode, cls: Class, c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
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
      Lex{Word{}, [c], toks}
    case Word{} CPunct{t}:
      Lex{Idle{}, [], t <> TWord{text(buf)} <> toks}
    case Word{} CQuote{}:
      Lex{Str{}, [], TWord{text(buf)} <> toks}
    case Word{} CSpace{}:
      Lex{Idle{}, [], TWord{text(buf)} <> toks}
    case Word{} CBack{}:
      Lex{Bad{}, [], toks}
    case Word{} COther{}:
      Lex{Word{}, c <> buf, toks}
    case Str{} CQuote{}:
      Lex{Idle{}, [], TStr{text(buf)} <> toks}
    case Str{} CBack{}:
      Lex{Esc{}, buf, toks}
    case Str{} other:
      step.str(c, buf, toks)
    case Esc{} other:
      escape(c, buf, toks)
    case Uni{left, acc} other:
      unicode(left, acc, c, buf, toks)
    case Hi{hi} other:
      step.hi(hi, c, buf, toks)
    case HiEsc{hi} other:
      step.hiesc(hi, c, buf, toks)
    case Lo{left, acc, hi} other:
      unicode.low(left, acc, hi, c, buf, toks)
    case Bad{} other:
      Lex{Bad{}, [], toks}

# one char into the machine
def feed(+c: Char, st: Lex) -> Lex:
  Lex{mode, buf, toks} = st
  step(mode, classify(c), c, buf, toks)

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

# a text as tokens
def tokens(s: String) -> List<&2, Tok>:
  finish(run(String.to_list(s), Lex{Idle{}, [], []}))
