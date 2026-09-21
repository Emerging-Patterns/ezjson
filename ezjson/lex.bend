# ezjson/lex: text to tokens, one char per step: a tail-recursive state machine
# over the char list, so it needs no fuel and runs as a loop.
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

# what the machine is inside of: nothing, a bare word, a string, an escape
# in a string, or a \\u escape with hex digits still owed
type Mode is Data:
  Idle{}
  Word{}
  Str{}
  Esc{}
  Uni{left: Nat, acc: U32}

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

# the char an escape stands for; an unknown escape stands for itself
def unescape(+c: Char) -> Char:
  +x = Char.to_u32(c)
  Bool.pick(Char, U32.is_eq(x, 110), '\n',  # 'n'
  Bool.pick(Char, U32.is_eq(x, 114), '\r',  # 'r'
  Bool.pick(Char, U32.is_eq(x, 116), '\t',  # 't'
  Bool.pick(Char, U32.is_eq(x, 98), Char.from_u32(8),  # 'b'
  Bool.pick(Char, U32.is_eq(x, 102), Char.from_u32(12), c)))))  # 'f'

# a hex digit's value
def hex(c: Char) -> U32:
  +x = Char.to_u32(c)
  Bool.pick(U32, U32.is_le(x, 57), (x - 48 : U32),
    Bool.pick(U32, U32.is_ge(x, 97), (x - 87 : U32), (x - 55 : U32)))

# the char after a backslash in a string
def escape(c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match c:
    case 'u':
      Lex{Uni{3n, 0}, buf, toks}
    case other:
      Lex{Str{}, unescape(other) <> buf, toks}

# one hex digit of a \\uXXXX escape; the code point once four are in
def unicode(left: Nat, acc: U32, c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match left:
    case 0n:
      +d = hex(c)
      Lex{Str{}, Char.from_u32((acc * 16 + d : U32)) <> buf, toks}
    case 1n+p:
      +d = hex(c)
      Lex{Uni{p, (acc * 16 + d : U32)}, buf, toks}

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
      Lex{Idle{}, [], TBad{} <> toks}
    case Idle{} COther{}:
      Lex{Word{}, [c], toks}
    case Word{} CPunct{t}:
      Lex{Idle{}, [], t <> TWord{text(buf)} <> toks}
    case Word{} CQuote{}:
      Lex{Str{}, [], TWord{text(buf)} <> toks}
    case Word{} CSpace{}:
      Lex{Idle{}, [], TWord{text(buf)} <> toks}
    case Word{} CBack{}:
      Lex{Idle{}, [], TBad{} <> toks}
    case Word{} COther{}:
      Lex{Word{}, c <> buf, toks}
    case Str{} CQuote{}:
      Lex{Idle{}, [], TStr{text(buf)} <> toks}
    case Str{} CBack{}:
      Lex{Esc{}, buf, toks}
    case Str{} other:
      Lex{Str{}, c <> buf, toks}
    case Esc{} other:
      escape(c, buf, toks)
    case Uni{left, acc} other:
      unicode(left, acc, c, buf, toks)

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

# the tokens, in order; text that ends inside a string ends in TBad
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
